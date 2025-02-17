use interner::intern;
use module::*;
use renamer::Name;
use std::collections::HashMap;

pub struct PrecedenceVisitor {
    precedence: HashMap<Name, (isize, Assoc)>,
}

impl MutVisitor<Name> for PrecedenceVisitor {
    fn visit_expr(&mut self, expr: &mut TypedExpr<Name>) {
        walk_expr_mut(self, expr);
        match expr.expr {
            Expr::OpApply(..) => {
                let mut temp = TypedExpr::new(Expr::Identifier(Name {
                    uid: usize::max_value(),
                    name: intern(""),
                }));
                ::std::mem::swap(&mut temp, expr);
                temp = self.rewrite(box temp);
                ::std::mem::swap(&mut temp, expr);
            }
            _ => (),
        }
    }
    fn visit_module(&mut self, module: &mut Module<Name>) {
        for fixity in module.fixity_declarations.iter() {
            for op in fixity.operators.iter() {
                self.precedence
                    .insert(op.clone(), (fixity.precedence, fixity.assoc));
            }
        }
        walk_module_mut(self, module);
    }
}
impl PrecedenceVisitor {
    pub fn new() -> PrecedenceVisitor {
        let mut map = HashMap::new();
        map.insert(
            Name {
                uid: 0,
                name: intern(":"),
            },
            (5, Assoc::Right),
        );
        PrecedenceVisitor { precedence: map }
    }

    fn get_precedence(&self, name: &Name) -> (isize, Assoc) {
        self.precedence
            .get(name)
            .map(|x| *x)
            .unwrap_or_else(|| (9, Assoc::Left))
    }

    ///Takes a operator expression the is in the form (1 + (2 * (3 - 4))) and rewrites it using the
    ///operators real precedences
    fn rewrite(&self, mut input: Box<TypedExpr<Name>>) -> TypedExpr<Name> {
        //Takes the two expressions at the top of the stack and applies the operator at the top to them
        fn reduce(expr_stack: &mut Vec<Box<TypedExpr<Name>>>, op_stack: &mut Vec<Name>) {
            assert!(expr_stack.len() >= 2);
            let op = op_stack.pop().unwrap();
            let rhs = expr_stack.pop().unwrap();
            let lhs = expr_stack.pop().unwrap();
            let loc = lhs.location;
            expr_stack.push(box TypedExpr::with_location(
                Expr::OpApply(lhs, op, rhs),
                loc,
            ));
        }
        let mut expr_stack = Vec::new();
        let mut op_stack = Vec::new();
        loop {
            //FIXME should destructure instead of clone
            let TypedExpr {
                typ,
                location,
                expr,
            } = (*input).clone();
            match expr {
                Expr::OpApply(l, op, r) => {
                    expr_stack.push(l);
                    input = r;
                    loop {
                        match op_stack.last().map(|x| *x) {
                            Some(previous_op) => {
                                let (op_prec, op_assoc) = self.get_precedence(&op);
                                let (prev_prec, prev_assoc) = self.get_precedence(&previous_op);
                                if op_prec > prev_prec {
                                    op_stack.push(op);
                                    break;
                                } else if op_prec == prev_prec {
                                    match (op_assoc, prev_assoc) {
                                        (Assoc::Left, Assoc::Left) => {
                                            reduce(&mut expr_stack, &mut op_stack);
                                        }
                                        (Assoc::Right, Assoc::Right) => {
                                            tracing::debug!("Shift op {:?}", op);
                                            op_stack.push(op);
                                            break;
                                        }
                                        _ => panic!("Syntax error: mismatched associativity"),
                                    }
                                } else {
                                    reduce(&mut expr_stack, &mut op_stack);
                                }
                            }
                            None => {
                                op_stack.push(op);
                                break;
                            }
                        }
                    }
                }
                rhs => {
                    let mut result = TypedExpr {
                        typ: typ,
                        location: location,
                        expr: rhs,
                    };
                    while op_stack.len() != 0 {
                        assert!(expr_stack.len() >= 1);
                        let lhs = expr_stack.pop().unwrap();
                        let op = op_stack.pop().unwrap();
                        result =
                            TypedExpr::with_location(Expr::OpApply(lhs, op, box result), location);
                    }
                    return result;
                }
            }
        }
    }
}

