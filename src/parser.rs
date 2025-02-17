use interner::*;
use lexer::TokenEnum::*;
use lexer::*;
use module::Expr::*;
use module::LiteralData::*;
use module::*;
use std::collections::{HashMap, HashSet};
use std::error;
use std::fmt;
use std::fs::File;
use std::io;
use std::io::Read;
use std::mem::swap;
use std::str::FromStr;

///The Parser is a recursive descent parser which has a method for each production
///in the AST. By calling such a production method it is expected that the parser is
///in a position where it starts at the first token of that production and can parse the production
///completely otherwise it will call fail with an appropriate error message.
///If the methods returns an Option it will instead return None.
///In any case it is expected that a production method will place the parser in a position where_bindings
///it can continue parsing without having to move the lexer's position.
pub struct Parser<Iter: Iterator<Item = char>> {
    lexer: Lexer<Iter>,
}

#[derive(Debug, Eq, PartialEq)]
enum Error {
    UnexpectedToken(&'static [TokenEnum], TokenEnum),
    Message(::std::string::String),
}

#[derive(Debug, PartialEq)]
pub struct ParseError(Located<Error>);

pub type ParseResult<T> = Result<T, ParseError>;

impl From<io::Error> for ParseError {
    fn from(io_error: io::Error) -> ParseError {
        ParseError(Located {
            location: Location::eof(),
            node: Error::Message(io_error.to_string()),
        })
    }
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.0.node {
            Error::UnexpectedToken(unexpected, expected) => {
                write!(
                    f,
                    "Expected token {:?}, but found {:?}",
                    unexpected, expected
                )
            }
            Error::Message(ref message) => write!(f, "{}", message),
        }
    }
}

impl error::Error for ParseError {
    fn description(&self) -> &str {
        "parse error"
    }
}

enum BindOrTypeDecl {
    Binding(Binding),
    TypeDecl(TypeDeclaration),
}

macro_rules! expect {
    ($e: expr, $p: ident (..)) => {{
        match $e.next($p).token {
            $p(..) => $e.lexer.current(),
            actual => unexpected!($e, actual, $p),
        }
    }};
    ($e: expr, $p: ident) => {{
        match $e.next($p).token {
            $p => $e.lexer.current(),
            actual => unexpected!($e, actual, $p),
        }
    }};
}

#[allow(unused_macros)] // TODO: figure out what does these unused macros do
macro_rules! expect1 {
    ($e: expr, $p: ident ($x: ident)) => {{
        match $e.next().token {
            $p($x) => $x,
            actual => unexpected!($e, actual, $p),
        }
    }};
}

#[allow(unused_macros)]
macro_rules! matches {
    ($e: expr, $p: pat) => {
        match $e {
            $p => true,
            _ => false,
        }
    };
}

macro_rules! unexpected (
    ($parser: expr, [$($expected: expr),+]) => { unexpected!($parser, $parser.lexer.current().token, $($expected),+) };
    ($parser: expr, $token: expr, $($expected: expr),+) => { {
        $parser.lexer.backtrack();
        static EXPECTED: &'static [TokenEnum] = &[$($expected),+];
        return Err($parser.unexpected_token(EXPECTED, $token))
    } }
);

impl<Iter: Iterator<Item = char>> Parser<Iter> {
    pub fn new(iterator: Iter) -> Parser<Iter> {
        Parser {
            lexer: Lexer::new(iterator),
        }
    }

    fn next<'a>(&'a mut self, expected: TokenEnum) -> &'a Token {
        if expected == RBRACE {
            self.lexer.next_end()
        } else {
            self.lexer.next()
        }
    }

    fn error<T>(&self, message: ::std::string::String) -> ParseResult<T> {
        Err(ParseError(Located {
            location: self.lexer.current().location,
            node: Error::Message(message),
        }))
    }
    fn unexpected_token(&self, expected: &'static [TokenEnum], actual: TokenEnum) -> ParseError {
        ParseError(Located {
            location: self.lexer.current().location,
            node: Error::UnexpectedToken(expected, actual),
        })
    }

    pub fn module(&mut self) -> ParseResult<Module> {
        let modulename = match self.lexer.module_next().token {
            MODULE => {
                let modulename = expect!(self, NAME).value.clone();
                expect!(self, WHERE);
                expect!(self, LBRACE);
                modulename
            }
            LBRACE => {
                //No module declaration was found so default to Main
                intern("Main")
            }
            _ => unexpected!(self, [LBRACE]),
        };

        let mut imports = Vec::new();
        loop {
            if self.lexer.peek().token == IMPORT {
                imports.push(self.import()?);
                if self.lexer.peek().token == SEMICOLON {
                    self.lexer.next();
                } else {
                    break;
                }
            } else {
                break;
            }
        }

        let mut classes = Vec::new();
        let mut bindings = Vec::new();
        let mut instances = Vec::new();
        let mut type_declarations = Vec::new();
        let mut data_definitions = Vec::new();
        let mut newtypes = Vec::new();
        let mut fixity_declarations = Vec::new();
        loop {
            //Do a lookahead to see what the next top level binding is
            let token = self.lexer.peek().token;
            if token == NAME || token == LPARENS {
                match self.binding_or_type_declaration()? {
                    BindOrTypeDecl::Binding(bind) => bindings.push(bind),
                    BindOrTypeDecl::TypeDecl(decl) => type_declarations.push(decl),
                }
            } else if token == CLASS {
                classes.push(self.class()?);
            } else if token == INSTANCE {
                instances.push(self.instance()?);
            } else if token == DATA {
                data_definitions.push(self.data_definition()?);
            } else if token == NEWTYPE {
                newtypes.push(self.newtype()?);
            } else if token == INFIXL || token == INFIXR || token == INFIX {
                fixity_declarations.push(self.fixity_declaration()?);
            } else {
                self.lexer.next();
                break;
            }
            let semicolon = self.lexer.next();
            tracing::debug!("More bindings? {:?}", semicolon.token);
            if semicolon.token != SEMICOLON {
                break;
            }
        }

        self.lexer.backtrack();
        expect!(self, RBRACE);
        expect!(self, EOF);

        Ok(Module {
            name: modulename,
            imports: imports,
            bindings: bindings,
            type_declarations: type_declarations,
            classes: classes,
            instances: instances,
            data_definitions: data_definitions,
            newtypes: newtypes,
            fixity_declarations: fixity_declarations,
        })
    }

    fn import(&mut self) -> ParseResult<Import<InternedStr>> {
        expect!(self, IMPORT);
        let module_name = expect!(self, NAME).value;
        let imports = if self.lexer.peek().token == LPARENS {
            self.lexer.next();
            let x = if self.lexer.peek().token == RPARENS {
                self.lexer.next();
                Vec::new()
            } else {
                let imports = self.sep_by_1(|this| Ok(expect!(this, NAME).value), COMMA)?;
                expect!(self, RPARENS);
                imports
            };
            Some(x)
        } else {
            None
        };
        Ok(Import {
            module: module_name,
            imports: imports,
        })
    }

    fn class(&mut self) -> ParseResult<Class> {
        expect!(self, CLASS);
        let (constraints, typ) = self.constrained_type()?;

        expect!(self, WHERE);
        expect!(self, LBRACE);
        let x = self.sep_by_1(|this| this.binding_or_type_declaration(), SEMICOLON)?;
        let mut bindings = Vec::new();
        let mut declarations = Vec::new();
        for decl_or_binding in x.into_iter() {
            match decl_or_binding {
                BindOrTypeDecl::Binding(mut bind) => {
                    //Bindings need to have their name altered to distinguish them from
                    //the declarations name
                    match typ {
                        Type::Application(ref op, _) => {
                            let classname = match **op {
                                Type::Constructor(ref ctor) => ctor.name,
                                _ => return self.error("Expected type operator".to_string()),
                            };
                            bind.name = encode_binding_identifier(classname, bind.name);
                        }
                        _ => {
                            return self.error(
                                "The name of the class must start with an uppercase letter"
                                    .to_string(),
                            )
                        }
                    }
                    bindings.push(bind)
                }
                BindOrTypeDecl::TypeDecl(decl) => declarations.push(decl),
            }
        }

        expect!(self, RBRACE);

        match typ {
            Type::Application(l, r) => match (*l, *r) {
                (Type::Constructor(classname), Type::Variable(var)) => {
                    return Ok(Class {
                        constraints: constraints,
                        name: classname.name,
                        variable: var,
                        declarations: declarations,
                        bindings: bindings,
                    });
                }
                _ => (),
            },
            _ => (),
        }
        self.error("Parse error in class declaration header".to_string())
    }

    fn instance(&mut self) -> ParseResult<Instance> {
        expect!(self, INSTANCE);

        let (constraints, instance_type) = self.constrained_type()?;
        match instance_type {
            Type::Application(op, arg) => {
                let classname = match *op {
                    Type::Constructor(TypeConstructor {
                        name: classname, ..
                    }) => classname,
                    _ => return self.error("Expected type operator".to_string()),
                };
                expect!(self, WHERE);
                expect!(self, LBRACE);

                let mut bindings = self.sep_by_1(|this| this.binding(), SEMICOLON)?;
                {
                    let inner_type = extract_applied_type(&*arg);
                    for bind in bindings.iter_mut() {
                        bind.name = encode_binding_identifier(inner_type.ctor().name, bind.name);
                    }
                }

                expect!(self, RBRACE);
                Ok(Instance {
                    typ: *arg,
                    classname: classname,
                    bindings: bindings,
                    constraints: constraints,
                })
            }
            _ => return self.error("TypeVariable in instance".to_string()),
        }
    }

    pub fn expression_(&mut self) -> ParseResult<TypedExpr> {
        match self.expression()? {
            Some(expr) => Ok(expr),
            None => Err(ParseError(Located {
                location: self.lexer.current().location,
                node: Error::Message(format!(
                    "Failed to parse expression at {:?}",
                    self.lexer.current().location
                )),
            })),
        }
    }

    pub fn expression(&mut self) -> ParseResult<Option<TypedExpr>> {
        let app = self.application()?;
        match self.binary_expression(app)? {
            Some(expr) => {
                //Try to parse a type signature on this expression
                if self.lexer.next().token == TYPEDECL {
                    let (constraints, typ) = self.constrained_type()?;
                    let loc = expr.location;
                    Ok(Some(TypedExpr::with_location(
                        TypeSig(
                            box expr,
                            Qualified {
                                constraints: constraints,
                                value: typ,
                            },
                        ),
                        loc,
                    )))
                } else {
                    self.lexer.backtrack();
                    Ok(Some(expr))
                }
            }
            None => Ok(None),
        }
    }

    fn list(&mut self) -> ParseResult<TypedExpr> {
        let mut expressions = Vec::new();
        loop {
            match self.expression()? {
                Some(expr) => expressions.push(expr),
                None => break,
            }
            let comma = self.lexer.next().token;
            if comma != COMMA {
                self.lexer.backtrack();
                break;
            }
        }
        expect!(self, RBRACKET);

        let nil = TypedExpr::new(Identifier(intern("[]")));
        Ok(expressions
            .into_iter()
            .rev()
            .fold(nil, |application, expr| {
                let arguments = vec![expr, application];
                make_application(
                    TypedExpr::new(Identifier(intern(":"))),
                    arguments.into_iter(),
                )
            }))
    }

    fn sub_expression(&mut self) -> ParseResult<Option<TypedExpr>> {
        let token = self.lexer.next().token;
        tracing::debug!("Begin SubExpr {:?}", self.lexer.current());
        let expr = match token {
            LPARENS => {
                let location = self.lexer.current().location;
                if self.lexer.peek().token == RPARENS {
                    self.lexer.next();
                    Some(TypedExpr::with_location(Identifier(intern("()")), location))
                } else {
                    let mut expressions = self.sep_by_1(|this| this.expression_(), COMMA)?;
                    expect!(self, RPARENS);
                    if expressions.len() == 1 {
                        let expr = expressions.pop().unwrap();
                        let loc = expr.location;
                        Some(TypedExpr::with_location(Paren(box expr), loc))
                    } else {
                        Some(new_tuple(expressions))
                    }
                }
            }
            LBRACKET => Some(self.list()?),
            LET => {
                let binds = self.let_bindings()?;

                expect!(self, IN);
                match self.expression()? {
                    Some(e) => Some(TypedExpr::new(Let(binds, box e))),
                    None => None,
                }
            }
            CASE => {
                let location = self.lexer.current().location;
                let expr = self.expression()?;

                expect!(self, OF);
                expect!(self, LBRACE);

                let alts = self.sep_by_1(|this| this.alternative(), SEMICOLON)?;
                expect!(self, RBRACE);
                match expr {
                    Some(e) => Some(TypedExpr::with_location(Case(box e, alts), location)),
                    None => None,
                }
            }
            IF => {
                let location = self.lexer.current().location;
                let pred = self.expression_()?;
                if self.lexer.peek().token == SEMICOLON {
                    self.lexer.next();
                }
                expect!(self, THEN);
                let if_true = self.expression_()?;
                if self.lexer.peek().token == SEMICOLON {
                    self.lexer.next();
                }
                expect!(self, ELSE);
                let if_false = self.expression_()?;
                Some(TypedExpr::with_location(
                    IfElse(box pred, box if_true, box if_false),
                    location,
                ))
            }
            LAMBDA => {
                let args = self.pattern_arguments()?;
                expect!(self, ARROW);
                Some(make_lambda(args.into_iter(), self.expression_()?))
            }
            DO => {
                let location = self.lexer.current().location;
                expect!(self, LBRACE);
                let mut bindings = self.sep_by_1(|this| this.do_binding(), SEMICOLON)?;
                expect!(self, RBRACE);
                if bindings.len() == 0 {
                    return Err(ParseError(Located {
                        location: self.lexer.current().location,
                        node: Error::Message(format!(
                            "{:?}: Parse error: Empty do",
                            self.lexer.current().location
                        )),
                    }));
                }
                let expr = match bindings.pop().unwrap() {
                    DoBinding::DoExpr(e) => e,
                    _ => {
                        return self.error(
                            "Parse error: Last binding in do must be an expression".to_string(),
                        )
                    }
                };
                Some(TypedExpr::with_location(Do(bindings, box expr), location))
            }
            NAME => {
                let token = self.lexer.current();
                Some(TypedExpr::with_location(
                    Identifier(token.value.clone()),
                    token.location,
                ))
            }
            NUMBER => {
                let token = self.lexer.current();
                Some(TypedExpr::with_location(
                    Literal(Integral(FromStr::from_str(token.value.as_ref()).unwrap())),
                    token.location,
                ))
            }
            FLOAT => {
                let token = self.lexer.current();
                Some(TypedExpr::with_location(
                    Literal(Fractional(FromStr::from_str(token.value.as_ref()).unwrap())),
                    token.location,
                ))
            }
            STRING => {
                let token = self.lexer.current();
                Some(TypedExpr::with_location(
                    Literal(String(token.value.clone())),
                    token.location,
                ))
            }
            CHAR => {
                let token = self.lexer.current();
                Some(TypedExpr::with_location(
                    Literal(Char(token.value.chars().next().expect("char at 0"))),
                    token.location,
                ))
            }
            _ => {
                self.lexer.backtrack();
                None
            }
        };
        Ok(expr)
    }

    fn do_binding(&mut self) -> ParseResult<DoBinding> {
        if self.lexer.next().token == LET {
            return self.let_bindings().map(DoBinding::DoLet);
        }
        tracing::debug!("Do binding {:?}", self.lexer.current());
        self.lexer.backtrack();
        let mut lookahead = 0;
        loop {
            lookahead += 1;
            match self.lexer.next().token {
                SEMICOLON | RBRACE => {
                    for _ in 0..lookahead {
                        self.lexer.backtrack();
                    }
                    return self.expression_().map(DoBinding::DoExpr);
                }
                LARROW => {
                    for _ in 0..lookahead {
                        self.lexer.backtrack();
                    }
                    let p = self.located_pattern()?;
                    self.lexer.next(); //Skip <-
                    return self.expression_().map(move |e| DoBinding::DoBind(p, e));
                }
                EOF => {
                    return Err(ParseError(Located {
                        location: self.lexer.current().location,
                        node: Error::Message("Unexpected EOF".to_string()),
                    }))
                }
                _ => {
                    tracing::debug!("Lookahead {:?}", self.lexer.current());
                }
            }
        }
    }

    fn let_bindings(&mut self) -> ParseResult<Vec<Binding>> {
        expect!(self, LBRACE);

        let binds = self.sep_by_1(|this| this.binding(), SEMICOLON)?;
        self.lexer.next_end();
        Ok(binds)
    }

    fn alternative(&mut self) -> ParseResult<Alternative> {
        let pat = self.located_pattern()?;
        static GUARD_TOKENS: &'static [TokenEnum] = &[ARROW, PIPE];
        let matches = self.expr_or_guards(GUARD_TOKENS)?;
        let where_bindings = if self.lexer.peek().token == WHERE {
            self.lexer.next();
            Some(self.let_bindings()?)
        } else {
            None
        };
        Ok(Alternative {
            pattern: pat,
            matches: matches,
            where_bindings: where_bindings,
        })
    }

    fn binary_expression(&mut self, lhs: Option<TypedExpr>) -> ParseResult<Option<TypedExpr>> {
        tracing::debug!("Parse operator expression, {:?}", &self.lexer.current());
        if self.lexer.next().token == OPERATOR {
            let op = self.lexer.current().value;
            let loc = self.lexer.current().location;
            let rhs = self.application()?;
            let rhs = self.binary_expression(rhs)?;
            let expr = match (lhs, rhs) {
                (Some(lhs), Some(rhs)) => {
                    Some(TypedExpr::with_location(OpApply(box lhs, op, box rhs), loc))
                }
                (Some(lhs), None) => {
                    let name = TypedExpr::with_location(Identifier(op), loc);
                    Some(TypedExpr::with_location(Apply(box name, box lhs), loc))
                }
                (None, Some(rhs)) => {
                    if op == intern("-") {
                        let name = TypedExpr::with_location(Identifier(intern("negate")), loc);
                        let args = vec![rhs];
                        Some(make_application(name, args.into_iter()))
                    } else {
                        let name = TypedExpr::with_location(Identifier(intern("negate")), loc);
                        let args =
                            vec![TypedExpr::with_location(Identifier(intern("#")), loc), rhs];
                        let mut apply = make_application(name, args.into_iter());
                        apply.location = loc;
                        let params = vec![intern("#")];
                        Some(make_lambda(
                            params.into_iter().map(|a| Pattern::Identifier(a)),
                            apply,
                        ))
                    }
                }
                (None, None) => return Ok(None),
            };
            Ok(expr)
        } else {
            self.lexer.backtrack();
            Ok(lhs)
        }
    }

    fn application(&mut self) -> ParseResult<Option<TypedExpr>> {
        let e = self.sub_expression()?;
        match e {
            Some(mut lhs) => {
                let mut expressions = Vec::new();
                loop {
                    let expr = self.sub_expression()?;
                    match expr {
                        Some(e) => expressions.push(e),
                        None => break,
                    }
                }
                if expressions.len() > 0 {
                    let loc = lhs.location;
                    lhs = make_application(lhs, expressions.into_iter()); //, loc);
                    lhs.location = loc;
                }
                Ok(Some(lhs))
            }
            None => Ok(None),
        }
    }

    fn constructor(&mut self, data_def: &DataDefinition) -> ParseResult<Constructor> {
        let name = expect!(self, NAME).value.clone();
        let mut arity = 0;
        let typ = self.constructor_type(&mut arity, data_def)?;
        self.lexer.backtrack();
        Ok(Constructor {
            name: name,
            typ: qualified(vec![], typ),
            tag: 0,
            arity: arity,
        })
    }

    pub fn binding(&mut self) -> ParseResult<Binding> {
        tracing::debug!("Begin binding");
        //name1 = expr
        //or
        //name2 x y = expr
        let name_token = self.lexer.next().token;
        let mut name = self.lexer.current().value.clone();
        if name_token == LPARENS {
            //Parse a name within parentheses
            let function_name = self.lexer.next().token;
            if function_name != NAME && function_name != OPERATOR {
                unexpected!(self, [NAME, OPERATOR]);
            }
            name = self.lexer.current().value.clone();
            expect!(self, RPARENS);
        } else if name_token != NAME {
            unexpected!(self, [NAME]);
        }

        //Parse the arguments for the binding
        let arguments = self.pattern_arguments()?;
        static GUARD_TOKENS: &'static [TokenEnum] = &[EQUALSSIGN, PIPE];
        let matches = self.expr_or_guards(GUARD_TOKENS)?;
        let where_bindings = if self.lexer.peek().token == WHERE {
            self.lexer.next();
            Some(self.let_bindings()?)
        } else {
            None
        };
        Ok(Binding {
            name: name.clone(),
            typ: Default::default(),
            arguments: arguments,
            where_bindings: where_bindings,
            matches: matches,
        })
    }

    fn binding_or_type_declaration(&mut self) -> ParseResult<BindOrTypeDecl> {
        //Since the token indicates an identifier it will be a function declaration or a function definition
        //We can disambiguate this by looking wether the '::' token appear.
        let token = self.lexer.next().token;
        let maybe_type_decl = if token == LPARENS {
            expect!(self, OPERATOR);
            expect!(self, RPARENS);
            let tok = self.lexer.next().token;
            self.lexer.backtrack();
            self.lexer.backtrack();
            self.lexer.backtrack();
            self.lexer.backtrack();
            tok
        } else {
            let tok = self.lexer.next().token;
            self.lexer.backtrack();
            self.lexer.backtrack();
            tok
        };

        if maybe_type_decl == TYPEDECL {
            self.type_declaration().map(BindOrTypeDecl::TypeDecl)
        } else {
            self.binding().map(BindOrTypeDecl::Binding)
        }
    }

    fn fixity_declaration(&mut self) -> ParseResult<FixityDeclaration> {
        let assoc = {
            match self.lexer.next().token {
                INFIXL => Assoc::Left,
                INFIXR => Assoc::Right,
                INFIX => Assoc::No,
                _ => unexpected!(self, [INFIXL, INFIXR, INFIX]),
            }
        };
        let precedence = match self.lexer.next().token {
            NUMBER => FromStr::from_str(self.lexer.current().value.as_ref()).unwrap(),
            _ => {
                self.lexer.backtrack();
                9
            }
        };
        let operators = self.sep_by_1(|this| Ok(expect!(this, OPERATOR).value), COMMA)?;
        Ok(FixityDeclaration {
            assoc: assoc,
            precedence: precedence,
            operators: operators,
        })
    }

    fn expr_or_guards(&mut self, end_token_and_pipe: &'static [TokenEnum]) -> ParseResult<Match> {
        let end_token = end_token_and_pipe[0];
        let token = self.lexer.next().token;
        if token == PIPE {
            self.sep_by_1(
                |this| {
                    let p = this.expression_()?;
                    if this.lexer.next().token != end_token {
                        this.lexer.backtrack();
                        return Err(this.unexpected_token(
                            &end_token_and_pipe[..1],
                            this.lexer.current().token,
                        ));
                    }
                    this.expression_().map(move |e| Guard {
                        predicate: p,
                        expression: e,
                    })
                },
                PIPE,
            )
            .map(Match::Guards)
        } else if token == end_token {
            self.expression_().map(|e| Match::Simple(e))
        } else {
            self.lexer.backtrack();
            Err(self.unexpected_token(end_token_and_pipe, self.lexer.current().token))
        }
    }

    fn make_pattern<F>(&mut self, name: InternedStr, args: F) -> ParseResult<Pattern>
    where
        F: FnOnce(&mut Parser<Iter>) -> ParseResult<Vec<Pattern>>,
    {
        let c = name.chars().next().expect("char at 0");
        if c.is_uppercase() || name == intern(":") {
            args(self).map(|ps| Pattern::Constructor(name, ps))
        } else if c == '_' {
            Ok(Pattern::WildCard)
        } else {
            Ok(Pattern::Identifier(name))
        }
    }

    fn pattern_arguments(&mut self) -> ParseResult<Vec<Pattern>> {
        let mut parameters = Vec::new();
        loop {
            let token = self.lexer.next().token;
            match token {
                NAME => {
                    let name = self.lexer.current().value;
                    let p = self.make_pattern(name, |_| Ok(vec![]))?;
                    parameters.push(p);
                }
                NUMBER => parameters.push(Pattern::Number(
                    FromStr::from_str(self.lexer.current().value.as_ref()).unwrap(),
                )),
                LPARENS => {
                    self.lexer.backtrack();
                    parameters.push(self.pattern()?);
                }
                LBRACKET => {
                    expect!(self, RBRACKET);
                    parameters.push(Pattern::Constructor(intern("[]"), vec![]));
                }
                _ => {
                    break;
                }
            }
        }
        self.lexer.backtrack();
        Ok(parameters)
    }

    fn located_pattern(&mut self) -> ParseResult<Located<Pattern>> {
        let location = self.lexer.next().location;
        self.lexer.backtrack();
        self.pattern().map(|pattern| Located {
            location: location,
            node: pattern,
        })
    }

    fn pattern(&mut self) -> ParseResult<Pattern> {
        let name_token = self.lexer.next().token;
        let name = self.lexer.current().value.clone();
        let pat = match name_token {
            LBRACKET => {
                expect!(self, RBRACKET);
                Pattern::Constructor(intern("[]"), vec![])
            }
            NAME => self.make_pattern(name, |this| this.pattern_arguments())?,
            NUMBER => Pattern::Number(FromStr::from_str(name.as_ref()).unwrap()),
            LPARENS => {
                if self.lexer.peek().token == RPARENS {
                    self.lexer.next();
                    Pattern::Constructor(intern("()"), vec![])
                } else {
                    let mut tuple_args = self.sep_by_1(|this| this.pattern(), COMMA)?;
                    expect!(self, RPARENS);
                    if tuple_args.len() == 1 {
                        tuple_args.pop().unwrap()
                    } else {
                        Pattern::Constructor(
                            intern(tuple_name(tuple_args.len()).as_ref()),
                            tuple_args,
                        )
                    }
                }
            }
            _ => unexpected!(self, [LBRACKET, NAME, NUMBER, LPARENS]),
        };
        self.lexer.next();
        if self.lexer.current().token == OPERATOR && self.lexer.current().value.as_ref() == ":" {
            Ok(Pattern::Constructor(
                self.lexer.current().value,
                vec![pat, self.pattern()?],
            ))
        } else {
            self.lexer.backtrack();
            Ok(pat)
        }
    }

    pub fn type_declaration(&mut self) -> ParseResult<TypeDeclaration> {
        let mut name;
        {
            let name_token = self.lexer.next().token;
            name = self.lexer.current().value.clone();
            if name_token == LPARENS {
                //Parse a name within parentheses
                let function_name = self.lexer.next().token;
                if function_name != NAME && function_name != OPERATOR {
                    unexpected!(self, [NAME, OPERATOR]);
                }
                name = self.lexer.current().value.clone();
                expect!(self, RPARENS);
            } else if name_token != NAME {
                unexpected!(self, [LPARENS, NAME]);
            }
        }
        expect!(self, TYPEDECL);
        let (context, typ) = self.constrained_type()?;
        Ok(TypeDeclaration {
            name: name,
            typ: Qualified {
                constraints: context,
                value: typ,
            },
        })
    }

    fn constrained_type(&mut self) -> ParseResult<(Vec<Constraint>, Type)> {
        tracing::debug!("Parse constrained type");
        let mut maybe_constraints = if self.lexer.next().token == LPARENS {
            if self.lexer.peek().token == RPARENS {
                self.lexer.next();
                vec![]
            } else {
                let t = self.sep_by_1(|this| this.parse_type(), COMMA)?;
                expect!(self, RPARENS);
                t
            }
        } else {
            self.lexer.backtrack();
            vec![self.parse_type()?]
        };
        tracing::debug!("{:?}", &maybe_constraints);
        //If there is => arrow we proceed to parse the type
        let typ = match self.lexer.next().token {
            CONTEXTARROW => self.parse_type(),
            ARROW => {
                self.lexer.backtrack();
                let mut args = Vec::new();
                swap(&mut args, &mut maybe_constraints);
                self.parse_return_type(make_tuple_type(args))
            }
            _ => {
                //If no => was found, translate the constraint list into a type
                self.lexer.backtrack();
                let mut args = Vec::new();
                swap(&mut args, &mut maybe_constraints);
                Ok(make_tuple_type(args))
            }
        }?;
        Ok((make_constraints(maybe_constraints), typ))
    }

    fn constructor_type(
        &mut self,
        arity: &mut isize,
        data_def: &DataDefinition,
    ) -> ParseResult<Type> {
        tracing::debug!("Parse constructor type");
        let token = self.lexer.next().token;
        let typ = if token == NAME {
            *arity += 1;
            let arg = if self
                .lexer
                .current()
                .value
                .chars()
                .next()
                .expect("char at 0")
                .is_lowercase()
            {
                Type::new_var(self.lexer.current().value)
            } else {
                Type::new_op(self.lexer.current().value.clone(), Vec::new())
            };
            function_type_(arg, self.constructor_type(arity, data_def)?)
        } else if token == LPARENS {
            *arity += 1;
            let arg = self.parse_type()?;
            expect!(self, RPARENS);
            function_type_(arg, self.constructor_type(arity, data_def)?)
        } else {
            data_def.typ.value.clone()
        };
        Ok(typ)
    }

    pub fn data_definition(&mut self) -> ParseResult<DataDefinition> {
        expect!(self, DATA);

        let mut definition = DataDefinition {
            constructors: Vec::new(),
            typ: qualified(vec![], Type::new_var(intern("a"))),
            parameters: HashMap::new(),
            deriving: Vec::new(),
        };
        definition.typ.value = self.data_lhs()?;
        expect!(self, EQUALSSIGN);

        definition.constructors = self.sep_by_1_func(
            |this| this.constructor(&definition),
            |t: &Token| t.token == PIPE,
        )?;
        for ii in 0..definition.constructors.len() {
            definition.constructors[ii].tag = ii as isize;
        }
        definition.deriving = self.deriving()?;
        Ok(definition)
    }

    fn newtype(&mut self) -> ParseResult<Newtype> {
        tracing::debug!("Parsing newtype");
        expect!(self, NEWTYPE);
        let typ = self.data_lhs()?;
        expect!(self, EQUALSSIGN);
        let name = expect!(self, NAME).value;
        let arg_type = match self.sub_type()? {
            Some(t) => t,
            None => return self.error("Parse error when parsing argument to new type".to_string()),
        };

        Ok(Newtype {
            typ: qualified(Vec::new(), typ.clone()),
            constructor_name: name,
            constructor_type: qualified(Vec::new(), function_type_(arg_type, typ)),
            deriving: self.deriving()?,
        })
    }

    fn data_lhs(&mut self) -> ParseResult<Type> {
        let name = expect!(self, NAME).value.clone();
        let mut typ = Type::Constructor(TypeConstructor {
            name: name,
            kind: Kind::Star.clone(),
        });
        while self.lexer.next().token == NAME {
            typ = Type::Application(box typ, box Type::new_var(self.lexer.current().value));
        }
        self.lexer.backtrack();
        Parser::<Iter>::set_kind(&mut typ, 1);
        Ok(typ)
    }

    fn deriving(&mut self) -> ParseResult<Vec<InternedStr>> {
        if self.lexer.next().token == DERIVING {
            expect!(self, LPARENS);
            let vec = self.sep_by_1(|this| Ok(expect!(this, NAME).value), COMMA)?;
            expect!(self, RPARENS);
            Ok(vec)
        } else {
            self.lexer.backtrack();
            Ok(Vec::new())
        }
    }

    fn set_kind(typ: &mut Type, kind: isize) {
        match typ {
            &mut Type::Application(ref mut lhs, _) => {
                Parser::<Iter>::set_kind(&mut **lhs, kind + 1)
            }
            _ => *typ.mut_kind() = Kind::new(kind),
        }
    }

    fn sub_type(&mut self) -> ParseResult<Option<Type>> {
        let token = (*self.lexer.next()).clone();
        let t = match token.token {
            LBRACKET => {
                self.lexer.backtrack();
                Some(self.parse_type()?)
            }
            LPARENS => {
                self.lexer.backtrack();
                Some(self.parse_type()?)
            }
            NAME => {
                if token
                    .value
                    .chars()
                    .next()
                    .expect("char at 0")
                    .is_uppercase()
                {
                    Some(Type::new_op(token.value, Vec::new()))
                } else {
                    Some(Type::new_var(token.value))
                }
            }
            _ => {
                self.lexer.backtrack();
                None
            }
        };
        Ok(t)
    }

    fn parse_type(&mut self) -> ParseResult<Type> {
        let token = (*self.lexer.next()).clone();
        match token.token {
            LBRACKET => {
                if self.lexer.next().token == RBRACKET {
                    let list = Type::new_op_kind(intern("[]"), vec![], Kind::new(2));
                    self.parse_return_type(list)
                } else {
                    self.lexer.backtrack();
                    let t = self.parse_type()?;
                    expect!(self, RBRACKET);
                    let list = list_type(t);
                    self.parse_return_type(list)
                }
            }
            LPARENS => {
                if self.lexer.peek().token == RPARENS {
                    self.lexer.next();
                    self.parse_return_type(Type::new_op(intern("()"), vec![]))
                } else {
                    let t = self.parse_type()?;
                    match self.lexer.next().token {
                        COMMA => {
                            let mut tuple_args: Vec<Type> =
                                self.sep_by_1(|this| this.parse_type(), COMMA)?;
                            tuple_args.insert(0, t);
                            expect!(self, RPARENS);

                            self.parse_return_type(make_tuple_type(tuple_args))
                        }
                        RPARENS => self.parse_return_type(t),
                        _ => {
                            unexpected!(self, [COMMA, RPARENS])
                        }
                    }
                }
            }
            NAME => {
                let mut type_arguments = Vec::new();
                loop {
                    match self.sub_type()? {
                        Some(typ) => type_arguments.push(typ),
                        None => break,
                    }
                }

                let this_type = if token
                    .value
                    .chars()
                    .next()
                    .expect("char at 0")
                    .is_uppercase()
                {
                    Type::new_op(token.value, type_arguments)
                } else {
                    Type::new_var_args(token.value, type_arguments)
                };
                self.parse_return_type(this_type)
            }
            _ => unexpected!(self, [LBRACKET, LPARENS, NAME]),
        }
    }

    fn parse_return_type(&mut self, typ: Type) -> ParseResult<Type> {
        let arrow = self.lexer.next().token;
        if arrow == ARROW {
            Ok(function_type_(typ, self.parse_type()?))
        } else {
            self.lexer.backtrack();
            Ok(typ)
        }
    }

    fn sep_by_1<T, F>(&mut self, f: F, sep: TokenEnum) -> ParseResult<Vec<T>>
    where
        F: FnMut(&mut Parser<Iter>) -> ParseResult<T>,
    {
        self.sep_by_1_func(f, |tok| tok.token == sep)
    }

    fn sep_by_1_func<T, F, P>(&mut self, mut f: F, mut sep: P) -> ParseResult<Vec<T>>
    where
        F: FnMut(&mut Parser<Iter>) -> ParseResult<T>,
        P: FnMut(&Token) -> bool,
    {
        let mut result = Vec::new();
        loop {
            result.push(f(self)?);
            if !sep(self.lexer.next()) {
                self.lexer.backtrack();
                break;
            }
        }
        Ok(result)
    }
} //end impl Parser

fn make_constraints(types: Vec<Type>) -> Vec<Constraint> {
    types
        .into_iter()
        .map(|typ| match typ {
            Type::Application(lhs, rhs) => Constraint {
                class: lhs.ctor().name.clone(),
                variables: vec![rhs.var().clone()],
            },
            _ => panic!("Parse error in constraint, non applied type"),
        })
        .collect()
}

fn make_application<I: Iterator<Item = TypedExpr>>(f: TypedExpr, args: I) -> TypedExpr {
    let mut func = f;
    for a in args {
        let loc = func.location.clone();
        func = TypedExpr::with_location(Apply(box func, box a), loc);
    }
    func
}

fn make_lambda<Iter: DoubleEndedIterator<Item = Pattern<InternedStr>>>(
    args: Iter,
    body: TypedExpr,
) -> TypedExpr {
    let mut body = body;
    for a in args.rev() {
        let loc = body.location.clone();
        body = TypedExpr::with_location(Lambda(a, box body), loc);
    }
    body
}

//Create a tuple with the constructor name inferred from the number of arguments passed in
fn new_tuple(arguments: Vec<TypedExpr>) -> TypedExpr {
    let name = TypedExpr::new(Identifier(intern(tuple_name(arguments.len()).as_ref())));
    make_application(name, arguments.into_iter())
}

fn make_tuple_type(mut types: Vec<Type>) -> Type {
    if types.len() == 1 {
        types.pop().unwrap()
    } else {
        Type::new_op(intern(tuple_name(types.len()).as_ref()), types)
    }
}

pub fn parse_string(contents: &str) -> ParseResult<Vec<Module>> {
    let mut modules = Vec::new();
    let mut visited = HashSet::new();
    parse_modules_(&mut visited, &mut modules, "<input>", contents)?;
    Ok(modules)
}

///Parses a module and all its imports
///If the modules contain a cyclic dependency fail is called.
pub fn parse_modules(modulename: &str) -> ParseResult<Vec<Module>> {
    let mut modules = Vec::new();
    let mut visited = HashSet::new();
    let contents = get_contents(modulename)?;
    parse_modules_(&mut visited, &mut modules, modulename, contents.as_ref())?;
    Ok(modules)
}

fn get_contents(modulename: &str) -> io::Result<::std::string::String> {
    let mut filename = ::std::string::String::from(modulename);
    filename.push_str(".hs"); // FIXME: filename might have hs in it
    let mut file = File::open(&filename)?;
    let mut contents = ::std::string::String::new();
    file.read_to_string(&mut contents)?;
    Ok(contents)
}

fn parse_modules_(
    visited: &mut HashSet<InternedStr>,
    modules: &mut Vec<Module>,
    modulename: &str,
    contents: &str,
) -> ParseResult<()> {
    let mut parser = Parser::new(contents.chars());
    let module = parser.module()?;
    let interned_name = intern(modulename);
    visited.insert(interned_name);
    for import in module.imports.iter() {
        if visited.contains(&import.module) {
            return parser.error("Cyclic dependency in modules".to_string());
        } else if modules.iter().all(|m| m.name != import.module) {
            //parse the module if it is not parsed
            let import_module = import.module.as_ref();
            let contents_next = get_contents(import_module)?;
            parse_modules_(visited, modules, import_module, contents_next.as_ref())?;
        }
    }
    visited.remove(&interned_name);
    modules.push(module);
    Ok(())
}

