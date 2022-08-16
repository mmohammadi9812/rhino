use compiler::*;
use core::translate::translate_module;
use interner::*;
use lambda_lift::do_lambda_lift;
use parser::Parser;
use renamer::rename_module;
use std::cell::{Ref, RefCell, RefMut};
use std::fmt;
use std::fs::File;
use std::io;
use std::io::Read;
use std::num::Wrapping;
use std::path::Path;
use std::rc::Rc;
use typecheck::TypeEnvironment;
use vm::primitive::{get_builtin, BuiltinFun};

use self::Node_::*;

#[derive(Clone)]
pub struct InstanceDictionary {
    entries: Vec<Rc<DictionaryEntry>>,
}
#[derive(Clone)]
enum DictionaryEntry {
    Function(usize),
    App(usize, InstanceDictionary),
}

pub enum Node_<'a> {
    Application(Node<'a>, Node<'a>),
    Int(isize),
    Float(f64),
    Char(char),
    Combinator(&'a SuperCombinator),
    Indirection(Node<'a>),
    Constructor(u16, Vec<Node<'a>>),
    Dictionary(InstanceDictionary),
    BuiltinFunction(usize, BuiltinFun),
}
impl<'a> Clone for Node_<'a> {
    fn clone(&self) -> Node_<'a> {
        match self {
            &Application(ref func, ref arg) => Application(func.clone(), arg.clone()),
            &Int(i) => Int(i),
            &Float(i) => Float(i),
            &Char(c) => Char(c),
            &Combinator(sc) => Combinator(sc),
            &Indirection(ref n) => Indirection(n.clone()),
            &Constructor(ref tag, ref args) => Constructor(tag.clone(), args.clone()),
            &Dictionary(ref dict) => Dictionary(dict.clone()),
            &BuiltinFunction(arity, f) => BuiltinFunction(arity, f),
        }
    }
}

#[derive(Clone)]
pub struct Node<'a> {
    node: Rc<RefCell<Node_<'a>>>,
}

impl<'a> Node<'a> {
    ///Creates a new node
    fn new(n: Node_<'a>) -> Node<'a> {
        Node {
            node: Rc::new(RefCell::new(n)),
        }
    }
    fn borrow<'b>(&'b self) -> Ref<'b, Node_<'a>> {
        (*self.node).borrow()
    }
    fn borrow_mut<'b>(&'b self) -> RefMut<'b, Node_<'a>> {
        (*self.node).borrow_mut()
    }
}
impl<'a> fmt::Debug for Node<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", *self.borrow())
    }
}
impl<'a> fmt::Debug for Node_<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &Application(ref func, ref arg) => write!(f, "({:?} {:?})", *func, *arg),
            &Int(i) => write!(f, "{:?}", i),
            &Float(i) => write!(f, "{:?}f", i),
            &Char(c) => write!(f, "'{:?}'", c),
            &Combinator(ref sc) => write!(f, "{:?}", sc.name),
            &Indirection(ref n) => write!(f, "(~> {:?})", *n),
            &Constructor(ref tag, ref args) => {
                let cons = args;
                if cons.len() > 0 {
                    match *cons[0].borrow() {
                        Char(_) => {
                            fn print_string<'a>(
                                f: &mut fmt::Formatter,
                                cons: &Vec<Node<'a>>,
                            ) -> fmt::Result {
                                if cons.len() >= 2 {
                                    match *cons[0].borrow() {
                                        Char(c) => {
                                            write!(f, "{:?}", c)?;
                                        }
                                        _ => (),
                                    }
                                    match *cons[1].borrow() {
                                        Constructor(_, ref args2) => return print_string(f, args2),
                                        _ => (),
                                    }
                                }
                                Ok(())
                            }
                            write!(f, "\"")?;
                            print_string(f, cons)?;
                            write!(f, "\"")
                        }
                        _ => {
                            //Print a normal constructor
                            write!(f, "{{{:?}", *tag)?;
                            for arg in args.iter() {
                                write!(f, " {:?}", *arg.borrow())?;
                            }
                            write!(f, "}}")
                        }
                    }
                } else {
                    //Print a normal constructor
                    write!(f, "{{{:?}", *tag)?;
                    for arg in args.iter() {
                        write!(f, " {:?}", *arg.borrow())?;
                    }
                    write!(f, "}}")
                }
            }
            &Dictionary(ref dict) => write!(f, "{:?}", dict),
            &BuiltinFunction(..) => write!(f, "<extern function>"),
        }
    }
}
impl fmt::Debug for InstanceDictionary {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "[")?;
        if self.entries.len() > 0 {
            write!(f, "{:?}", *self.entries[0])?;
        }
        for entry in self.entries.iter().skip(1) {
            write!(f, ", {:?}", **entry)?;
        }
        write!(f, "]")
    }
}
impl fmt::Debug for DictionaryEntry {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            DictionaryEntry::Function(index) => write!(f, "{:?}", index),
            DictionaryEntry::App(ref func, ref arg) => write!(f, "({:?} {:?})", *func, *arg),
        }
    }
}

pub struct VM {
    ///Vector of all assemblies which are loaded.
    pub assembly: Vec<Assembly>,
    ///A pair of (assembly_index, function_index).
    globals: Vec<(usize, usize)>,
}

impl<'a> VM {
    pub fn new() -> VM {
        VM {
            assembly: Vec::new(),
            globals: Vec::new(),
        }
    }

    ///Adds an assembly to the VM, adding entries to the global table as necessary
    pub fn add_assembly(&mut self, assembly: Assembly) -> usize {
        self.assembly.push(assembly);
        let assembly_index = self.assembly.len() - 1;
        for index in 0..self.assembly.last().unwrap().super_combinators.len() {
            self.globals.push((assembly_index, index));
        }
        assembly_index
    }
    ///Returns a reference to the assembly at the index
    pub fn get_assembly(&self, index: usize) -> &Assembly {
        &self.assembly[index]
    }

    ///Evaluates the code into Head Normal Form (HNF)
    pub fn evaluate(&self, code: &[Instruction], assembly_id: usize) -> Node_ {
        let mut stack = Vec::new();
        self.execute(&mut stack, code, assembly_id);
        self.deepseq(stack, assembly_id)
    }

    ///Evaluates the what is at the top of the stack into HNF
    fn deepseq(&'a self, mut stack: Vec<Node<'a>>, assembly_id: usize) -> Node_<'a> {
        static EVALCODE: &'static [Instruction] = &[Instruction::Eval];
        self.execute(&mut stack, EVALCODE, assembly_id);
        match *stack[0].borrow() {
            Constructor(tag, ref vals) => {
                let mut ret = Vec::new();
                for v in vals.iter() {
                    let s = vec![v.clone()];
                    let x = self.deepseq(s, assembly_id);
                    ret.push(Node::new(x));
                }
                Constructor(tag, ret)
            }
            _ => stack[0].borrow().clone(),
        }
    }

    ///Executes a sequence of instructions, leaving the result on the top of the stack
    pub fn execute(&'a self, stack: &mut Vec<Node<'a>>, code: &[Instruction], assembly_id: usize) {
        use compiler::Instruction::*;
        // println!("----------------------------");
        // println!("Entering frame with stack");
        // for x in stack.iter() {
        //     println!("{:?}", *x.borrow());
        // }
        // println!("");
        let mut i = Wrapping(0);
        while i.0 < code.len() {
            // println!("Executing instruction {:?} : {:?}", i.0, code[i.0]);
            match code[i.0] {
                Add => primitive(stack, |l, r| l + r),
                Sub => primitive(stack, |l, r| l - r),
                Multiply => primitive(stack, |l, r| l * r),
                Divide => primitive(stack, |l, r| l / r),
                Remainder => primitive(stack, |l, r| l % r),
                IntEQ => primitive_int(stack, |l, r| {
                    if l == r {
                        Constructor(0, Vec::new())
                    } else {
                        Constructor(1, Vec::new())
                    }
                }),
                IntLT => primitive_int(stack, |l, r| {
                    if l < r {
                        Constructor(0, Vec::new())
                    } else {
                        Constructor(1, Vec::new())
                    }
                }),
                IntLE => primitive_int(stack, |l, r| {
                    if l <= r {
                        Constructor(0, Vec::new())
                    } else {
                        Constructor(1, Vec::new())
                    }
                }),
                IntGT => primitive_int(stack, |l, r| {
                    if l > r {
                        Constructor(0, Vec::new())
                    } else {
                        Constructor(1, Vec::new())
                    }
                }),
                IntGE => primitive_int(stack, |l, r| {
                    if l >= r {
                        Constructor(0, Vec::new())
                    } else {
                        Constructor(1, Vec::new())
                    }
                }),
                DoubleAdd => primitive_float(stack, |l, r| Float(l + r)),
                DoubleSub => primitive_float(stack, |l, r| Float(l - r)),
                DoubleMultiply => primitive_float(stack, |l, r| Float(l * r)),
                DoubleDivide => primitive_float(stack, |l, r| Float(l / r)),
                DoubleRemainder => primitive_float(stack, |l, r| Float(l % r)),
                DoubleEQ => primitive_float(stack, |l, r| {
                    if l == r {
                        Constructor(0, Vec::new())
                    } else {
                        Constructor(1, Vec::new())
                    }
                }),
                DoubleLT => primitive_float(stack, |l, r| {
                    if l < r {
                        Constructor(0, Vec::new())
                    } else {
                        Constructor(1, Vec::new())
                    }
                }),
                DoubleLE => primitive_float(stack, |l, r| {
                    if l <= r {
                        Constructor(0, Vec::new())
                    } else {
                        Constructor(1, Vec::new())
                    }
                }),
                DoubleGT => primitive_float(stack, |l, r| {
                    if l > r {
                        Constructor(0, Vec::new())
                    } else {
                        Constructor(1, Vec::new())
                    }
                }),
                DoubleGE => primitive_float(stack, |l, r| {
                    if l >= r {
                        Constructor(0, Vec::new())
                    } else {
                        Constructor(1, Vec::new())
                    }
                }),
                IntToDouble => {
                    let top = stack.pop().unwrap();
                    stack.push(match *top.borrow() {
                        Int(i) => Node::new(Float(i as f64)),
                        _ => panic!("Excpected Int in Int -> Double cast"),
                    });
                }
                DoubleToInt => {
                    let top = stack.pop().unwrap();
                    stack.push(match *top.borrow() {
                        Float(f) => Node::new(Int(f as isize)),
                        _ => panic!("Excpected Double in Double -> Int cast"),
                    });
                }
                PushInt(value) => {
                    stack.push(Node::new(Int(value)));
                }
                PushFloat(value) => {
                    stack.push(Node::new(Float(value)));
                }
                PushChar(value) => {
                    stack.push(Node::new(Char(value)));
                }
                Push(index) => {
                    let x = stack[index].clone();
                    // println!("Pushed {:?}", *x.borrow());
                    // for j in 0..stack.len() {
                    //     println!(" {:?}  {:?}", j, *stack[j].borrow());
                    // }
                    stack.push(x);
                }
                PushGlobal(index) => {
                    let (assembly_index, index) = self.globals[index];
                    let sc = &self.assembly[assembly_index].super_combinators[index];
                    stack.push(Node::new(Combinator(sc)));
                }
                PushBuiltin(index) => {
                    let (arity, f) = get_builtin(index);
                    stack.push(Node::new(BuiltinFunction(arity, f)));
                }
                Mkap => {
                    assert!(stack.len() >= 2);
                    let func = stack.pop().unwrap();
                    let arg = stack.pop().unwrap();
                    // println!("Mkap {:?} {:?}", *func.borrow(), *arg.borrow());
                    stack.push(Node::new(Application(func, arg)));
                }
                Eval => {
                    static UNWINDCODE: &'static [Instruction] = &[Unwind];
                    let old = stack.pop().unwrap();
                    let mut new_stack = vec![old.clone()];
                    self.execute(&mut new_stack, UNWINDCODE, assembly_id);
                    stack.push(new_stack.pop().unwrap());
                    // println!("{:?}", stack);
                    let new = stack.last().unwrap().borrow().clone();
                    *(*old.node).borrow_mut() = new;
                    // println!("{:?}", stack);
                }
                Pop(num) => {
                    for _ in 0..num {
                        stack.pop();
                    }
                }
                Update(index) => {
                    stack[index] = Node::new(Indirection(stack.last().unwrap().clone()));
                }
                Unwind => {
                    fn unwind<'a, F>(
                        i_ptr: &mut Wrapping<usize>,
                        arity: usize,
                        stack: &mut Vec<Node<'a>>,
                        f: F,
                    ) where
                        F: FnOnce(&mut Vec<Node<'a>>) -> Node<'a>,
                    {
                        if stack.len() - 1 < arity {
                            while stack.len() > 1 {
                                stack.pop();
                            }
                        } else {
                            for j in (stack.len() - arity - 1)..(stack.len() - 1) {
                                let temp = match *stack[j].borrow() {
                                    Application(_, ref arg) => arg.clone(),
                                    _ => panic!("Expected Application"),
                                };
                                stack[j] = temp;
                            }
                            let value = {
                                let mut new_stack = Vec::new();
                                for i in 0..arity {
                                    let index = stack.len() - i - 2;
                                    new_stack.push(stack[index].clone());
                                }
                                f(&mut new_stack)
                            };
                            for _ in 0..(arity + 1) {
                                stack.pop();
                            }
                            stack.push(value);
                            *i_ptr = *i_ptr - Wrapping(1);
                        }
                    }
                    let x = (*stack.last().unwrap().borrow()).clone();
                    // println!("Unwinding {:?}", x);
                    match x {
                        Application(func, _) => {
                            stack.push(func);
                            i = i - Wrapping(1); //Redo the unwind instruction
                        }
                        Combinator(comb) => {
                            // println!(">>> Call {:?}", comb.name);
                            unwind(&mut i, comb.arity, stack, |new_stack| {
                                self.execute(new_stack, &*comb.instructions, comb.assembly_id);
                                new_stack.pop().unwrap()
                            });
                        }
                        BuiltinFunction(arity, func) => {
                            unwind(&mut i, arity, stack, |new_stack| {
                                func(self, new_stack.as_ref())
                            });
                        }
                        Indirection(node) => {
                            *stack.last_mut().unwrap() = node;
                            i = i - Wrapping(1); //Redo the unwind instruction
                        }
                        _ => (),
                    }
                }
                Slide(size) => {
                    let top = stack.pop().unwrap();
                    for _ in 0..size {
                        stack.pop();
                    }
                    stack.push(top);
                }
                Split(_) => {
                    let temp = stack.pop().unwrap();
                    let temp = temp.borrow();
                    match *temp {
                        Constructor(_, ref fields) => {
                            for field in fields.iter() {
                                stack.push(field.clone());
                            }
                        }
                        _ => panic!("Expected constructor in Split instruction"),
                    }
                }
                Pack(tag, arity) => {
                    let mut args = Vec::new();
                    for _ in 0..arity {
                        args.push(stack.pop().unwrap());
                    }
                    stack.push(Node::new(Constructor(tag, args)));
                }
                JumpFalse(address) => {
                    match *stack.last().unwrap().borrow() {
                        Constructor(0, _) => (),
                        Constructor(1, _) => i = Wrapping(address - 1),
                        _ => (),
                    }
                    stack.pop();
                }
                CaseJump(jump_tag) => {
                    let jumped = match *stack.last().unwrap().borrow() {
                        Constructor(tag, _) => {
                            if jump_tag == tag as usize {
                                i = i + Wrapping(1); //Skip the jump instruction ie continue to the next test
                                true
                            } else {
                                false
                            }
                        }
                        ref x => {
                            panic!("Expected constructor when executing CaseJump, got {:?}", *x)
                        }
                    };
                    if !jumped {
                        stack.pop();
                    }
                }
                Jump(to) => {
                    i = Wrapping(to - 1);
                }
                PushDictionary(index) => {
                    let assembly = &self.assembly[assembly_id];
                    let dict: &[usize] = &*assembly.instance_dictionaries[index];
                    let dict = InstanceDictionary {
                        entries: dict
                            .iter()
                            .map(|i| Rc::new(DictionaryEntry::Function(*i)))
                            .collect(),
                    };
                    stack.push(Node::new(Dictionary(dict)));
                }
                PushDictionaryMember(index) => {
                    let sc = {
                        let x = stack[0].borrow();
                        let dict = match *x {
                            Dictionary(ref x) => x,
                            ref x => panic!("Attempted to retrieve {:?} as dictionary", *x),
                        };
                        match *dict.entries[index] {
                            DictionaryEntry::Function(gi) => {
                                let (assembly_index, i) = self.globals[gi];
                                Combinator(&self.assembly[assembly_index].super_combinators[i])
                            }
                            DictionaryEntry::App(gi, ref dict) => {
                                let (assembly_index, i) = self.globals[gi];
                                let sc = &self.assembly[assembly_index].super_combinators[i];
                                Application(
                                    Node::new(Combinator(sc)),
                                    Node::new(Dictionary(dict.clone())),
                                )
                            }
                        }
                    };
                    stack.push(Node::new(sc));
                }
                MkapDictionary => {
                    let a = stack.pop().unwrap();
                    let a = a.borrow();
                    let arg = match *a {
                        Dictionary(ref d) => d,
                        _ => panic!(),
                    };
                    let func = stack.pop().unwrap();
                    let mut new_dict = InstanceDictionary {
                        entries: Vec::new(),
                    };
                    match *func.borrow() {
                        Dictionary(ref d) => {
                            for entry in d.entries.iter() {
                                match **entry {
                                    DictionaryEntry::Function(index) => {
                                        new_dict.entries.push(Rc::new(DictionaryEntry::App(
                                            index,
                                            arg.clone(),
                                        )));
                                    }
                                    _ => panic!(),
                                }
                            }
                        }
                        _ => panic!(),
                    }
                    stack.push(Node::new(Dictionary(new_dict)));
                }
                ConstructDictionary(size) => {
                    let mut new_dict = InstanceDictionary {
                        entries: Vec::new(),
                    };
                    for _ in 0..size {
                        let temp = stack.pop().unwrap();
                        let temp = temp.borrow();
                        match *temp {
                            Dictionary(ref d) => {
                                new_dict.entries.extend(d.entries.iter().map(|x| x.clone()));
                            }
                            ref x => panic!("Unexpected {:?}", x),
                        }
                    }
                    stack.push(Node::new(Dictionary(new_dict)));
                }
                PushDictionaryRange(start, size) => {
                    let mut new_dict = InstanceDictionary {
                        entries: Vec::new(),
                    };
                    match *stack[0].borrow() {
                        Dictionary(ref d) => {
                            new_dict
                                .entries
                                .extend(d.entries.iter().skip(start).take(size).map(|x| x.clone()));
                        }
                        _ => panic!(),
                    }
                    stack.push(Node::new(Dictionary(new_dict)));
                }
            }
            i = i + Wrapping(1);
        }
        // println!("End frame");
        // println!("--------------------------");
    }
}

///Exucutes a binary primitive instruction taking two integers
fn primitive_int<'a, F>(stack: &mut Vec<Node<'a>>, f: F)
where
    F: FnOnce(isize, isize) -> Node_<'a>,
{
    let l = stack.pop().unwrap();
    let r = stack.pop().unwrap();
    let l = l.borrow();
    let r = r.borrow();
    match (&*l, &*r) {
        (&Int(lhs), &Int(rhs)) => stack.push(Node::new(f(lhs, rhs))),
        (lhs, rhs) => panic!(
            "Expected fully evaluted numbers in primitive instruction\n LHS: {:?}\nRHS: {:?} ",
            lhs, rhs
        ),
    }
}
///Exucutes a binary primitive instruction taking two doubles
fn primitive_float<'a, F>(stack: &mut Vec<Node<'a>>, f: F)
where
    F: FnOnce(f64, f64) -> Node_<'a>,
{
    let l = stack.pop().unwrap();
    let r = stack.pop().unwrap();
    let l = l.borrow();
    let r = r.borrow();
    match (&*l, &*r) {
        (&Float(lhs), &Float(rhs)) => stack.push(Node::new(f(lhs, rhs))),
        (lhs, rhs) => panic!(
            "Expected fully evaluted numbers in primitive instruction\n LHS: {:?}\nRHS: {:?} ",
            lhs, rhs
        ),
    }
}
fn primitive<F>(stack: &mut Vec<Node>, f: F)
where
    F: FnOnce(isize, isize) -> isize,
{
    primitive_int(stack, move |l, r| Int(f(l, r)))
}

#[derive(PartialEq, Debug)]
pub enum VMResult {
    Int(isize),
    Double(f64),
    Constructor(u16, Vec<VMResult>),
}

macro_rules! vm_error {
    ($($pre: ident :: $post: ident),+) => {

    #[derive(Debug)]
    pub enum VMError {
        Io(io::Error),
        $($post(::$pre::$post)),+
    }

    impl fmt::Display for VMError {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            match *self {
                VMError::Io(ref e) => write!(f, "{}", e),
                $(VMError::$post(ref e) => write!(f, "{}", e)),+
            }
        }
    }

    impl From<io::Error> for VMError {
        fn from(e: io::Error) -> Self { VMError::Io(e) }
    }

    $(impl From<::$pre::$post> for VMError {
        fn from(e: ::$pre::$post) -> Self { VMError::$post(e) }
    })+
    }
}
vm_error! { parser::ParseError, renamer::RenamerError, typecheck::TypeError }

pub fn compile_iter<T: Iterator<Item = char>>(iterator: T) -> Result<Assembly, VMError> {
    let mut parser = Parser::new(iterator);
    let module = parser.module()?;
    let mut module = rename_module(module)?;

    let mut typer = TypeEnvironment::new();
    typer.typecheck_module(&mut module)?;
    let core_module = do_lambda_lift(translate_module(module));

    let mut compiler = Compiler::new();
    Ok(compiler.compile_module(&core_module))
}

///Compiles a single file
pub fn compile_file(filename: &str) -> Result<Assembly, VMError> {
    let path = &Path::new(filename);
    let mut file = File::open(path)?;
    let mut contents = ::std::string::String::new();
    file.read_to_string(&mut contents)?;
    compile_iter(contents.chars())
}

pub fn extract_result(node: Node_) -> Option<VMResult> {
    match node {
        Constructor(tag, fields) => {
            let mut result = Vec::new();
            for field in fields.iter() {
                match extract_result((*field.borrow()).clone()) {
                    Some(x) => result.push(x),
                    None => return None,
                }
            }
            Some(VMResult::Constructor(tag, result))
        }
        Int(i) => Some(VMResult::Int(i)),
        Float(i) => Some(VMResult::Double(i)),
        x => {
            println!("Can't extract result {:?}", x);
            None
        }
    }
}

pub fn execute_main_string(module: &str) -> Result<Option<VMResult>, String> {
    let assemblies = compile_string(module)?;
    execute_main_module_(assemblies)
}

///Takes a module with a main function and compiles it and all its imported modules
///and then executes the main function
pub fn execute_main_module(modulename: &str) -> Result<Option<VMResult>, String> {
    let assemblies = compile_module(modulename)?;
    execute_main_module_(assemblies)
}

fn execute_main_module_(assemblies: Vec<Assembly>) -> Result<Option<VMResult>, String> {
    let mut vm = VM::new();
    for assembly in assemblies.into_iter() {
        vm.add_assembly(assembly);
    }
    let x = vm
        .assembly
        .iter()
        .flat_map(|a| a.super_combinators.iter())
        .find(|sc| sc.name.name == intern("main"));
    match x {
        Some(sc) => {
            assert!(sc.arity == 0);
            let result = vm.evaluate(&*sc.instructions, sc.assembly_id);
            Ok(extract_result(result))
        }
        None => Ok(None),
    }
}

//We mirror the naming scheme from Haskell here which is camelCase
#[allow(non_snake_case)]
mod primitive {

    use compiler::Instruction;
    use compiler::Instruction::Eval;
    use std::fs::File;
    use std::io::Read;
    use vm::Node_::{Application, BuiltinFunction, Char, Constructor};
    use vm::{Node, Node_, VM};

    pub fn get_builtin(i: usize) -> (usize, BuiltinFun) {
        match i {
            0 => (1, error),
            1 => (2, seq),
            2 => (2, readFile),
            3 => (3, io_bind),
            4 => (2, io_return),
            5 => (2, putStrLn),
            6 => (2, compare_tags),
            _ => panic!("undefined primitive"),
        }
    }

    pub type BuiltinFun = for<'a> fn(&'a VM, &[Node<'a>]) -> Node<'a>;

    fn error<'a>(vm: &'a VM, stack: &[Node<'a>]) -> Node<'a> {
        let mut vec = Vec::new();
        vec.push(stack[0].clone());
        let node = vm.deepseq(vec, 123);
        panic!("error: {:?}", node)
    }
    fn eval<'a>(vm: &'a VM, node: Node<'a>) -> Node<'a> {
        static EVALCODE: &'static [Instruction] = &[Eval];
        let mut temp = Vec::new();
        temp.push(node);
        vm.execute(&mut temp, EVALCODE, 123);
        temp.pop().unwrap()
    }
    fn seq<'a>(vm: &'a VM, stack: &[Node<'a>]) -> Node<'a> {
        eval(vm, stack[0].clone());
        stack[1].clone()
    }
    fn io_bind<'a>(_vm: &'a VM, stack: &[Node<'a>]) -> Node<'a> {
        //IO a -> (a -> IO b) -> IO b
        //IO a = (RealWorld -> (a, RealWorld)
        //((RealWorld -> (a, RealWorld)) -> (a -> RealWorld -> (b, RealWorld)) -> RealWorld -> (b, RealWorld)
        //             0                                      1                        2
        //(a, RealWorld)
        let aw = Node::new(Application(stack[0].clone(), stack[2].clone()));
        let p = Node::new(BuiltinFunction(2, pass));
        Node::new(Application(Node::new(Application(p, aw)), stack[1].clone()))
    }
    fn pass<'a>(vm: &'a VM, stack: &[Node<'a>]) -> Node<'a> {
        //(a, RealWorld) -> (a -> RealWorld -> (b, RealWorld)) -> (b, RealWorld)
        eval(vm, stack[0].clone());
        let aw = stack[0].borrow();
        let (a, rw) = match *aw {
            Constructor(_, ref args) => (&args[0], &args[1]),
            _ => panic!("pass exepected constructor"),
        };
        Node::new(Application(
            Node::new(Application(stack[1].clone(), a.clone())),
            rw.clone(),
        ))
    }
    fn io_return<'a>(_vm: &'a VM, stack: &[Node<'a>]) -> Node<'a> {
        //a -> RealWorld -> (a, RealWorld)
        Node::new(Constructor(0, vec![stack[0].clone(), stack[1].clone()]))
    }
    fn readFile<'a>(vm: &'a VM, stack: &[Node<'a>]) -> Node<'a> {
        let mut temp = Vec::new();
        temp.push(stack[0].clone());
        let node_filename = vm.deepseq(temp, 123);
        let filename = get_string(&node_filename);
        let mut file = match File::open(&filename) {
            Ok(f) => f,
            Err(err) => panic!("error: readFile -> {:?}", err),
        };
        let mut s = ::std::string::String::new();
        let (begin, _end) = match file.read_to_string(&mut s) {
            Ok(_) => create_string(&s),
            Err(err) => panic!("error: readFile -> {:?}", err),
        };
        //Return (String, RealWorld)
        Node::new(Constructor(0, vec![begin, stack[1].clone()]))
    }

    fn putStrLn<'a>(vm: &'a VM, stack: &[Node<'a>]) -> Node<'a> {
        let mut temp = Vec::new();
        temp.push(stack[0].clone());
        let msg_node = vm.deepseq(temp, 123);
        let msg = get_string(&msg_node);
        println!("{:?}", msg);
        Node::new(Constructor(
            0,
            vec![Node::new(Constructor(0, vec![])), stack[1].clone()],
        ))
    }
    fn get_string<'a>(node: &Node_<'a>) -> String {
        fn get_string_<'a>(buffer: &mut String, node: &Node_<'a>) {
            match *node {
                Constructor(_, ref args) => {
                    if args.len() == 2 {
                        match *args[0].borrow() {
                            Char(c) => buffer.push(c),
                            _ => panic!("Unevaluated char"),
                        }
                        get_string_(buffer, &*args[1].borrow());
                    }
                }
                _ => panic!("Unevaluated list"),
            }
        }
        let mut buffer = String::new();
        get_string_(&mut buffer, node);
        buffer
    }
    fn create_string<'a>(s: &str) -> (Node<'a>, Node<'a>) {
        let mut node = Node::new(Constructor(0, vec![]));
        let first = node.clone();
        for c in s.chars() {
            let temp = match *node.borrow_mut() {
                Constructor(ref mut tag, ref mut args) => {
                    *tag = 1;
                    args.push(Node::new(Char(c)));
                    args.push(Node::new(Constructor(0, Vec::new())));
                    args[1].clone()
                }
                _ => panic!(),
            };
            node = temp;
        }
        (first, node)
    }
    ///Compares the tags of two constructors, returning an Ordering
    fn compare_tags<'a>(vm: &'a VM, stack: &[Node<'a>]) -> Node<'a> {
        use std::cmp::Ordering;
        assert_eq!(stack.len(), 2);
        let lhs = eval(vm, stack[0].clone());
        let rhs = eval(vm, stack[1].clone());
        let tag = match (&*lhs.borrow(), &*rhs.borrow()) {
            (&Constructor(lhs, _), &Constructor(rhs, _)) => match lhs.cmp(&rhs) {
                Ordering::Less => 0,
                Ordering::Equal => 1,
                Ordering::Greater => 2,
            },
            (_, _) => 1, //EQ
        };
        Node::new(Constructor(tag, Vec::new()))
    }
}

