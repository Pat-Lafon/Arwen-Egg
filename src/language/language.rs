use std::collections::HashMap;
use std::fmt::{Debug, Display};
use std::hash::Hash;
use std::rc::Rc;
use std::str::FromStr;

use itertools::Itertools;

use crate::language::{Signature, TypeSystemBounds};

use super::{BaseType, Examples, RefinementType, TestCase};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Tree<T> {
    Leaf,
    Node(T, Box<Tree<T>>, Box<Tree<T>>),
}

impl<T> Tree<T> {
    pub fn height(&self) -> usize {
        match self {
            Tree::Leaf => 0,
            Tree::Node(_, t1, t2) => 1 + std::cmp::max(t1.height(), t2.height()),
        }
    }
}

impl<T: Display> Display for Tree<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Tree::Leaf => "leaf".to_string(),
                Tree::Node(n, t1, t2) => format!("node {} ({}) ({})", n, t1, t2),
            }
        )
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct List(Vec<i64>);

impl List {
    pub fn new() -> Self {
        List(Vec::new())
    }

    pub fn cons(mut self, v: i64) -> Self {
        self.0.push(v);
        self
    }

    pub fn hd(&self) -> Option<i64> {
        self.0.last().cloned()
    }

    pub fn tail(mut self) -> Self {
        self.0.pop();
        self
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn member(&self, i: &i64) -> bool {
        self.0.contains(i)
    }
}

impl Display for List {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[{}]", self.0.iter().rev().join(", "))
    }
}

#[derive(Debug, Clone, PartialEq, Hash, Eq, PartialOrd, Ord)]
pub enum Constant {
    Int(i64),
    Bool(bool),
    IntList(List),
    IntTree(Tree<i64>),
}

impl Constant {
    pub fn is_base_case(&self) -> bool {
        match self {
            Constant::Int(i) => i == &0,
            Constant::Bool(_) => panic!(),
            Constant::IntList(l) => l.is_empty(),
            Constant::IntTree(t) => matches!(t, Tree::Leaf),
        }
    }
}

impl FromStr for Constant {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        todo!()
    }
}

impl Display for Constant {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Constant::Int(i) => i.to_string(),
                Constant::Bool(b) => b.to_string(),
                Constant::IntList(l) => l.to_string(),
                Constant::IntTree(_) => "tree".to_string(),
            }
        )
    }
}

impl From<i64> for Constant {
    fn from(i: i64) -> Self {
        Constant::Int(i)
    }
}

impl TryFrom<Constant> for i64 {
    type Error = InvalidProg;

    fn try_from(value: Constant) -> Result<Self, Self::Error> {
        match value {
            Constant::Int(i) => Ok(i),
            _ => Err(InvalidProg {}),
        }
    }
}

impl TryFrom<&Constant> for i64 {
    type Error = InvalidProg;

    fn try_from(value: &Constant) -> Result<Self, Self::Error> {
        match value {
            Constant::Int(i) => Ok(*i),
            _ => Err(InvalidProg {}),
        }
    }
}

impl From<bool> for Constant {
    fn from(b: bool) -> Self {
        Constant::Bool(b)
    }
}

impl TryFrom<Constant> for bool {
    type Error = InvalidProg;

    fn try_from(value: Constant) -> Result<Self, Self::Error> {
        match value {
            Constant::Bool(b) => Ok(b),
            _ => Err(InvalidProg {}),
        }
    }
}

impl TryFrom<&Constant> for bool {
    type Error = InvalidProg;

    fn try_from(value: &Constant) -> Result<Self, Self::Error> {
        match value {
            Constant::Bool(b) => Ok(*b),
            _ => Err(InvalidProg {}),
        }
    }
}

/* impl From<Vec<i64>> for Constant {
    fn from(v: Vec<i64>) -> Self {
        Constant::IntList(List(v))
    }
} */

impl TryFrom<Constant> for Vec<i64> {
    type Error = InvalidProg;

    fn try_from(value: Constant) -> Result<Self, Self::Error> {
        match value {
            Constant::IntList(v) => Ok(v.0),
            _ => Err(InvalidProg {}),
        }
    }
}

impl From<Tree<i64>> for Constant {
    fn from(t: Tree<i64>) -> Self {
        Constant::IntTree(t)
    }
}

impl TryFrom<Constant> for Tree<i64> {
    type Error = InvalidProg;

    fn try_from(value: Constant) -> Result<Self, Self::Error> {
        match value {
            Constant::IntTree(t) => Ok(t),
            _ => Err(InvalidProg {}),
        }
    }
}

pub type SynthFuncType = dyn Fn(&Vec<Constant>) -> Result<Constant, InvalidProg>;

#[derive(Clone)]
pub struct Operation<T> {
    pub name: String,
    pub sig: Signature<T>,
    pub code: Rc<SynthFuncType>,
}

impl<T> Operation<T> {
    pub fn execute(&self, args: &Vec<Constant>) -> Result<Constant, InvalidProg> {
        (self.code)(args)
    }
}

impl<T> Display for Operation<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)
    }
}

impl<T: Debug> std::fmt::Debug for Operation<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Operation")
            .field("name", &self.name)
            .field("sig", &self.sig)
            .finish()
    }
}

impl<T> Hash for Operation<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.name.hash(state);
    }
}

impl<T> PartialEq for Operation<T> {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name
    }
}

impl<T> Eq for Operation<T> {}

impl<T> PartialOrd for Operation<T> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<T> Ord for Operation<T> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.name.cmp(&other.name)
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Variable<T: TypeSystemBounds> {
    pub name: String,
    pub ty: T,
}

impl<T: TypeSystemBounds> Display for Variable<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)
    }
}

impl<T: TypeSystemBounds> FromStr for Variable<T> {
    type Err = ();

    fn from_str(_s: &str) -> Result<Self, Self::Err> {
        todo!()
    }
}

// Program node that can be used to create a block/trace
// Basically no if statements or recursive calls
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum LinearProgramNode<T: TypeSystemBounds> {
    Constant(Constant),
    Variable(Variable<T>),
    Operation(Operation<T>),
}

impl<T: TypeSystemBounds> Display for LinearProgramNode<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LinearProgramNode::Constant(c) => write!(f, "{c}"),
            LinearProgramNode::Variable(v) => write!(f, "{v}"),
            LinearProgramNode::Operation(o) => write!(f, "{}", o),
        }
    }
}

impl<T: TypeSystemBounds> TryFrom<LinearProgramNode<T>> for Operation<T> {
    type Error = ();

    fn try_from(value: LinearProgramNode<T>) -> Result<Self, Self::Error> {
        match value {
            LinearProgramNode::Constant(_) => Err(()),
            LinearProgramNode::Variable(_) => Err(()),
            LinearProgramNode::Operation(o) => Ok(o),
        }
    }
}

impl<T: TypeSystemBounds> TryFrom<LinearProgramNode<T>> for Variable<T> {
    type Error = ();

    fn try_from(value: LinearProgramNode<T>) -> Result<Self, Self::Error> {
        match value {
            LinearProgramNode::Constant(_) => Err(()),
            LinearProgramNode::Variable(v) => Ok(v),
            LinearProgramNode::Operation(_) => Err(()),
        }
    }
}

impl<T: TypeSystemBounds> From<Variable<T>> for LinearProgramNode<T> {
    fn from(value: Variable<T>) -> Self {
        LinearProgramNode::Variable(value)
    }
}

impl<T: TypeSystemBounds> From<Constant> for LinearProgramNode<T> {
    fn from(value: Constant) -> Self {
        LinearProgramNode::Constant(value)
    }
}

impl<T: TypeSystemBounds> From<Operation<T>> for LinearProgramNode<T> {
    fn from(value: Operation<T>) -> Self {
        LinearProgramNode::Operation(value)
    }
}

impl<T: TypeSystemBounds> From<Constant> for ProgramNode<T> {
    fn from(value: Constant) -> Self {
        Into::<LinearProgramNode<T>>::into(value).into()
    }
}

impl<T: TypeSystemBounds> From<Variable<T>> for ProgramNode<T> {
    fn from(value: Variable<T>) -> Self {
        Into::<LinearProgramNode<T>>::into(value).into()
    }
}

impl<T: TypeSystemBounds> From<Operation<T>> for ProgramNode<T> {
    fn from(value: Operation<T>) -> Self {
        Into::<LinearProgramNode<T>>::into(value).into()
    }
}

impl<T: TypeSystemBounds> TryFrom<LinearProgramNode<T>> for Constant {
    type Error = ();

    fn try_from(value: LinearProgramNode<T>) -> Result<Self, Self::Error> {
        match value {
            LinearProgramNode::Constant(c) => Ok(c),
            LinearProgramNode::Variable(_) => Err(()),
            LinearProgramNode::Operation(_) => Err(()),
        }
    }
}

impl<T: TypeSystemBounds> TryFrom<ProgramNode<T>> for LinearProgramNode<T> {
    type Error = ();

    fn try_from(value: ProgramNode<T>) -> Result<Self, ()> {
        match value {
            ProgramNode::Constant(c) => Ok(LinearProgramNode::Constant(c)),
            ProgramNode::Variable(v) => Ok(LinearProgramNode::Variable(v)),
            ProgramNode::Operation(o) => Ok(LinearProgramNode::Operation(o)),
            ProgramNode::If => Err(()),
            ProgramNode::Rec(_) => Err(()),
        }
    }
}

impl<T: TypeSystemBounds> From<LinearProgramNode<T>> for ProgramNode<T> {
    fn from(value: LinearProgramNode<T>) -> Self {
        match value {
            LinearProgramNode::Constant(c) => ProgramNode::Constant(c),
            LinearProgramNode::Variable(v) => ProgramNode::Variable(v),
            LinearProgramNode::Operation(o) => ProgramNode::Operation(o),
        }
    }
}

#[derive(Debug, Clone)]
pub struct LinearProgram<T: TypeSystemBounds> {
    pub node: LinearProgramNode<T>,
    pub args: Vec<LinearProgram<T>>,
}

impl<T: TypeSystemBounds> LinearProgram<T> {
    pub fn new(node: LinearProgramNode<T>, args: Vec<LinearProgram<T>>) -> Self {
        Self { node, args }
    }

    pub fn contains_variable(&self) -> bool {
        match self.node {
            LinearProgramNode::Variable(_) => true,
            LinearProgramNode::Constant(_) => false,
            LinearProgramNode::Operation(_) => self.args.iter().any(|a| a.contains_variable()),
        }
    }

    pub fn contains_named_variable(&self, name: &str) -> bool {
        match &self.node {
            LinearProgramNode::Variable(v) => v.name == name,
            LinearProgramNode::Constant(_) => false,
            LinearProgramNode::Operation(_) => {
                self.args.iter().any(|a| a.contains_named_variable(name))
            }
        }
    }

    pub fn interpret(&self, e: &Environment<T>) -> Result<Constant, InvalidProg> {
        let LinearProgram { node, args } = self;
        Ok(match node {
            LinearProgramNode::Constant(c) => c.clone(),
            LinearProgramNode::Variable(v) => e.get(v).unwrap().clone(),
            LinearProgramNode::Operation(o) => {
                let args = args.iter().map(|a| a.interpret(e)).try_collect()?;
                o.execute(&args)?
            }
        })
    }

    pub fn get_behavior(&self, tests: &[TestCase]) -> Vec<TestCase> {
        tests
            .iter()
            .filter_map(|t| {
                self.interpret(&t.into()).ok().map(|output| TestCase {
                    inputs: t.inputs.clone(),
                    output,
                })
            })
            .collect()
    }

    pub fn get_behavior_ex(&self, ex: &Examples) -> Examples {
        Examples::new(
            self.get_behavior(ex.get_positive_examples()),
            if ex.get_negative_examples().is_empty() {
                vec![]
            } else {
                self.get_behavior(ex.get_negative_examples())
            },
        )
    }

    pub fn get_type(&self) -> T {
        match &self.node {
            LinearProgramNode::Constant(c) => c.clone().into(),
            LinearProgramNode::Variable(v) => v.ty.clone(),
            LinearProgramNode::Operation(o) => o.sig.output.clone(),
        }
    }
}

impl<T: TypeSystemBounds> Display for LinearProgram<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", Program::from(self.clone()))
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum ProgramNode<T: TypeSystemBounds> {
    Constant(Constant),
    Variable(Variable<T>),
    Operation(Operation<T>),
    If,
    Rec(T), // Recursive Call
}

impl<T: TypeSystemBounds> Display for ProgramNode<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ProgramNode::Constant(c) => write!(f, "{c}"),
            ProgramNode::Variable(v) => write!(f, "{v}"),
            ProgramNode::Operation(o) => write!(f, "{}", o),
            ProgramNode::If => write!(f, "if"),
            ProgramNode::Rec(t) => write!(f, "rec<{t}>"),
        }
    }
}

/// A sketch is a program that can contain holes in it
/// Each hole has a corresponding type it is trying to fill
#[derive(Debug, Clone /* , PartialEq, Eq */)]
pub enum Sketch<T: TypeSystemBounds> {
    Hole(T),
    Constant(Constant),
    Variable(Variable<T>),
    Operation(Operation<T>, Vec<Sketch<T>>),
    If(Box<Program<T>>, Box<Sketch<T>>, Box<Sketch<T>>),
    Rec(T, Vec<Sketch<T>>),
}

impl From<&Sketch<BaseType>> for BaseType {
    fn from(s: &Sketch<BaseType>) -> Self {
        match s {
            Sketch::Hole(t) => *t,
            Sketch::Constant(c) => c.clone().into(),
            Sketch::Variable(v) => v.ty,
            Sketch::Operation(o, _) => o.sig.output,
            Sketch::If(_, t1, t2) => {
                let t: BaseType = (&**t1).into();
                assert!(t == (&**t2).into());
                t
            }
            Sketch::Rec(t, _) => *t,
        }
    }
}

impl<T: TypeSystemBounds> TryFrom<&Sketch<T>> for ProgramNode<T> {
    type Error = ();

    fn try_from(value: &Sketch<T>) -> Result<Self, Self::Error> {
        match value {
            Sketch::Hole(_) => Err(()),
            Sketch::Constant(c) => Ok(ProgramNode::Constant(c.clone())),
            Sketch::Variable(v) => Ok(ProgramNode::Variable(v.clone())),
            Sketch::Operation(o, ..) => Ok(ProgramNode::Operation(o.clone())),
            Sketch::If(..) => Ok(ProgramNode::If),
            Sketch::Rec(..) => Err(()),
        }
    }
}

impl From<&Sketch<RefinementType>> for RefinementType {
    fn from(s: &Sketch<RefinementType>) -> Self {
        match s {
            Sketch::Hole(t) => t.clone(),
            Sketch::Constant(c) => c.clone().into(),
            Sketch::Variable(v) => v.ty.clone(),
            Sketch::Operation(o, _) => o.sig.output.clone(),
            Sketch::If(_, t1, t2) => {
                let t: RefinementType = (&**t1).into();
                assert!(t == (&**t2).into());
                t
            }
            Sketch::Rec(t, _) => t.clone(),
        }
    }
}

impl<T: TypeSystemBounds> From<Program<T>> for Sketch<T> {
    fn from(Program { node, args }: Program<T>) -> Self {
        match node {
            ProgramNode::Constant(c) => Self::Constant(c),
            ProgramNode::Variable(v) => Sketch::Variable(v),
            ProgramNode::Operation(o) => {
                Self::Operation(o, args.into_iter().map(Self::from).collect_vec())
            }
            ProgramNode::Rec(t) => Self::Rec(t, args.into_iter().map(Self::from).collect_vec()),
            ProgramNode::If => {
                assert!(args.len() == 3);
                Self::If(
                    Box::new(args[0].clone()),
                    Box::new(args[1].clone().into()),
                    Box::new(args[2].clone().into()),
                )
            }
        }
    }
}

impl<T: TypeSystemBounds> From<LinearProgram<T>> for Sketch<T> {
    fn from(value: LinearProgram<T>) -> Self {
        Program::from(value).into()
    }
}

impl<T: TypeSystemBounds> TryFrom<Sketch<T>> for Program<T> {
    type Error = ();

    fn try_from(value: Sketch<T>) -> Result<Self, Self::Error> {
        match value {
            Sketch::Hole(_) => Err(()),
            Sketch::Constant(c) => Ok(Program {
                node: ProgramNode::Constant(c),
                args: Vec::new(),
            }),
            Sketch::Variable(v) => Ok(Program {
                node: ProgramNode::Variable(v),
                args: Vec::new(),
            }),
            Sketch::Operation(o, args) => Ok(Program {
                node: ProgramNode::Operation(o),
                args: args.into_iter().try_fold(Vec::new(), |mut acc, a| {
                    acc.push(a.try_into()?);
                    Ok(acc)
                })?,
            }),
            Sketch::Rec(t, args) => Ok(Program {
                node: ProgramNode::Rec(t),
                args: args.into_iter().try_fold(Vec::new(), |mut acc, a| {
                    acc.push(a.try_into()?);
                    Ok(acc)
                })?,
            }),
            Sketch::If(b, s1, s2) => Ok(Program {
                node: ProgramNode::If,
                args: vec![*b, (*s1).try_into()?, (*s2).try_into()?],
            }),
        }
    }
}

impl<T: TypeSystemBounds> Display for Sketch<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self {
            Sketch::Hole(t) => write!(f, "{{}} : {t:?}"),
            Self::Constant(c) => write!(f, "{c}"),
            Self::Variable(v) => write!(f, "{v}"),
            Self::Operation(o, args) => {
                write!(f, "{o}({})", args.iter().map(ToString::to_string).join(","))
            }
            Self::Rec(t, args) => {
                write!(
                    f,
                    "rec<{t:?}>({})",
                    args.iter().map(ToString::to_string).join(",")
                )
            }
            Self::If(cond, s1, s2) => write!(f, "if ({cond}) {{{s1}}} else {{{s2}}}"),
        }
    }
}

pub struct Environment<T: TypeSystemBounds>(HashMap<Variable<T>, Constant>);

impl<T: TypeSystemBounds> Environment<T> {
    pub fn new() -> Self {
        Environment(HashMap::new())
    }

    pub fn get(&self, v: &Variable<T>) -> Option<&Constant> {
        self.0.get(v)
    }
}

impl<T: TypeSystemBounds> Default for Environment<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: TypeSystemBounds> From<&TestCase> for Environment<T> {
    fn from(TestCase { inputs, .. }: &TestCase) -> Self {
        Environment(
            inputs
                .iter()
                .enumerate()
                .map(|(i, c)| {
                    (
                        Variable {
                            name: format!("arg{i:?}"),
                            ty: Into::<T>::into(c.clone()),
                        },
                        c.clone(),
                    )
                })
                .collect(),
        )
    }
}

impl<T: TypeSystemBounds> From<TestCase> for Environment<T> {
    fn from(TestCase { inputs, .. }: TestCase) -> Self {
        Environment(
            inputs
                .into_iter()
                .enumerate()
                .map(|(i, c)| {
                    (
                        Variable {
                            name: format!("arg{i:?}"),
                            ty: Into::<T>::into(c.clone()),
                        },
                        c.clone(),
                    )
                })
                .collect(),
        )
    }
}

use std::borrow::Borrow;

impl<T: TypeSystemBounds, R: Borrow<Constant>> From<&Vec<R>> for Environment<T> {
    fn from(inputs: &Vec<R>) -> Self {
        Environment(
            inputs
                .iter()
                .enumerate()
                .map(|(i, c)| {
                    (
                        Variable {
                            name: format!("arg{i:?}"),
                            ty: Into::<T>::into(c.borrow().clone()),
                        },
                        c.borrow().clone(),
                    )
                })
                .collect(),
        )
    }
}

impl<T: TypeSystemBounds> From<Vec<Constant>> for Environment<T> {
    fn from(inputs: Vec<Constant>) -> Self {
        Environment(
            inputs
                .into_iter()
                .enumerate()
                .map(|(i, c)| {
                    (
                        Variable {
                            name: format!("arg{i:?}"),
                            ty: Into::<T>::into(c.clone()),
                        },
                        c,
                    )
                })
                .collect(),
        )
    }
}

#[derive(Debug)]
pub struct InvalidProg {}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Program<T: TypeSystemBounds> {
    pub node: ProgramNode<T>,
    pub args: Vec<Program<T>>,
}

impl<T: TypeSystemBounds> Program<T> {
    pub fn new(node: ProgramNode<T>, args: Vec<Program<T>>) -> Self {
        Program { node, args }
    }

    pub fn interpret(
        &self,
        e: &Environment<T>,
        full_program: &Self,
        last_rec_arg: &Option<Constant>,
    ) -> Result<Constant, InvalidProg> {
        let Program { node, args } = self;
        Ok(match node {
            ProgramNode::Constant(c) => c.clone(),
            ProgramNode::Variable(v) => e.get(v).unwrap().clone(),
            ProgramNode::Operation(o) => {
                let args = args
                    .iter()
                    .map(|a| a.interpret(e, full_program, last_rec_arg))
                    .try_collect()?;
                o.execute(&args)?
            }
            ProgramNode::Rec(_) => {
                let args: Vec<Constant> = args
                    .iter()
                    .map(|a| a.interpret(e, full_program, last_rec_arg))
                    .try_collect()?;

                if let Some(rec_arg) = &last_rec_arg {
                    if &args[0] >= rec_arg {
                        return Err(InvalidProg {});
                    }
                }

                let last_rec_arg = Some(args[0].clone());

                let new_e = &(&args).into();

                full_program.interpret(new_e, full_program, &last_rec_arg)?
            }
            ProgramNode::If => {
                if args
                    .get(0)
                    .unwrap()
                    .interpret(e, full_program, last_rec_arg)?
                    == Constant::Bool(true)
                {
                    args.get(1)
                        .unwrap()
                        .interpret(e, full_program, last_rec_arg)?
                } else {
                    args.get(2)
                        .unwrap()
                        .interpret(e, full_program, last_rec_arg)?
                }
            }
        })
    }

    pub fn get_behavior(&self, tests: &[TestCase]) -> Vec<TestCase> {
        tests
            .iter()
            .filter_map(|t| {
                self.interpret(&t.into(), self, &None)
                    .ok()
                    .map(|output| TestCase {
                        inputs: t.inputs.clone(),
                        output,
                    })
            })
            .collect()
    }

    pub fn get_type(&self) -> T {
        match &self.node {
            ProgramNode::Constant(c) => c.clone().into(),
            ProgramNode::Variable(v) => v.ty.clone(),
            ProgramNode::Operation(o) => o.sig.output.clone(),
            ProgramNode::If => self.args.get(1).unwrap().get_type(),
            ProgramNode::Rec(t) => t.clone(),
        }
    }

    pub fn size(&self) -> usize {
        1 + self.args.iter().map(|a| a.size()).sum::<usize>()
    }

    pub fn substitute(&self, env: &HashMap<String, LinearProgram<T>>) -> Self {
        match self {
            Program {
                node: ProgramNode::Variable(v),
                ..
            } if env.get(&v.name).is_some() => env.get(&v.name).unwrap().clone().into(),
            Program { node, args } => Program {
                node: node.clone(),
                args: args.iter().map(|a| a.substitute(env)).collect(),
            },
        }
    }
}

impl<T: TypeSystemBounds> From<Constant> for Program<T> {
    fn from(value: Constant) -> Self {
        Program {
            node: ProgramNode::Constant(value),
            args: vec![],
        }
    }
}

impl<T: TypeSystemBounds> From<Variable<T>> for Program<T> {
    fn from(value: Variable<T>) -> Self {
        Program {
            node: ProgramNode::Variable(value),
            args: vec![],
        }
    }
}

impl<T: TypeSystemBounds> From<LinearProgram<T>> for Program<T> {
    fn from(LinearProgram { node, args }: LinearProgram<T>) -> Self {
        Program {
            node: node.into(),
            args: args.into_iter().map(|a| a.into()).collect(),
        }
    }
}

impl<T: TypeSystemBounds> TryFrom<Program<T>> for LinearProgram<T> {
    type Error = ();

    fn try_from(Program { node, args }: Program<T>) -> Result<Self, Self::Error> {
        Ok(LinearProgram {
            node: node.try_into()?,
            args: args.into_iter().map(|a| a.try_into()).try_collect()?,
        })
    }
}

impl<T: TypeSystemBounds> Display for Program<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.node {
            ProgramNode::Constant(c) => write!(f, "{c}"),
            ProgramNode::Variable(v) => write!(f, "{v}"),
            ProgramNode::Operation(o) => write!(
                f,
                "{o}({})",
                self.args.iter().map(ToString::to_string).join(",")
            ),
            ProgramNode::Rec(t) => write!(
                f,
                "rec<{t}>({})",
                self.args.iter().map(ToString::to_string).join(",")
            ),
            ProgramNode::If => write!(
                f,
                "if ({}) {{{}}} else {{{}}}",
                self.args.get(0).unwrap(),
                self.args.get(1).unwrap(),
                self.args.get(2).unwrap()
            ),
        }
    }
}
