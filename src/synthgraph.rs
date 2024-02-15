// Have a Graph of I/O example relations
// I want to be able to walk from an I/O Relation to other versions depending on the direction I am trying to fill.

// Do I? or do I just add widening edges to all of the cases I care about?

// For a given type, I want to find all of the ID's of Eclasses of that type
// So that's a map from Types to ID's

// The Egraph has a mapping from ID's to Eclasses which contain data(That is the I/O Relation)

// Have a reference counted queue of Eclasses representing holes.
// Reference counting keeps holes alive if they still are waited on
// Allows an ordering of the references
// Allows holes to be dropped if they are not in use anymore

use itertools::Itertools;
use std::collections::hash_map::Entry;
use std::collections::{HashMap, HashSet};
use std::fmt::Display;
use std::fs::File;
use std::hash::Hash;
use std::mem::swap;
use std::num::NonZeroU8;
use std::ops::Index;
use std::str::FromStr;
use std::vec;
use tracing::{info, span, warn, Level};

use crate::language::{
    BaseType, Constant, Environment, Examples, LinearProgram, LinearProgramNode, Operation,
    Program, ProgramNode, RefinementType, Signature, Sketch, TestCase, TypeSystemBounds, Variable,
};

use egg::{define_language, Analysis, EGraph, Id};

use crate::data_structures::{IOExampleHashing, InverseMap, MinHeap};
use crate::sketch::{SynthesisInfo, SynthesisSketch};
use crate::{Libraries, OP_LIST};

const MAXIFDEPTH: u8 = 2;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct EggConstantData(ExampleHash, Constant);

impl Display for EggConstantData {
    fn fmt(&self, _f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        todo!()
    }
}

impl FromStr for EggConstantData {
    type Err = ();

    fn from_str(_s: &str) -> Result<Self, Self::Err> {
        todo!()
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct EggVariableData<T: TypeSystemBounds>(ExampleHash, Variable<T>);

impl<T: TypeSystemBounds> Display for EggVariableData<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} {}", self.0, self.1)
    }
}

impl<T: TypeSystemBounds> FromStr for EggVariableData<T> {
    type Err = ();

    fn from_str(_s: &str) -> Result<Self, Self::Err> {
        todo!()
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct EggOpData(ExampleHash, OpMapIndex);

impl Display for EggOpData {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} {}", self.0, self.1)
    }
}

impl FromStr for EggOpData {
    type Err = ();

    fn from_str(_s: &str) -> Result<Self, Self::Err> {
        todo!()
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct EggRecData(ExampleHash, BaseType);

impl Display for EggRecData {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} #rec", self.0)
    }
}

impl FromStr for EggRecData {
    type Err = ();

    fn from_str(_s: &str) -> Result<Self, Self::Err> {
        todo!()
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct EggIfData(ExampleHash);
impl Display for EggIfData {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} #if", self.0)
    }
}

impl FromStr for EggIfData {
    type Err = ();

    fn from_str(_s: &str) -> Result<Self, Self::Err> {
        todo!()
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct EggHoleData(ExampleHash);
impl Display for EggHoleData {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} #{{}}", self.0)
    }
}

impl FromStr for EggHoleData {
    type Err = ();

    fn from_str(_s: &str) -> Result<Self, Self::Err> {
        todo!()
    }
}

define_language! {
    pub enum ArwenLang {
        Hole(EggHoleData),
        Constant(EggConstantData),
        Var(EggVariableData<BaseType>),
        If(EggIfData, [Id; 3]),
        Op(EggOpData, Vec<Id>),
        Rec(EggRecData, Vec<Id>),
        Widen(ExampleHash, Id),
    }
}

impl ArwenLang {
    pub fn is_hole(&self) -> bool {
        matches!(self, ArwenLang::Hole(_))
    }

    pub fn is_rec(&self) -> bool {
        matches!(self, ArwenLang::Rec(_, _))
    }

    pub fn get_hash(&self) -> ExampleHash {
        match self {
            ArwenLang::Hole(h) => h.0,
            ArwenLang::Constant(EggConstantData(h, _)) => *h,
            ArwenLang::Var(EggVariableData(h, _)) => *h,
            ArwenLang::If(h, _) => h.0,
            ArwenLang::Op(EggOpData(h, _), _) => *h,
            ArwenLang::Rec(EggRecData(h, _), _) => *h,
            ArwenLang::Widen(h, _) => *h,
        }
    }
}

// A helper function for recursive calls to check for the arg0 variable
pub fn contains_arg0(id: &Id, egg: &EGraph<ArwenLang, ArwenAnalysis>) -> bool {
    egg[*id].nodes.iter().any(|n| match n {
        ArwenLang::Hole(_) => false,
        ArwenLang::Constant(_) => false,
        ArwenLang::Var(v) => v.1.name == "arg0",
        ArwenLang::If(_, [_, t, f]) => contains_arg0(t, egg) || contains_arg0(f, egg),
        ArwenLang::Op(_, args) => args.iter().any(|a| contains_arg0(a, egg)),
        ArwenLang::Rec(_, _) => false,
        ArwenLang::Widen(_, wid) => contains_arg0(wid, egg),
    })
}

#[derive(Debug, PartialEq, Eq, Hash, PartialOrd, Ord, Clone, Copy)]
pub struct ExampleHash(u32);

impl ExampleHash {
    pub fn new(u: u32) -> Self {
        ExampleHash(u)
    }
}

impl Display for ExampleHash {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl FromStr for ExampleHash {
    type Err = ();

    fn from_str(_s: &str) -> Result<Self, Self::Err> {
        todo!()
    }
}

pub struct ArwenAnalysis {}

impl Analysis<ArwenLang> for ArwenAnalysis {
    type Data = ExampleHash;

    fn make(_egraph: &EGraph<ArwenLang, Self>, enode: &ArwenLang) -> Self::Data {
        enode.get_hash()
    }

    fn merge(&mut self, a: &mut Self::Data, b: Self::Data) -> egg::DidMerge {
        if a == &b {
            egg::DidMerge(true, true)
        } else {
            panic!()
        }
    }
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct OpMapIndex(u32);

impl Display for OpMapIndex {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "#{}",
            OP_LIST.lock().unwrap().get(self.0 as usize).unwrap()
        )
    }
}

pub struct OpMap<T> {
    map: HashMap<String, OpMapIndex>,
    pub arr: Vec<Operation<T>>,
}

impl<T: std::clone::Clone> Default for OpMap<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: std::clone::Clone> OpMap<T> {
    pub fn new() -> Self {
        OpMap {
            map: HashMap::new(),
            arr: Vec::new(),
        }
    }

    pub fn get_idx(&mut self, o: &Operation<T>) -> OpMapIndex {
        if let Some(x) = self.map.get(&o.name) {
            return *x;
        }

        let ret = OpMapIndex(self.arr.len() as u32);
        self.map.insert(o.name.clone(), ret);
        self.arr.push(o.clone());
        ret
    }

    pub fn get(&self, o: &OpMapIndex) -> &Operation<T> {
        &self.arr[o.0 as usize]
    }
}

#[derive(Clone)]
pub struct FancyTypeMap {
    map: HashMap<BaseType, HashSet<Id>>,
}

impl Default for FancyTypeMap {
    fn default() -> Self {
        Self::new()
    }
}

impl FancyTypeMap {
    pub fn new() -> Self {
        FancyTypeMap {
            map: HashMap::new(),
        }
    }

    pub fn insert(&mut self, egg: &EGraph<ArwenLang, ArwenAnalysis>, ty: BaseType, id: Id) {
        let set = self.map.entry(ty).or_default();
        let current_id_hash = egg[id].data;
        if !set
            .iter()
            .any(|included_id| current_id_hash == egg[*included_id].data)
        {
            set.insert(id);
        }
    }

    pub fn get(&self, ty: &BaseType) -> Option<&HashSet<Id>> {
        self.map.get(ty)
    }
}

#[derive(Debug, Clone)]
enum StartingValues<T: TypeSystemBounds> {
    Var(Variable<T>),
    Op(OpMapIndex, T),
}

impl StartingValues<BaseType> {
    pub fn into_arwenlang(&self, h: ExampleHash) -> ArwenLang {
        match self {
            StartingValues::Var(v) => ArwenLang::Var(EggVariableData(h, v.clone())),
            StartingValues::Op(s, _) => ArwenLang::Op(EggOpData(h, *s), vec![]),
        }
    }
}

impl From<StartingValues<BaseType>> for BaseType {
    fn from(value: StartingValues<BaseType>) -> Self {
        match value {
            StartingValues::Var(v) => v.ty,
            StartingValues::Op(_, ty) => ty,
        }
    }
}
/*
fn extraction_node_ordering(a: &ArwenLang, b: &ArwenLang) -> Ordering {
    match (a, b) {
        // Handle Equality Ordering
        // I think in this usage a lot of these will be equal?
        (ArwenLang::Hole(_), ArwenLang::Hole(_))
        | (ArwenLang::Constant(_), ArwenLang::Constant(_))
        | (ArwenLang::Var(_), ArwenLang::Var(_))
        | (ArwenLang::Op(_, _), ArwenLang::Op(_, _))
        | (ArwenLang::If(_, _), ArwenLang::If(_, _))
        | (ArwenLang::Rec(_, _), ArwenLang::Rec(_, _))
        | (ArwenLang::Widen(_, _), ArwenLang::Widen(_, _)) => Ordering::Equal,

        // Holes have the least priority because they will require speculation
        (ArwenLang::Hole(_), _) => Ordering::Greater,
        (_, ArwenLang::Hole(_)) => Ordering::Less,

        // Vars have the highest priority because they are simple, but more general than constants
        (ArwenLang::Var(_), _) => Ordering::Less,
        (_, ArwenLang::Var(_)) => Ordering::Greater,

        // Constants don't have any children so lets do them next
        (ArwenLang::Constant(_), _) => Ordering::Less,
        (_, ArwenLang::Constant(_)) => Ordering::Greater,

        // Ops are then the next least costed because they help us make progress in the synthesis problem
        (ArwenLang::Op(_, _), _) => Ordering::Less,
        (_, ArwenLang::Op(_, _)) => Ordering::Greater,

        // Kinda bringing up the rear are the if's
        (ArwenLang::If(_, _), _) => Ordering::Less,
        (_, ArwenLang::If(_, _)) => Ordering::Greater,

        (ArwenLang::Rec(_, _), _) => Ordering::Less,
        (_, ArwenLang::Rec(_, _)) => Ordering::Greater,
        // Widen is at the end since it opens up a new section
        // Maybe I could think about collapsing all of the widen candidates together into one list
        // But we also don't have anything here since all the cases are handled above
    }
}
 */
/* fn pull_from_graph(
    solution_graph: &DiGraph<ProgramNodeWithHole, ()>,
    root_node: NodeIndex,
) -> Program<BaseType> {
    match solution_graph.node_weight(root_node).unwrap() {
        ProgramNodeWithHole::ProgramNode(c @ ProgramNode::Constant(_)) => Program {
            node: c.clone(),
            args: vec![],
        },
        ProgramNodeWithHole::ProgramNode(v @ ProgramNode::Variable(_)) => Program {
            node: v.clone(),
            args: vec![],
        },
        ProgramNodeWithHole::ProgramNode(o @ ProgramNode::Operation(_)) => {
            let args = solution_graph
                .neighbors_directed(root_node, petgraph::Direction::Outgoing)
                .map(|n| pull_from_graph(solution_graph, n))
                .collect_vec();
            Program {
                node: o.clone(),
                args,
            }
        }
        ProgramNodeWithHole::ProgramNode(ProgramNode::If) => {
            let args = solution_graph
                .neighbors_directed(root_node, petgraph::Direction::Outgoing)
                .map(|n| pull_from_graph(solution_graph, n))
                .collect_vec();
            Program {
                node: ProgramNode::If,
                args,
            }
        }
        ProgramNodeWithHole::ProgramNode(ProgramNode::Rec(t)) => {
            let args = solution_graph
                .neighbors_directed(root_node, petgraph::Direction::Outgoing)
                .map(|n| pull_from_graph(solution_graph, n))
                .collect_vec();
            Program {
                node: ProgramNode::Rec(t.clone()),
                args,
            }
        }
        ProgramNodeWithHole::Hole => unreachable!(),
    }
}
 */

#[derive(Debug)]
enum PropResult {
    Success,
    Failure,
}

impl PropResult {
    pub fn is_success(&self) -> bool {
        matches!(self, PropResult::Success)
    }

    pub fn success(&self) -> Option<()> {
        match self {
            PropResult::Success => Some(()),
            PropResult::Failure => None,
        }
    }
}

impl Display for PropResult {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PropResult::Success => write!(f, "PropSuccess"),
            PropResult::Failure => write!(f, "PropFailure"),
        }
    }
}

pub struct SynthesisGraph {
    pub egg: EGraph<ArwenLang, ArwenAnalysis>, // The egraph that is being build up
    pub size: NonZeroU8, // How many iterations have been done/how large are the biggest fragments
    pub classes_added_in_last_iteration: HashSet<Id>,
    pub example_map: IOExampleHashing, // Map that keeps track of examples to their corresponding Hashes
    pub id_lookup: HashMap<ExampleHash, Id>, // The map that ties together examples and e-classes
    type_map: FancyTypeMap, // Maps types to egraph Ids to use as arguments in the next iteration
    pub inverse_mapping: InverseMap<BaseType>, // The inverse mapping that we will be building up
    pub op_lookup: OpMap<BaseType>,
    pub sig: Signature<BaseType>,
}

impl SynthesisGraph {
    pub fn new(
        io_examples: &Examples,
        variables: Vec<Variable<BaseType>>,
        components: &Libraries<BaseType>,
        sig: Signature<BaseType>,
    ) -> Self {
        let mut egg = EGraph::new(ArwenAnalysis {});
        let mut op_lookup = OpMap::new();

        let behaviors = variables
            .into_iter()
            .map(|v| {
                let node = LinearProgramNode::Variable(v.clone());
                (
                    StartingValues::Var(v),
                    LinearProgram { node, args: vec![] }.get_behavior_ex(io_examples),
                )
            })
            .chain(components.iter().filter_map(
                |o @ Operation {
                     sig: Signature { input, output },
                     ..
                 }| {
                    if !input.is_empty() {
                        None
                    } else {
                        let fragment = LinearProgram {
                            node: LinearProgramNode::Operation(o.clone()),
                            args: Vec::new(),
                        };

                        let behavior = fragment.get_behavior_ex(io_examples);

                        Some((StartingValues::Op(op_lookup.get_idx(o), *output), behavior))
                    }
                },
            ));

        let mut example_map = IOExampleHashing::new();

        let x: Vec<(_, BaseType, _)> = behaviors
            .into_iter()
            .map(|(v, ex)| {
                assert!(!ex.is_empty());
                (v.clone(), v.into(), example_map.insert(&ex))
            })
            .collect_vec();

        let mut type_map = FancyTypeMap::new();
        let mut id_lookup = HashMap::new();
        let mut classes_added_in_last_iteration = HashSet::new();

        x.into_iter().for_each(|(v, ty, h)| {
            let id = egg.add(v.into_arwenlang(h));
            type_map.insert(&egg, ty, id);
            id_lookup.insert(h, id).map(|id2| {
                assert!(egg.union(id, id2));
                Some(())
            });
            classes_added_in_last_iteration.insert(id);
        });

        Self {
            egg,
            size: NonZeroU8::new(1).unwrap(),
            classes_added_in_last_iteration,
            example_map,
            id_lookup,
            type_map,
            inverse_mapping: InverseMap::empty(io_examples),
            op_lookup,
            sig,
        }
    }

    fn op_lookup(&self, o: &OpMapIndex) -> &Operation<BaseType> {
        self.op_lookup.get(o)
    }

    // todo a specific version of this for recursive calls
    pub fn fuzz_spec(
        &self,
        p: &Program<BaseType>,
        spec: &Signature<RefinementType>,
    ) -> Option<TestCase> {
        let constant_map = self.inverse_mapping.get_all_constants();

        dbg!(&spec);

        spec.input
            .iter()
            .map(|t| constant_map.get(TypeSystemBounds::into(t)).unwrap())
            .multi_cartesian_product()
            .filter(|args| spec.check_input_spec(args))
            .find_map(|args| {
                if let Ok(output) = p.interpret(&Environment::from(&args.clone()), p, &None) {
                    if !spec.check_output_spec(&args, &output) {
                        Some(TestCase {
                            inputs: args.into_iter().cloned().collect_vec(),
                            output,
                        })
                    } else {
                        None
                    }
                } else {
                    None
                }
            })
    }

    /// Something about adding an operation to the egraph
    /// Should maintain all the invariants that I'm trying to keep track of
    pub fn add_fragment(&mut self, o: &Operation<BaseType>, args: Vec<Id>) {
        assert!(args.len() == o.sig.input.len());

        let mut hashes = args.iter().map(|a| self.egg[*a].data);

        // Each of the Id's can be mapped back to examples
        let x = hashes
            .clone()
            .map(|e_hash| self.example_map.get_examples(e_hash))
            .collect_vec();

        assert!(x.len() == o.sig.input.len());

        // A list of pairs
        // The initial environment inputs
        // and the current inputs to the operation
        let intersected_input_example_set: (
            HashMap<Vec<Constant>, Vec<Constant>>,
            HashMap<Vec<Constant>, Vec<Constant>>,
        ) = x
            .into_iter()
            .fold((HashMap::new(), HashMap::new()), |mut acc, e| {
                e.get_positive_examples().iter().for_each(|t| {
                    let entry = acc.0.entry(t.inputs.clone()).or_default();
                    entry.push(t.output.clone());
                });
                e.get_negative_examples().iter().for_each(|t| {
                    let entry = acc.1.entry(t.inputs.clone()).or_default();
                    entry.push(t.output.clone());
                });
                acc
            });

        let filter_len = |s: HashMap<_, Vec<_>>| {
            s.into_iter()
                .filter(|(_, v)| v.len() == o.sig.input.len())
                .collect_vec()
        };

        let intersected_input_example_set = (
            filter_len(intersected_input_example_set.0),
            filter_len(intersected_input_example_set.1),
        );

        let mut convert_to_testcase_vec = |v: Vec<(_, _)>| {
            v.into_iter()
                .filter_map(|(inputs, args)| {
                    Some(TestCase {
                        inputs,
                        output: self.inverse_mapping.add(o.clone(), &args)?.output.clone(),
                    })
                })
                .collect_vec()
        };

        // Given the list of inputs, convert those into testcases
        // Add the new mapping to the inverse mapping for this operation
        let intersected_input_testcases: Examples = Examples::new(
            convert_to_testcase_vec(intersected_input_example_set.0),
            convert_to_testcase_vec(intersected_input_example_set.1),
        );

        if intersected_input_testcases.is_empty() {
            // Bail out
            return;
        }

        assert!(!intersected_input_testcases.is_empty());

        // get example hash
        let hash = self.example_map.insert(&intersected_input_testcases);

        if hashes.contains(&hash) {
            //eprintln!("Circular dep");
            return;
        }

        // Look up the associated EClass
        // Check if this new potential node is already in the EClass
        // Ignore it if it already exists
        if self.id_lookup.contains_key(&hash) {
            eprintln!("Already exists");
            eprintln!("This should be fixed by limiting the choosing of operations later to one representative, not pruning the egraph");
            return;
        }

        // If it doesn't exist, add it to the EClass and add the node to the previously_added list adn the type map
        let entry = self.id_lookup.entry(hash);

        // Build the new enode
        let new_enode = ArwenLang::Op(EggOpData(hash, self.op_lookup.get_idx(o)), args.clone());

        // Add it to the graph, it may already be there in the right eclass or it is in its own eclass
        let id = self.egg.add(new_enode);

        match entry {
            Entry::Vacant(v) => {
                v.insert(id);
                self.type_map.insert(&self.egg, o.sig.output, id);
                self.classes_added_in_last_iteration.insert(id);
            }
            Entry::Occupied(oc) => {
                panic!();
                let eclass_id = oc.get();
                if self.egg.union(*eclass_id, id) {
                    // This is a new node that has been added to the eclass
                    self.classes_added_in_last_iteration.insert(id);
                    self.type_map.insert(&self.egg, o.sig.output, id);
                } else {
                    // This already exists in the eclass so we are done
                }
            }
        }
    }

    pub fn update_inverse_map(&mut self) {
        self.inverse_mapping.update_mappings_with_new_constants();
    }

    pub fn increment(&mut self, components: &Libraries<BaseType>) {
        self.size = self.size.checked_add(1).unwrap();

        let mut previously_added = HashSet::new();

        // Now self has a new empty list of classes as no new classes have been added in this iteration
        // `previously_added` now contains all the old classes that will be iterated over.
        swap(
            &mut self.classes_added_in_last_iteration,
            &mut previously_added,
        );

        // Because the type map gets updated during iteration
        let map_copy = self.type_map.clone();
        let example_map_copy = self.example_map.clone();

        // Iterate through each of the components and construct new possible programs to add to the graph.
        components.iter().for_each(|o| {
            let possible_args: Vec<_> = (0..o.sig.input.len())
                .flat_map(|idx| {
                    o.sig
                        .input
                        .iter()
                        .enumerate()
                        .map(|(i, ty)| {
                            if i == idx {
                                previously_added
                                    .iter()
                                    .filter(|id| {
                                        *ty == example_map_copy
                                            .get_examples(self.egg[**id].data)
                                            .get_positive_examples()[0]
                                            .output
                                            .clone()
                                            .into()
                                    })
                                    .cloned()
                                    .collect_vec()
                                    .into_iter()
                            } else {
                                map_copy
                                    .get(ty)
                                    .cloned()
                                    .unwrap_or_default()
                                    .into_iter()
                                    .collect_vec()
                                    .into_iter()
                            }
                        })
                        .multi_cartesian_product()
                        .collect_vec()
                })
                .collect();

            /*             dbg!(&o);
            dbg!(&possible_args); */

            // Some common way to add a new fragment to the graph and update all the corresponding things
            // Also want it to be in the "previously added part" so that it can be used in the next iteration
            possible_args.into_iter().for_each(|a| {
                println!(
                    "{}: {}",
                    o.name,
                    a.iter().map(ToString::to_string).join(",")
                );
                self.add_fragment(o, a)
            });
        });
    }

    fn id_exists_or_hole(&mut self, hash: ExampleHash) -> Id {
        self.id_lookup.get(&hash).cloned().unwrap_or_else(|| {
            let id = self.egg.add(ArwenLang::Hole(EggHoleData(hash)));
            self.id_lookup.insert(hash, id);
            id
        })
    }

    pub fn generate_recursive_calls(&mut self, rec_sig: &Signature<BaseType>) -> Id {
        let possible_args: Vec<_> = rec_sig
            .input
            .iter()
            .enumerate()
            .map(|(i, ty)| {
                let arg_i_iter = self
                    .type_map
                    .get(ty)
                    .cloned()
                    .unwrap_or_default()
                    .into_iter()
                    .collect_vec();

                // If we are the first argument, we need to make sure the value is observably smaller
                if i == 0 {
                    arg_i_iter
                        .into_iter()
                        .filter(|a_id| contains_arg0(a_id, &self.egg))
                        .filter(|a_id| {
                            self.example_map
                                .get_examples(self.egg[*a_id].data)
                                .is_observably_smaller()
                        })
                        .collect_vec()
                        .into_iter()
                } else {
                    arg_i_iter.into_iter()
                }
            })
            .multi_cartesian_product()
            .collect_vec();

        if possible_args.is_empty() {
            panic!();
        }

        /*         let possible_args: Vec<_> = (0..rec_sig.input.len())
        .flat_map(|idx| {
            rec_sig
                .input
                .iter()
                .enumerate()
                .map(|(i, ty)| {
                    let arg_i_iter = self
                        .type_map
                        .get(ty)
                        .cloned()
                        .unwrap_or_default()
                        .into_iter() // And then we need to make sure that the argument is defined on all of the subsequent calls(Atleast the ones the programmer has told us about)
                        .filter(|a_id| {
                            let a = self.example_map.get_examples(self.egg[*a_id].data);
                            positive_examples.iter().all(|e| {
                                a.get_positive_examples()
                                    .iter()
                                    .any(|c| c.output == e.inputs[i])
                            })
                        });

                    // If we are the first argument, we need to make sure the value is observably smaller
                    if i == 0 {
                        arg_i_iter
                            .filter(|a_id| {
                                self.example_map
                                    .get_examples(self.egg[*a_id].data)
                                    .is_observably_smaller()
                            })
                            .collect_vec()
                            .into_iter()
                    } else {
                        arg_i_iter.collect_vec().into_iter()
                    }
                })
                .multi_cartesian_product()
                .collect_vec()
        })
        .collect(); */

        let rec_data = EggRecData(
            self.example_map
                ./* insert(&Examples::new(positive_examples, vec![])) */get_rec_hash(),
            rec_sig.output,
        );

        // We don't want the special rec node accidentally referenced
        /* self.id_lookup.insert(rec_data.0, rec_id); */
        possible_args
            .into_iter()
            .map(|args| self.egg.add(ArwenLang::Rec(rec_data.clone(), args)))
            .collect_vec() // add all the nodes first which does the mutation, then union the Id's later
            .into_iter()
            .reduce(|acc, e| {
                self.egg.union(acc, e);
                self.egg.find(acc)
            })
            .unwrap()
    }

    pub fn top_down_prop(&mut self, hole: &Examples, rec_id: Id) {
        info!("Doing top down prop");
        let hash = self.example_map.insert(hole);

        let id = self.id_exists_or_hole(hash);

        let mut queue = MinHeap::new();
        queue.push(SynthesisSketch::init(id));

        let mut count = 0;

        while let Some(progress) = queue.pop() {
            let x = self.fill_progress(progress, rec_id);
            for new_progress_work in x {
                if new_progress_work.no_more_work() {
                    count += 1;
                    if count > 4 {
                        info!("We are done with top_down propagation");
                        /* self.dump_all_programs(); */
                        crate::update_global_oplist(&self.op_lookup);
                        /*     g.egg.dot().to_dot("test.dot").unwrap(); */
                        // Else, maybe we do some processing to set up the traces we are walking along
                        if let Some(s) = self.extraction(hole) {
                            dbg!(s);
                            return;
                        }
                        count = 0
                    }
                } else {
                    queue.push(new_progress_work);
                }
            }
        }
        info!("DOne");
    }

    pub fn check_if_program_in_egraph(&self, start_id: Id, prog: Sketch<BaseType>) -> bool {
        self.egg[start_id].nodes.iter().any(|n| match (n, &prog) {
            (_, Sketch::Hole(_)) => true,
            (ArwenLang::Hole(_), _) => false,
            (ArwenLang::Constant(c1), Sketch::Constant(c2)) => c1.1 == *c2,
            (ArwenLang::Constant(_), _) => false,
            (ArwenLang::Var(v1), Sketch::Variable(v2)) => v1.1 == *v2,
            (ArwenLang::Var(_), _) => false,
            (ArwenLang::If(_, args), Sketch::If(p1, s1, s2)) => {
                self.check_if_program_in_egraph(args[0], (*p1.clone()).into())
                    && self.check_if_program_in_egraph(args[1], *s1.clone())
                    && self.check_if_program_in_egraph(args[2], *s2.clone())
            }

            (ArwenLang::If(_, _), _) => false,
            (ArwenLang::Op(o1, args1), Sketch::Operation(o2, args2)) => {
                self.op_lookup.get(&o1.1) == o2
                    && args1
                        .iter()
                        .zip(args2)
                        .all(|(a1, a2)| self.check_if_program_in_egraph(*a1, a2.clone()))
            }
            (ArwenLang::Op(_, _), _) => false,
            (ArwenLang::Rec(_, _), _) => todo!(),
            (ArwenLang::Widen(_, id), _) => self.check_if_program_in_egraph(*id, prog.clone()),
        })
    }

    fn try_widen(&mut self, id: Id) -> PropResult {
        let hash = self.egg[id].data;
        let hole = self.example_map.get_examples(hash);
        // Check to see if we can finish this with a simple widen to another eclass
        let wider_eclasses: Vec<Id> = self
            .example_map
            .wider(hole)
            .into_iter()
            .filter_map(|e| {
                let eclass = *self.id_lookup.get(&e).unwrap();
                if self
                    .egg
                    .index(eclass)
                    .nodes
                    .iter()
                    // We don't want to widen to just a hole
                    // And we don't want to skip trying to synthesize something over just a probably wrong recursive call
                    .any(|n| !n.is_hole() && !n.is_rec())
                {
                    Some(eclass)
                } else {
                    None
                }
            })
            .collect();

        if !wider_eclasses.is_empty() {
            let res = wider_eclasses
                .into_iter()
                .map(|id| self.egg.add(ArwenLang::Widen(hash, id)))
                .collect_vec();

            info!("Widen created");
            let final_id = res.into_iter().fold(id, |id1, id2| {
                self.egg.union(id1, id2);
                self.egg.find(id1)
            });
            self.id_lookup.insert(hash, final_id);
            PropResult::Success
        } else {
            PropResult::Failure
        }
    }

    fn try_op(&mut self, id: Id) -> Vec<Vec<Id>> {
        let hash = self.egg[id].data;
        let hole = self.example_map.get_examples(hash);
        // We are going to look for candidate operations from our traces
        let narrower_eclasses = self.example_map.narrower(hole);

        if narrower_eclasses.is_empty() {
            return Vec::new();
        }

        // We have a suggestion
        let mut candidate_operation = narrower_eclasses
            .into_iter()
            .flat_map(|e| {
                let id = self.id_lookup.get(&e).unwrap();
                let eclass = self.egg.index(*id);
                let enodes = &eclass.nodes;
                // We are skipping over classes with the hole node as that means it wasn't part of our traces
                if enodes.iter().any(|l| matches!(l, ArwenLang::Hole(_))) {
                    Vec::new()
                } else {
                    // Otherwise we can just grab all of our operations
                    enodes
                        .iter()
                        .filter_map(|n| match n {
                            ArwenLang::Op(EggOpData(_, o), _) => Some(o),
                            _ => None,
                        })
                        .collect()
                }
            })
            .copied()
            .collect_vec();

        // We sort and dedup to get a unique list of ops
        candidate_operation.sort();
        candidate_operation.dedup();

        // For each op
        candidate_operation
            .into_iter()
            .filter_map(|o| {
                hole.propogate_operation_examples(self.op_lookup.get(&o), &self.inverse_mapping)
                    .map(|x| (o, x))
            })
            .collect_vec()
            .into_iter()
            .flat_map(|(o, examples_vec)| {
                examples_vec
                    .into_iter()
                    .map(|examples_v| {
                        let args = examples_v
                            .into_iter()
                            .map(|e| {
                                let e_hash = self.example_map.insert(&e);

                                self.id_exists_or_hole(e_hash)
                            })
                            .collect_vec();

                        let op_id = self
                            .egg
                            .add(ArwenLang::Op(EggOpData(hash, o), args.clone()));
                        self.egg.union(id, op_id);
                        args
                    })
                    .collect_vec()
            })
            .collect_vec()
    }

    // Just return the false branch because we will try to enforce that there is a true branch
    fn try_if(&mut self, id: Id) -> Vec<Id> {
        let hash = self.egg[id].data;
        let hole = self.example_map.get_examples(hash);
        let conds = self.type_map.get(&BaseType::Bool).unwrap().clone();
        {
            // Do some kinds of uniqueness assertion
            let mut assert_stuff = conds
                .iter()
                .map(|id| {
                    self.example_map
                        .get_examples(self.egg[*id].data)
                        .get_positive_examples()
                })
                .collect_vec();
            assert_stuff.sort();
            let assert_len = assert_stuff.len();
            assert_stuff.dedup();
            assert!(assert_len == assert_stuff.len());
        }

        let res = conds
            .into_iter()
            .filter_map(|c| {
                /* if incomplete { */
                let eclass = &self.egg[c];
                let cond_examples = self.example_map.get_examples(eclass.data);
                let true_behavior = hole.filter_behavior_e(cond_examples, true);
                let false_behavior = hole.filter_behavior_e(cond_examples, false);

                let not_all_behaviours_are_accounted_for = hole.get_positive_examples().len()
                    != true_behavior.get_positive_examples().len()
                        + false_behavior.get_positive_examples().len();

                if !(true_behavior.is_empty()
                    || false_behavior.is_empty()
                    || not_all_behaviours_are_accounted_for)
                {
                    Some((c, true_behavior, false_behavior))
                } else {
                    None
                }
            })
            .collect_vec()
            .into_iter()
            .filter_map(|(c, true_behavior, false_behavior)| {
                let true_hash = self.example_map.insert(&true_behavior);
                let false_hash = self.example_map.insert(&false_behavior);
                let true_id = self.id_exists_or_hole(true_hash);
                let false_id = self.id_exists_or_hole(false_hash);

                // We want to actually just initialize the true branch if possible
                if self.egg[true_id]
                    .nodes
                    .iter()
                    .all(|n| !matches!(n, ArwenLang::Hole(_)))
                    || self.try_widen(true_id).is_success()
                {
                    let if_id = self
                        .egg
                        .add(ArwenLang::If(EggIfData(hash), [c, true_id, false_id]));
                    self.egg.union(id, if_id);
                    Some(false_id)
                } else {
                    None
                }
            })
            .collect();
        info!("Finished If");
        res
    }

    fn fill_progress(&mut self, mut progress: SynthesisSketch, rec_id: Id) -> Vec<SynthesisSketch> {
        // We know there is no cycle because work is checked when added
        let SynthesisInfo {
            id,
            if_depth,
            can_synthesize_rec,
        } = progress.get_work();

        // Condition that checks if we bottom-up enumerated this
        if self.egg[id]
            .nodes
            .iter()
            .all(|n| !matches!(n, ArwenLang::Hole(_)))
        {
            return vec![progress];
        }

        // Condition that checks that we haven't already solved this
        if !(self.egg[id].nodes.len() == 1 && self.egg[id].nodes[0].is_hole()) {
            return vec![progress];
        }

        // Check whether we can just trivially widen to solve
        if self.try_widen(id).is_success() {
            info!("Did widen");
            return vec![progress];
        }

        // Where we will store the new progress structs
        let mut new_progress = Vec::new();

        // Check for operations
        new_progress.extend(self.try_op(id).into_iter().filter_map(|args| {
            let mut new_p = progress.clone();
            new_p.add_cost_of_op(args.len());
            if new_p
                .update_worklist(
                    args.into_iter()
                        .map(|a| SynthesisInfo {
                            id: a,
                            if_depth: MAXIFDEPTH + 1,
                            can_synthesize_rec,
                        })
                        .collect(),
                )
                .is_ok()
            {
                Some(new_p)
            } else {
                None
            }
        }));

        // Check for if
        if if_depth < MAXIFDEPTH {
            info!("Trying if");
            new_progress.extend(self.try_if(id).into_iter().filter_map(|f| {
                let mut new_p = progress.clone();
                new_p.add_cost_of_if();

                if new_p
                    .update_worklist(vec![SynthesisInfo {
                        id: f,
                        if_depth: if_depth + 1,
                        can_synthesize_rec: true,
                    }])
                    .is_ok()
                {
                    Some(new_p)
                } else {
                    None
                }
            }));
        }

        if can_synthesize_rec {
            info!("trying rec");
            let hash = self.egg[id].data;
            let hole = self.example_map.get_examples(hash);
            if self.sig.output == hole.get_positive_examples()[0].output.clone().into() {
                progress.add_cost_of_rec();
                let into_rec_call_id = self.egg.add(ArwenLang::Widen(hash, rec_id));
                self.egg.union(id, into_rec_call_id);
                new_progress.push(progress);
            }
        }

        new_progress
    }
    /*
       fn top_down_prop_helper(
           &mut self,
           hole: &Examples,
           hash: ExampleHash,
           id: Id,
           base_case: bool,
           nested_if_depth: u8,
           mut visited_set: HashSet<Id>,
       ) -> PropResult {
           let span = span!(Level::TRACE, "top_down_prop_helper");
           // `enter` returns a RAII guard which, when dropped, exits the span. this
           // indicates that we are in the span for the current lexical scope.
           let _enter = span.enter();
           info!("Starting top_down_prop_helper");

           // We are doing some kind of cycle
           if visited_set.contains(&id) {
               return PropResult::Failure;
           } else {
               visited_set.insert(id);
           }

           // Condition that checks if we bottom-up enumerated this
           if self.egg[id]
               .nodes
               .iter()
               .any(|n| n != &ArwenLang::Hole(EggHoleData(hash)))
           {
               return PropResult::Success;
           }

           // Condition that checks that we haven't already solved this
           if !(self.egg[id].nodes.len() == 1 && self.egg[id].nodes[0].is_hole()) {
               return PropResult::Success;
           }

           // Check to see if we can finish this with a simple widen to another eclass
           let wider_eclasses: Vec<Id> = self
               .example_map
               .wider(hole)
               .into_iter()
               .filter_map(|e| {
                   let eclass = *self.id_lookup.get(&e).unwrap();
                   if self
                       .egg
                       .index(eclass)
                       .nodes
                       .iter()
                       // We don't want to widen to just a hole
                       // And we don't want to skip trying to synthesize something over a probably wrong recursive call
                       .any(|n| !n.is_hole() && !n.is_rec())
                   {
                       None
                   } else {
                       Some(eclass)
                   }
               })
               .collect();

           if !wider_eclasses.is_empty() {
               let res = wider_eclasses
                   .into_iter()
                   .map(|id| self.egg.add(ArwenLang::Widen(hash, id)))
                   .collect_vec();

               info!("Widen created");
               let final_id = res.into_iter().fold(id, |id1, id2| {
                   self.egg.union(id1, id2);
                   self.egg.find(id1)
               });
               self.id_lookup.insert(hash, final_id);
               return PropResult::Success;
           }

           let mut res = PropResult::Failure;

           // We are going to look for candidate operations from our traces
           let narrower_eclasses = self.example_map.narrower(hole);
           if !narrower_eclasses.is_empty() {
               // We have a suggestion
               let mut candidate_operation = narrower_eclasses
                   .into_iter()
                   .flat_map(|e| {
                       let id = self.id_lookup.get(&e).unwrap();
                       let eclass = self.egg.index(*id);
                       let enodes = &eclass.nodes;
                       // We are skipping over classes with the hole node as that means it wasn't part of our traces
                       if enodes.iter().any(|l| matches!(l, ArwenLang::Hole(_))) {
                           Vec::new()
                       } else {
                           // Otherwise we can just grab all of our operations
                           enodes
                               .iter()
                               .filter_map(|n| match n {
                                   ArwenLang::Op(EggOpData(_, o), _) => Some(o),
                                   _ => None,
                               })
                               .collect()
                       }
                   })
                   .copied()
                   .collect_vec();

               // We sort and dedup to get a unique list of ops
               candidate_operation.sort();
               candidate_operation.dedup();

               candidate_operation.into_iter().for_each(|o| {
                   if let Some(examples_vec) =
                       hole.propogate_operation_examples(self.op_lookup.get(&o), &self.inverse_mapping)
                   {
                       assert!(!examples_vec.iter().any(|v| v.is_empty()));
                       /* let mut incomplete = true; */
                       examples_vec.into_iter().for_each(|examples_v| {
                           /* if incomplete { */
                           let x = examples_v
                               .into_iter()
                               .map(|e| {
                                   let e_hash = self.example_map.insert(&e);
                                   let e_id = self.id_exists_or_hole(e_hash);
                                   (e, e_hash, e_id)
                               })
                               .collect_vec();

                           let op_id = self.egg.add(ArwenLang::Op(
                               EggOpData(hash, o),
                               x.iter().map(|(_, _, e_id)| *e_id).collect_vec(),
                           ));
                           self.egg.union(id, op_id);
                           if x.into_iter()
                               .try_for_each(|(e, e_hash, e_id)| {
                                   self.top_down_prop_helper(
                                       &e,
                                       e_hash,
                                       e_id,
                                       base_case,
                                       nested_if_depth,
                                       visited_set.clone(),
                                   )
                                   .success()
                               })
                               .is_some()
                           {
                               let op = &self.op_lookup.get(&o).name;
                               info!(op, "Operation created");
                               /* incomplete = false; */
                               res = PropResult::Success
                           }
                           /* } */
                       })
                   }
               });
           }
           if !base_case {
               if nested_if_depth < 1 {
                   // Synthesize an if statement
                   let conds = self.type_map.get(&BaseType::Bool).unwrap().clone();
                   {
                       // Do some kinds of uniqueness assertion
                       let mut assert_stuff = conds
                           .iter()
                           .map(|id| {
                               self.example_map
                                   .get_examples(self.egg[*id].data)
                                   .get_positive_examples()
                           })
                           .collect_vec();
                       assert_stuff.sort();
                       let assert_len = assert_stuff.len();
                       assert_stuff.dedup();
                       assert!(assert_len == assert_stuff.len());
                   }

                   conds.into_iter().for_each(|c| {
                       /* if incomplete { */
                       let eclass = self.egg.index(c);
                       let cond_examples = self.example_map.get_examples(eclass.data);
                       let true_behavior = hole.filter_behavior_e(cond_examples, true);
                       let false_behavior = hole.filter_behavior_e(cond_examples, false);

                       let not_all_behaviours_are_accounted_for = hole.get_positive_examples().len()
                           != true_behavior.get_positive_examples().len()
                               + false_behavior.get_positive_examples().len();

                       if !(true_behavior.is_empty()
                           || false_behavior.is_empty()
                           || not_all_behaviours_are_accounted_for)
                       {
                           let true_hash = self.example_map.insert(&true_behavior);
                           let false_hash = self.example_map.insert(&false_behavior);

                           let true_id = self.id_exists_or_hole(true_hash);
                           let false_id = self.id_exists_or_hole(false_hash);

                           let if_id = self
                               .egg
                               .add(ArwenLang::If(EggIfData(hash), [c, true_id, false_id]));
                           self.egg.union(id, if_id);

                           if self
                               .top_down_prop_helper(
                                   &true_behavior,
                                   true_hash,
                                   true_id,
                                   true,
                                   nested_if_depth + 1,
                                   visited_set.clone(),
                               )
                               .is_success()
                               && self
                                   .top_down_prop_helper(
                                       &false_behavior,
                                       false_hash,
                                       false_id,
                                       false,
                                       nested_if_depth + 1,
                                       visited_set.clone(),
                                   )
                                   .is_success()
                           {
                               info!("If statement created");
                               res = PropResult::Success;
                           }
                       }
                       /* } */
                   });
               }

               if nested_if_depth > 0
                   && self.sig.output == hole.get_positive_examples()[0].output.clone().into()
               {
                   /* let into_rec_call_id = self.egg.add(ArwenLang::Widen(hash, rec_id));
                   self.egg.union(id, into_rec_call_id);
                   info!("Recursive call created"); */
               }
               info!(res = res.to_string(), "Propogation result");
               return res;
           }
           info!("Propogating bottomed out");
           PropResult::Failure
       }
    */
    pub fn dump_all_programs(&self, mut file: File) {
        use std::io::Write;
        self.example_map
            .into_iter()
            .sorted_by(|a, b| a.0.cmp(b.0))
            .for_each(|(e, e_hash)| {
                let eclass = self.id_lookup.get(e_hash).unwrap();
                let progs = self.dump_eclass(*eclass, HashSet::new());
                writeln!(&mut file, "{e}:\t{}", progs.into_iter().join("\n\t")).unwrap()
            })
    }

    pub fn dump_eclass(
        &self,
        eclass_id: Id,
        mut visited_list: HashSet<Id>,
    ) -> Vec<Program<BaseType>> {
        if visited_list.contains(&eclass_id) {
            Vec::new()
        } else {
            visited_list.insert(eclass_id);
            self.egg[eclass_id]
                .nodes
                .iter()
                .flat_map(|n| match n {
                    ArwenLang::Hole(_) => Vec::new(),
                    ArwenLang::Constant(c) => vec![Program {
                        node: c.1.clone().into(),
                        args: Vec::new(),
                    }],
                    ArwenLang::Var(v) => vec![Program {
                        node: v.1.clone().into(),
                        args: Vec::new(),
                    }],
                    ArwenLang::If(_, [idb, idt, idf]) => [
                        self.dump_eclass(*idb, visited_list.clone()).into_iter(),
                        self.dump_eclass(*idt, visited_list.clone()).into_iter(),
                        self.dump_eclass(*idf, visited_list.clone()).into_iter(),
                    ]
                    .into_iter()
                    .multi_cartesian_product()
                    .map(|args| Program {
                        node: ProgramNode::If,
                        args,
                    })
                    .collect_vec(),
                    ArwenLang::Op(o, args) if args.is_empty() => vec![Program {
                        node: self.op_lookup.get(&o.1).clone().into(),
                        args: Vec::new(),
                    }],
                    ArwenLang::Op(o, args) => args
                        .iter()
                        .map(|a| self.dump_eclass(*a, visited_list.clone()).into_iter())
                        .multi_cartesian_product()
                        .map(|args| Program {
                            node: self.op_lookup.get(&o.1).clone().into(),
                            args,
                        })
                        .collect_vec(),
                    ArwenLang::Rec(_, args) => args
                        .iter()
                        .map(|a| self.dump_eclass(*a, visited_list.clone()).into_iter())
                        .multi_cartesian_product()
                        .map(|args| Program {
                            node: ProgramNode::Rec(BaseType::Int),
                            args,
                        })
                        .collect_vec(),
                    ArwenLang::Widen(_, id) => self.dump_eclass(*id, visited_list.clone()),
                })
                .collect_vec()
        }
    }

    pub fn extraction(&self, hole: &Examples) -> Option<Program<BaseType>> {
        info!("Starting Extraction");
        let hash = self.example_map.get_examplehash(hole).unwrap();

        let eclass = self.id_lookup.get(&hash).unwrap();

        let mut programs = self.extraction_helper(eclass, &mut HashMap::new(), false);
        info!("Finished Extraction");

        programs.sort_by_key(|a| a.size());

        info!("Program Sorted");

        programs.retain(|p| {
            hole.is_consistent_with(|t| {
                p.interpret(&t.into(), p, &None)
                    .is_ok_and(|x| x == t.output)
            })
        });

        info!("Programs Ready");

        println!("{}", programs.iter().map(ToString::to_string).join("\n"));

        programs.first().cloned()
    }
    /*
       // Fancy extractor?
       // We are immitating the symbolic_block_based_evaluator
       // However we need to worry about cycles in traces now
       // And we also want to enforce other properties... specifically around recursion
       fn fancy_extraction_helper(
           &self,
           eclass_id: Id,
           // So I want to avoid cycles, which means maybe I need a list of visited nodes?
           mut visited_set: HashSet<Id>,
           // I also need to keep track of the last recursive argument so that I enforce the constant recursion
           last_rec_arg: Option<&Constant>,
           // So here I somehow want to keep track of the current synthesis state
           solution_graph: &mut DiGraph<ProgramNodeWithHole, ()>,
           // I also want to be able to compute recursion(from the top)
           root_node: NodeIndex,
           // So I hand out a the current node on the graph
           // This could be a whole in the initial case,
           // But we could be using it to double check the program when doing recursion
           current_node: NodeIndex,
       ) -> Status {
           match solution_graph.node_weight(current_node).unwrap() {
               // We have a program node, we need to check against something
               ProgramNodeWithHole::ProgramNode(n) => {
                   todo!();
                   let eclass = self.egg.index(eclass_id);
                   let enode = eclass
                       .nodes
                       .iter()
                       .filter(|e_n| {
                           if let ArwenLangToNode::Node(x) = e_n.try_from(&self.op_lookup) {
                               &x == n
                           } else {
                               false
                           }
                       })
                       .collect_vec();

                   if enode.is_empty() {
                       return Status::HitError(HashSet::new());
                   }

                   // For each of the potential enodes, speculate on the right path and see if it works out.
                   if let Some(result) = enode.into_iter().find_map(|n| todo!()) {
                       return Status::SoFarSoGood(result);
                   } else {
                       return Status::HitError(HashSet::new());
                   }
               }
               // We have a hole which we need to speculatively fill
               ProgramNodeWithHole::Hole => {
                   // We can get potential candidates from the egraph
                   let eclass = self.egg.index(eclass_id);
                   let mut enodes = eclass.nodes.clone();
                   enodes.sort_by(extraction_node_ordering);
                   visited_set.insert(eclass_id);

                   match &enodes[0] {
                       ArwenLang::Hole(_) => Status::HitError(HashSet::new()),
                       ArwenLang::Constant(c) => {
                           *solution_graph.node_weight_mut(current_node).unwrap() =
                               ProgramNodeWithHole::ProgramNode(ProgramNode::Constant(c.1.clone()));
                           Status::SoFarSoGood(HashSet::new())
                       }
                       ArwenLang::Var(v) => {
                           *solution_graph.node_weight_mut(current_node).unwrap() =
                               ProgramNodeWithHole::ProgramNode(ProgramNode::Variable(v.1.clone()));
                           Status::SoFarSoGood(HashSet::new())
                       }
                       ArwenLang::If(_, _) => todo!(),
                       ArwenLang::Op(o, args) => {
                           if args.is_empty() {
                               *solution_graph.node_weight_mut(current_node).unwrap() =
                                   ProgramNodeWithHole::ProgramNode(ProgramNode::Operation(
                                       self.op_lookup(&o.1).clone(),
                                   ));
                               Status::SoFarSoGood(HashSet::new())
                           } else {
                               *solution_graph.node_weight_mut(current_node).unwrap() =
                                   ProgramNodeWithHole::ProgramNode(ProgramNode::Operation(
                                       self.op_lookup(&o.1).clone(),
                                   ));

                               let inputs = args
                                   .into_iter()
                                   .map(|i| {
                                       let a = solution_graph.add_node(ProgramNodeWithHole::Hole);
                                       solution_graph.add_edge(current_node, a, ());
                                       (i, a)
                                   })
                                   .collect_vec();

                               inputs.into_iter().for_each(|(i, a)| {
                                   self.fancy_extraction_helper(
                                       *i,
                                       visited_set.clone(),
                                       last_rec_arg,
                                       solution_graph,
                                       root_node,
                                       a,
                                   );
                                   todo!()
                               });
                               todo!()
                           }
                       }
                       ArwenLang::Widen(_, _) => todo!(),
                   }
               }
           }

           // Create a graph of program nodes? Not always just one choice in thems of the path you take... Maybe doesn't matter, won't strictly be useful when doing recursion tracking.

           // Further calls can add to the graph, and then worst case we iterate over and kill things that don't work out with the error set

           // The final thing is to return the completed graph(to extract the program out of) or an error
       }
    */

    fn extraction_helper(
        &self,
        eclass: &Id,
        memoize_map: &mut HashMap<Id, Vec<Program<BaseType>>>,
        base_case: bool,
    ) -> Vec<Program<BaseType>> {
        let span = span!(Level::TRACE, "extraction_helper");
        // `enter` returns a RAII guard which, when dropped, exits the span. this
        // indicates that we are in the span for the current lexical scope.
        let _enter = span.enter();

        let eclass = &self.egg.find(*eclass);
        if let Some(v) = memoize_map.get(eclass) {
            info!("Already explored");
            return v.to_vec();
        } else {
            memoize_map.insert(*eclass, Vec::new());
        }

        let nodes = &self.egg[*eclass].nodes;

        if nodes.is_empty() {
            warn!("Eclass is empty, something went wrong");
            panic!()
        }

        if nodes.len() == 1 && nodes[0].is_hole() {
            warn!("Eclass is just the hole");
            return Vec::new();
        }

        // So we have a hole, we want to find the eclass that contains it
        // Then we will iteratively work to extract from the eclass and it's children til we have a complete program
        // We can have dead ends? So maybe some kind of backtracking?
        // Lets just produce all of them and sort/filter
        let mut res = nodes
            .iter()
            .flat_map(|v| match v {
                ArwenLang::Hole(_) => Vec::new(),
                ArwenLang::Constant(c) => vec![Program::from(c.1.clone())],
                ArwenLang::Var(v) => vec![Program::from(v.1.clone())],
                ArwenLang::If(..) if base_case => {
                    warn!("If in base case");
                    Vec::new()
                }
                ArwenLang::If(_, ids) => ids
                    .iter()
                    .enumerate()
                    .map(|(idx, i)| self.extraction_helper(i, memoize_map, idx == 1).into_iter())
                    .multi_cartesian_product()
                    .map(|args| Program {
                        node: ProgramNode::If,
                        args,
                    })
                    .collect_vec(),
                ArwenLang::Op(o, ids) if ids.is_empty() => {
                    vec![Program {
                        node: ProgramNode::Operation(self.op_lookup(&o.1).clone()),
                        args: vec![],
                    }]
                }
                ArwenLang::Rec(ty, ids) if !base_case => {
                    info!("Processing Rec");
                    ids.iter()
                        .map(|i| { self.extraction_helper(i, memoize_map, false) }.into_iter())
                        .multi_cartesian_product()
                        .map(|args| Program {
                            node: ProgramNode::Rec(ty.1),
                            args,
                        })
                        .collect_vec()
                }
                ArwenLang::Rec(..) => {
                    warn!("Empty because rec generated in base case");
                    Vec::new()
                }
                ArwenLang::Op(o, ids) => ids
                    .iter()
                    .map(|i| {
                        self.extraction_helper(i, memoize_map, base_case)
                            .into_iter()
                    })
                    .multi_cartesian_product()
                    .map(|args| Program {
                        node: ProgramNode::Operation(self.op_lookup(&o.1).clone()),
                        args,
                    })
                    .collect_vec(),
                ArwenLang::Widen(_, i) => {
                    info!("widening");
                    self.extraction_helper(i, memoize_map, base_case)
                }
            })
            .collect_vec();

        res.sort_by_key(|a| a.size());
        res = res.into_iter().dedup().collect();

        info!(candidates = res.iter().join("\n"), "Candidates");
        memoize_map.insert(*eclass, res.clone());
        res
    }

    fn update_and_split(&mut self, cex: ()) {
        todo!()
    }
}
