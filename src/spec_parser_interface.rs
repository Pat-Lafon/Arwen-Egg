use std::{collections::HashMap, rc::Rc};

use arwen_elrond_ipc::{
    ipc::{
        ElrondAssertion, ElrondForallFormula, ElrondKnownPredicate, ElrondPred, ElrondPredicates,
        ElrondSpec, ElrondTpedvar, ElrondType, FreeVar,
    },
    ipc_assertion::{
        Assertion, AssertionFile, AssertionPredicates, AssertionType, Pred, Spec, Tpedvar,
    },
};

use crate::language::{BaseType, Constant, InnerPredicate, Predicate, RefinementType, Signature};

pub fn parse(src: String, sig: Signature<BaseType>) -> SpecShim {
    let parser = arwen_elrond_ipc::assertion_parser::AssertionFileParser::new();
    SpecShim::convert(parser.parse(&src).unwrap(), sig)
}

pub type SpecFunType = dyn Fn(&Vec<Constant>) -> Result<bool, ()>;
pub type SpecMap = HashMap<String, Rc<SpecFunType>>;

pub fn specs(preds: AssertionPredicates) -> SpecMap {
    let mut map: SpecMap = HashMap::new();

    [(
        Pred::head,
        Rc::new(
            |args: &Vec<Constant>| match (args.get(0).unwrap(), args.get(1).unwrap()) {
                (Constant::IntList(l), _) if l.is_empty() => Ok(false),
                (Constant::IntList(l), Constant::Int(i)) => Ok(&l.hd().unwrap() == i),
                _ => panic!(),
            },
        ),
    )]
    .into_iter()
    .filter(|(k, _)| preds.0.contains(k))
    .for_each(|(k, v)| {
        map.insert(k.to_string(), v);
    });

    map
}

pub struct SpecShim {
    pub spec_map: SpecMap,
    pub spec_sig: Signature<RefinementType>,
}

impl From<ElrondPred> for InnerPredicate {
    fn from(value: ElrondPred) -> Self {
        match value {
            ElrondPred::True => Self::Bool(true),
            ElrondPred::Atom(s) => todo!(),
            ElrondPred::Implies(p1, p2) => {
                Self::Impl(Box::new((*p1).into()), Box::new((*p2).into()))
            }
            ElrondPred::Ite(p1, p2, p3) => todo!(),
            ElrondPred::Not(p) => Self::Neg(Box::new((*p).into())),
            ElrondPred::And(a) => a.into_iter().fold(Self::Bool(true), |acc, x| {
                Self::Conj(Box::new(acc), Box::new(x.into()))
            }),
            ElrondPred::Or(_) => todo!(),
            ElrondPred::Iff(_, _) => Self::Equal(todo!(), todo!()),
        }
    }
}

impl From<Assertion> for InnerPredicate {
    fn from(value: Assertion) -> Self {
        match value {
            Assertion::True => Self::Bool(true),
            Assertion::Predicate(s, _) => todo!(),
            Assertion::Op(_, _, _) => todo!(),
            Assertion::Implies(p1, p2) => {
                Self::Impl(Box::new((*p1).into()), Box::new((*p2).into()))
            }
            Assertion::Not(p) => Self::Neg(Box::new((*p).into())),
            Assertion::And(a) => a.into_iter().fold(Self::Bool(true), |acc, x| {
                Self::Conj(Box::new(acc), Box::new(x.into()))
            }),
            Assertion::Or(_) => todo!(),
            Assertion::Iff(_, _) => Self::Equal(todo!(), todo!()),
        }
    }
}

impl From<AssertionType> for BaseType {
    fn from(value: AssertionType) -> Self {
        match value {
            AssertionType::Bool => BaseType::Bool,
            AssertionType::Int => BaseType::Int,
            AssertionType::Generic(s) => {
                dbg!(s);
                unimplemented!()
            }
        }
    }
}

fn elrond_spec_helper(Spec(tpred, p): Spec, len: usize) -> Predicate {
    Predicate::Forall(
        tpred
            .into_iter()
            .skip(len)
            .map(|Tpedvar(ty, name)| (name, ty.into()))
            .collect(),
        p.into(),
    )
}

impl SpecShim {
    pub fn convert(
        AssertionFile {
            preds,
            pre_spec,
            post_spec,
        }: AssertionFile,
        Signature { input, output }: Signature<BaseType>,
    ) -> Self {
        let pred = pre_spec.map_or_else(
            || Predicate::Inner(crate::language::InnerPredicate::Bool(true)),
            |x| elrond_spec_helper(x, input.len()),
        );

        let mut input: Vec<RefinementType> = input.into_iter().map(|x| x.into()).collect();
        input.last_mut().unwrap().p = pred;

        let post_pred = elrond_spec_helper(post_spec, input.len());

        let output = RefinementType {
            ty: output,
            p: post_pred,
        };

        SpecShim {
            spec_map: specs(preds),
            spec_sig: Signature { input, output },
        }
    }
}
