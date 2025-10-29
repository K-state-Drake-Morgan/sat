//! The Parts needed to solve a boolean sat problem

use super::parser::{HumanOperator, Sentance};
use log::{debug, trace};
use num_bigint::BigUint;
use num_traits::Zero;
use rayon::iter::{ParallelBridge, ParallelIterator};
use std::collections::HashMap;
use std::sync::Arc;

/// Part of a boolean formula
#[derive(Debug, PartialEq, Eq)]
pub enum FormulaPart {
    /// Boolean And
    And,
    /// Boolean Or
    Or,
    /// Boolean Not
    Not,
    /// Boolean Implies
    Implies,
    /// Boolean Varible like x or y
    Variable(usize), // using usize as identifier, will use hashmap to go from string to ussize
    // The usize is the 2^n for a big int for use to bit mask
    /// Boolean Constant: true or false
    Constant(bool), // for clause elimination
}

/// Part of a boolean formula but with only non smaller parts
#[derive(Debug, PartialEq, Eq)]
pub enum AtomicFormulaPart {
    /// Boolean And
    And,
    /// Boolean Or
    Or,
    /// Boolean Not
    Not,
    /// Boolean Varible like x or y
    Variable(usize), // using usize as identifier, will use hashmap to go from string to ussize
    // The usize is the 2^n for a big int for use to bit mask
    /// Boolean Constant: true or false
    Constant(bool), // for clause elimination
}

/// An error for a going from HumanOperator to FormulaPart
#[derive(Debug)]
pub struct UnReadableError;

impl TryFrom<HumanOperator> for FormulaPart {
    type Error = UnReadableError;
    fn try_from(value: HumanOperator) -> Result<Self, Self::Error> {
        Ok(match value {
            HumanOperator::And => FormulaPart::And,
            HumanOperator::Not => FormulaPart::Not,
            HumanOperator::Or => FormulaPart::Or,
            HumanOperator::Implies => FormulaPart::Implies,
            HumanOperator::Variable(_) => FormulaPart::Variable(0),
            _ => Err(UnReadableError)?,
        })
    }
}

/// A Formula with names to varible position
#[derive(Debug)]
pub struct Formula {
    /// data stored in postfix
    data: Arc<Vec<FormulaPart>>,
    /// named variables
    names: HashMap<String, usize>,
}

impl Formula {
    /// The Number of operands in the data (how many unique varibles)
    pub fn operands(&self) -> usize {
        self.names.len()
    }

    /// panics if the formula is nonsensical
    pub fn solve(&self, variables: &BigUint) -> bool {
        let mut stack: Vec<bool> = Vec::with_capacity(self.data.len() >> 2);
        for part in self.data.iter() {
            match part {
                FormulaPart::Variable(var) => {
                    let bit = (variables >> var) & BigUint::from(1u8);
                    stack.push(!bit.is_zero());
                }
                FormulaPart::Not => {
                    let change = !stack.pop().expect("Nothing to pop");
                    stack.push(change);
                }
                FormulaPart::And => {
                    let right = stack.pop().expect("Nothing to pop");
                    let left = stack.pop().expect("Nothing to pop");
                    stack.push(right && left);
                }
                FormulaPart::Or => {
                    let right = stack.pop().expect("Nothing to pop");
                    let left = stack.pop().expect("Nothing to pop");
                    stack.push(right || left);
                }
                FormulaPart::Implies => {
                    let right = stack.pop().expect("Nothing to pop");
                    let left = stack.pop().expect("Nothing to pop");
                    stack.push(!left || right);
                }
                FormulaPart::Constant(b) => stack.push(*b),
            }
        }

        assert_eq!(stack.len(), 1, "formula not fully reduced");
        let result = stack.pop().unwrap();
        trace!(
            "Tried: {:0width$b} and got: {}",
            variables,
            result,
            width = self.names.len()
        );
        result
    }

    /// Solve the satisabillity problem
    pub fn fully_solve(&self) -> Option<BigUint> {
        debug!("Solving: {:?}", self.data);
        let one: BigUint = BigUint::from(1_u8);
        // this is the total range
        let to = one << self.names.len();
        let zero = BigUint::from(0_u8);
        // create a hint
        let mut should_values: HashMap<usize, bool> = HashMap::with_capacity(self.names.len());
        let mut stack: Vec<FormulaPart> = Vec::with_capacity(self.data.len() >> 2);
        for part in self.data.iter() {
            match part {
                FormulaPart::Variable(var) => {
                    stack.push(FormulaPart::Variable(*var));
                }
                FormulaPart::Not => {
                    let change = stack.pop().expect("Nothing to pop");
                    if let FormulaPart::Variable(x) = change {
                        should_values.insert(x, false);
                    }
                    stack.push(FormulaPart::Not);
                }
                FormulaPart::And => {
                    let right = stack.pop().expect("Nothing to pop");
                    let left = stack.pop().expect("Nothing to pop");
                    if let FormulaPart::Variable(x) = left {
                        should_values.insert(x, true);
                    }
                    if let FormulaPart::Variable(x) = right {
                        should_values.insert(x, true);
                    }
                    stack.push(FormulaPart::And);
                }
                FormulaPart::Or => {
                    let right;
                    if let Some(FormulaPart::Variable(r)) = stack.pop() {
                        right = Some(r);
                    } else {
                        right = None;
                    }
                    let left;
                    if let Some(FormulaPart::Variable(l)) = stack.pop() {
                        left = Some(l);
                    } else {
                        left = None;
                    }
                    match (left, right) {
                        (Some(l), Some(r)) => {
                            if let None = should_values.get(&l) {
                                should_values.insert(l, true);
                            }
                            if let None = should_values.get(&r) {
                                should_values.insert(r, true);
                            }
                        }
                        (Some(l), None) => {
                            if let None = should_values.get(&l) {
                                should_values.insert(l, true);
                            }
                        }
                        (None, Some(r)) => {
                            if let None = should_values.get(&r) {
                                should_values.insert(r, true);
                            }
                        }
                        _ => {}
                    }
                    stack.push(FormulaPart::Or);
                }
                FormulaPart::Implies => {
                    let right = stack.pop().expect("Nothing to pop");
                    let left = stack.pop().expect("Nothing to pop");
                    if let FormulaPart::Variable(x) = left {
                        if let Some(value) = should_values.get(&x)
                            && *value != true
                        {
                            should_values.insert(x, false);
                        }
                    }
                    if let FormulaPart::Variable(x) = right {
                        if let Some(value) = should_values.get(&x)
                            && *value != false
                        {
                            should_values.insert(x, true);
                        }
                    }
                    stack.push(FormulaPart::Or);
                }
                FormulaPart::Constant(b) => stack.push(FormulaPart::Constant(*b)),
            }
        }
        let mut hint: BigUint = BigUint::ZERO;
        for value in (0..self.names.len()).rev() {
            hint = hint << 1;
            if let Some(b) = should_values.get(&value) {
                if *b {
                    hint += BigUint::from(1_u8);
                }
            }
        }

        let hint_forward = num_iter::range(hint.clone(), to);
        let hint_back = num_iter::range(zero, hint).rev();

        hint_forward.chain(hint_back).par_bridge().find_any(|x| {
            return self.solve(&x);
        })
    }

    /// Iterates backwards thru the formula and attempts to find a solution via guessing what
    /// the childrens values should be
    pub fn find_solve(&self) -> Option<BigUint> {
        // setup values only used here
        #[derive(Clone, Copy)]
        enum Needs {
            True,
            False,
            Either,
            Is(bool),
        }

        // create a vector that stores the varible values
        let values: Vec<Needs> = vec![Needs::Either; self.operands()];

        todo!()
    }

    /// Makes it easier to work on self by removings implies and doing negation
    pub fn simplify(&mut self) {
        let mut stack: Vec<FormulaPart> = Vec::with_capacity(self.data.len());
        for element in self.data.iter() {
            match element {
                FormulaPart::Variable(index) => stack.push(FormulaPart::Variable(*index)),
                FormulaPart::Constant(value) => stack.push(FormulaPart::Constant(*value)),
                FormulaPart::And => stack.push(FormulaPart::And),
                FormulaPart::Or => stack.push(FormulaPart::Or),
                FormulaPart::Implies => {
                    // insert not to the left (harder than it looks)
                    stack.push(FormulaPart::Not);
                    stack.push(FormulaPart::Or);
                }
                FormulaPart::Not => {
                    if let None = stack.pop_if(|last| *last == FormulaPart::Not) {
                        stack.push(FormulaPart::Not);
                    }
                }
            }
        }
        self.data = Arc::new(stack);
    }
}

/// Error when failure to convert from a sentance to a formula
#[derive(Debug)]
pub enum FormulaFromSentanceError {}

impl TryFrom<Sentance> for Formula {
    type Error = FormulaFromSentanceError;

    fn try_from(value: Sentance) -> Result<Self, Self::Error> {
        let input = value.data;
        let mut output: Vec<FormulaPart> = Vec::new();
        let mut stack: Vec<HumanOperator> = Vec::new();
        let mut names: HashMap<String, usize> = HashMap::new();

        for token in input {
            match token {
                HumanOperator::Variable(name) => {
                    // assign index if new variable
                    if let Some(index) = names.get(&name) {
                        output.push(FormulaPart::Variable(*index));
                    } else {
                        names.insert(name.clone(), names.len());
                        output.push(FormulaPart::Variable(*names.get(&name).unwrap()));
                    }
                }

                HumanOperator::Constant(value) => {
                    output.push(FormulaPart::Constant(value));
                }

                HumanOperator::Not
                | HumanOperator::And
                | HumanOperator::Or
                | HumanOperator::Implies => {
                    while let Some(top) = stack.last() {
                        if top.precedence() < token.precedence()
                            || (top.precedence() == token.precedence()
                                && !token.is_right_associative())
                        {
                            output.push(FormulaPart::try_from(stack.pop().unwrap()).unwrap());
                        } else {
                            break;
                        }
                    }
                    stack.push(token);
                }

                HumanOperator::OpeningParenthesis
                | HumanOperator::OpeningBracket
                | HumanOperator::OpeningCurly => {
                    stack.push(token);
                }

                HumanOperator::ClosingParenthesis
                | HumanOperator::ClosingBracket
                | HumanOperator::ClosingCurly => {
                    while let Some(top) = stack.pop() {
                        match top {
                            HumanOperator::OpeningParenthesis
                            | HumanOperator::OpeningBracket
                            | HumanOperator::OpeningCurly => break,
                            _ => output.push(FormulaPart::try_from(top).unwrap()),
                        }
                    }
                }
            }
        }

        // Pop any remaining operators
        while let Some(top) = stack.pop() {
            output.push(FormulaPart::try_from(top).unwrap());
        }

        Ok(Formula {
            data: Arc::new(output),
            names,
        })
    }
}

#[cfg(test)]
mod formula_tests {
    use super::super::parser::*;
    use super::*;
    #[test]
    fn can_convert() {
        let sentence = Sentance {
            data: vec![
                HumanOperator::Variable("A".to_string()),
                HumanOperator::And,
                HumanOperator::Not,
                HumanOperator::Variable("B".to_string()),
                HumanOperator::Or,
                HumanOperator::Variable("C".to_string()),
            ],
        };

        let formula = Formula::try_from(sentence).unwrap();

        println!("{:?}", formula.data);
        println!("{:?}", formula.names);

        assert!(
            formula.data
                == Arc::new(vec![
                    FormulaPart::Variable(0),
                    FormulaPart::Variable(1),
                    FormulaPart::Not,
                    FormulaPart::And,
                    FormulaPart::Variable(2),
                    FormulaPart::Or
                ])
        );
    }

    #[test]
    fn simplify_removes_extra_nots() {
        let sentance = Sentance {
            data: vec![
                HumanOperator::Not,
                HumanOperator::Not,
                HumanOperator::Variable("A".to_string()),
            ],
        };

        let mut formula = Formula::try_from(sentance).unwrap();

        formula.simplify();
        let should_be = Arc::new(vec![FormulaPart::Variable(0)]);
        println!("got: {:?}, should have: {:?}", formula.data, should_be);
        assert!(formula.data == should_be);
    }

    #[test]
    fn simplify_removes_implies() {
        let sentance = Sentance {
            data: vec![
                HumanOperator::Variable("A".to_string()),
                HumanOperator::Implies,
                HumanOperator::Variable("B".to_string()),
            ],
        };

        let mut formula = Formula::try_from(sentance).unwrap();

        formula.simplify();
        let should_be = Arc::new(vec![
            FormulaPart::Variable(0),
            FormulaPart::Not,
            FormulaPart::Variable(1),
            FormulaPart::Or,
        ]);
        println!("got: {:?}, should have: {:?}", formula.data, should_be);
        assert!(formula.data == should_be);
    }

    #[test]
    fn simplify_dosn_t_change_output() {
        let sentance = Sentance {
            data: vec![
                HumanOperator::Variable("A".to_string()),
                HumanOperator::Implies,
                HumanOperator::Variable("B".to_string()),
            ],
        };

        let mut formula = Formula::try_from(sentance).unwrap();

        formula.simplify();
        let should_be = Arc::new(vec![
            FormulaPart::Variable(0),
            FormulaPart::Variable(1),
            FormulaPart::Not,
            FormulaPart::Or,
        ]);
        println!("got: {:?}, should have: {:?}", formula.data, should_be);
        assert!(formula.data == should_be);
    }
}
