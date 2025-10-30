//! The Parts needed to solve a boolean sat problem

use log::{debug, trace};
use num_bigint::BigUint;
use num_traits::One;
use num_traits::Zero;
use rayon::iter::{ParallelBridge, ParallelIterator};
use std::collections::HashMap;
use std::error::Error;
use std::fmt::Display;
use std::sync::Arc;

/// Part of a boolean formula but with only non smaller parts
#[derive(Debug, PartialEq, Eq)]
#[repr(u8)]
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

#[repr(u8)]
enum FormulaOperator {
    And,
    Or,
    Not,
    Implies,
    OpenParenthisies { line: usize, column: usize },
}

/// Part of a boolean formula but with only non smaller parts
#[derive(Debug, PartialEq, Eq, Clone, Copy, PartialOrd, Ord)]
pub enum FormulaPart {
    /// Boolean And
    And,
    /// Boolean Or
    Or,
    /// Boolean Not
    Not,
    /// Boolean Varible like x or y
    Variable, // using usize as identifier, will use hashmap to go from string to ussize
    // The usize is the 2^n for a big int for use to bit mask
    /// Boolean Constant: true or false
    Constant, // for clause elimination
}

/// A Formula with names to varible position
#[derive(Debug)]
pub struct Formula {
    /// data stored in postfix
    data: Arc<Vec<AtomicFormulaPart>>,
    /// named variables
    names: Vec<String>,
}

impl Formula {
    /// how many named varibles there are
    pub fn operands(&self) -> usize {
        self.names.len()
    }
    /// panics if the formula is nonsensical
    pub fn solve(&self, variables: &BigUint) -> bool {
        let mut stack: Vec<bool> = Vec::with_capacity(self.data.len() >> 2);
        for part in self.data.iter() {
            match part {
                AtomicFormulaPart::Variable(var) => {
                    let bit = (variables >> var) & BigUint::from(1u8);
                    stack.push(!bit.is_zero());
                }
                AtomicFormulaPart::Not => {
                    let change = !stack.pop().expect("Nothing to pop");
                    stack.push(change);
                }
                AtomicFormulaPart::And => {
                    let right = stack.pop().expect("Nothing to pop");
                    let left = stack.pop().expect("Nothing to pop");
                    stack.push(right && left);
                }
                AtomicFormulaPart::Or => {
                    let right = stack.pop().expect("Nothing to pop");
                    let left = stack.pop().expect("Nothing to pop");
                    stack.push(right || left);
                }
                AtomicFormulaPart::Constant(b) => stack.push(*b),
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

    /// fully solve a given boolean formula looking for a true
    pub fn fully_solve(&self) -> Option<BigUint> {
        let one: BigUint = BigUint::one();
        let zero: BigUint = BigUint::zero();
        let to = &one << self.names.len();

        // Heuristic: collect likely true/false values from formula structure
        let mut should_values: HashMap<usize, bool> = HashMap::with_capacity(self.names.len());
        let mut stack: Vec<AtomicFormulaPart> = Vec::with_capacity(self.data.len() >> 2);

        for part in self.data.iter() {
            match part {
                AtomicFormulaPart::Variable(var) => stack.push(AtomicFormulaPart::Variable(*var)),

                AtomicFormulaPart::Constant(b) => stack.push(AtomicFormulaPart::Constant(*b)),

                AtomicFormulaPart::Not => {
                    if let Some(AtomicFormulaPart::Variable(v)) = stack.pop() {
                        should_values.insert(v, false);
                    }
                    stack.push(AtomicFormulaPart::Not);
                }

                AtomicFormulaPart::And => {
                    let right = stack.pop().expect("And missing right operand");
                    let left = stack.pop().expect("And missing left operand");

                    if let AtomicFormulaPart::Variable(v) = left {
                        should_values.insert(v, true);
                    }
                    if let AtomicFormulaPart::Variable(v) = right {
                        should_values.insert(v, true);
                    }

                    stack.push(AtomicFormulaPart::And);
                }

                AtomicFormulaPart::Or => {
                    let right = stack.pop();
                    let left = stack.pop();

                    match (left, right) {
                        (
                            Some(AtomicFormulaPart::Variable(l)),
                            Some(AtomicFormulaPart::Variable(r)),
                        ) => {
                            should_values.entry(l).or_insert(true);
                            should_values.entry(r).or_insert(true);
                        }
                        (Some(AtomicFormulaPart::Variable(l)), _) => {
                            should_values.entry(l).or_insert(true);
                        }
                        (_, Some(AtomicFormulaPart::Variable(r))) => {
                            should_values.entry(r).or_insert(true);
                        }
                        _ => {}
                    }

                    stack.push(AtomicFormulaPart::Or);
                }
            }
        }

        // Build initial hint from heuristic
        let mut hint: BigUint = BigUint::zero();
        for value in (0..self.names.len()).rev() {
            hint <<= 1;
            if let Some(b) = should_values.get(&value) {
                if *b {
                    hint += BigUint::one();
                }
            }
        }

        // Search space: try forward from hint, then backward
        let hint_forward = num_iter::range(hint.clone(), to.clone());
        let hint_back = num_iter::range(zero.clone(), hint).rev();

        // Parallel search using Rayon
        hint_forward
            .chain(hint_back)
            .par_bridge()
            .find_any(|candidate| self.solve(candidate))
    }
}

/// An Invalid Boolean Formula
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct InvalidFormula {
    /// Line in the string the error occured on
    line: usize,
    /// Column in the string the error occured on
    column: usize,
    /// Reason for the formula error
    error: InvalidFormulaPart,
}

impl Display for InvalidFormula {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(
            f,
            "Line: {}\nColumn: {}\nReason: {}",
            self.line, self.column, self.error
        )
    }
}

impl Error for InvalidFormula {
    fn cause(&self) -> Option<&dyn Error> {
        Some(&self.error)
    }
}

///Reason for a formula error
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum InvalidFormulaPart {
    ///
    ExtraParenthisies,
    ///
    UnclosedParenthisies,
    ///
    InvalidOperand(FormulaPart),
    ///
    InvalidPostFix,
}

impl Display for InvalidFormulaPart {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl Error for InvalidFormulaPart {}

impl TryFrom<String> for Formula {
    type Error = InvalidFormula;

    fn try_from(value: String) -> Result<Self, Self::Error> {
        let mut data: Vec<AtomicFormulaPart> = Vec::with_capacity(value.len());
        let mut names: HashMap<String, usize> = HashMap::new(); // will convert to a Vec later
        let mut buffer: String = String::new();
        let mut stack: Vec<FormulaOperator> = Vec::with_capacity(value.len() >> 1);
        for (line_number, line) in value.lines().enumerate() {
            for (column, character) in line.chars().enumerate() {
                match character {
                    '(' => {
                        let buffer_is_empty = buffer.is_empty();
                        if !buffer_is_empty {
                            if let Some(index) = names.get(&buffer) {
                                data.push(AtomicFormulaPart::Variable(*index));
                            } else {
                                let index = names.len();
                                names.insert(buffer.clone(), index);
                                data.push(AtomicFormulaPart::Variable(index));
                                buffer.clear();
                            }
                        }
                        stack.push(FormulaOperator::OpenParenthisies {
                            line: line_number,
                            column: column,
                        });
                    }
                    '&' => {
                        let buffer_is_empty = buffer.is_empty();
                        if !buffer_is_empty {
                            if let Some(index) = names.get(&buffer) {
                                data.push(AtomicFormulaPart::Variable(*index));
                            } else {
                                let index = names.len();
                                names.insert(buffer.clone(), index);
                                data.push(AtomicFormulaPart::Variable(index));
                                buffer.clear();
                            }
                        }
                        stack.push(FormulaOperator::And);
                    }
                    '|' => {
                        let buffer_is_empty = buffer.is_empty();
                        if !buffer_is_empty {
                            if let Some(index) = names.get(&buffer) {
                                data.push(AtomicFormulaPart::Variable(*index));
                            } else {
                                let index = names.len();
                                names.insert(buffer.clone(), index);
                                data.push(AtomicFormulaPart::Variable(index));
                                buffer.clear();
                            }
                        }
                        stack.push(FormulaOperator::Or);
                    }
                    '!' => {
                        let buffer_is_empty = buffer.is_empty();
                        if !buffer_is_empty {
                            if let Some(index) = names.get(&buffer) {
                                data.push(AtomicFormulaPart::Variable(*index));
                            } else {
                                let index = names.len();
                                names.insert(buffer.clone(), index);
                                data.push(AtomicFormulaPart::Variable(index));
                                buffer.clear();
                            }
                        }
                        stack.push(FormulaOperator::Not);
                    }
                    '>' => {
                        let buffer_is_empty = buffer.is_empty();
                        if !buffer_is_empty {
                            if let Some(index) = names.get(&buffer) {
                                data.push(AtomicFormulaPart::Variable(*index));
                            } else {
                                let index = names.len();
                                names.insert(buffer.clone(), index);
                                data.push(AtomicFormulaPart::Variable(index));
                                buffer.clear();
                            }
                        }
                        stack.push(FormulaOperator::Implies);
                    }
                    ')' => {
                        let buffer_is_empty = buffer.is_empty();
                        if !buffer_is_empty {
                            if let Some(index) = names.get(&buffer) {
                                data.push(AtomicFormulaPart::Variable(*index));
                            } else {
                                let index = names.len();
                                names.insert(buffer.clone(), index);
                                data.push(AtomicFormulaPart::Variable(index));
                                buffer.clear();
                            }
                        }
                        loop {
                            let operator = stack.pop();
                            match operator {
                                None => {
                                    return Err(InvalidFormula {
                                        line: line_number,
                                        column,
                                        error: InvalidFormulaPart::ExtraParenthisies,
                                    });
                                }
                                Some(op) => match op {
                                    FormulaOperator::OpenParenthisies { line: _, column: _ } => {
                                        break;
                                    }
                                    FormulaOperator::And => {
                                        data.push(AtomicFormulaPart::And);
                                    }
                                    FormulaOperator::Not => {
                                        data.push(AtomicFormulaPart::Not);
                                    }
                                    FormulaOperator::Or => {
                                        data.push(AtomicFormulaPart::Or);
                                    }
                                    FormulaOperator::Implies => {
                                        let mut count = 1;
                                        let mut position: Option<usize> = None;
                                        for (index, element) in data.iter().rev().enumerate() {
                                            match element {
                                                AtomicFormulaPart::And => count += 2,
                                                AtomicFormulaPart::Constant(_) => count -= 1,
                                                AtomicFormulaPart::Not => count += 1,
                                                AtomicFormulaPart::Variable(_) => count -= 1,
                                                AtomicFormulaPart::Or => count += 2,
                                            };
                                            if count == 0 {
                                                position = Some(index);
                                                break;
                                            }
                                        }
                                        match position {
                                            Some(index) => {
                                                data.insert(index + 1, AtomicFormulaPart::Not);
                                                data.push(AtomicFormulaPart::Or);
                                            }
                                            None => {
                                                return Err(InvalidFormula {
                                                    line: line_number,
                                                    column,
                                                    error: InvalidFormulaPart::InvalidOperand(
                                                        FormulaPart::Not,
                                                    ),
                                                });
                                            }
                                        }
                                    }
                                },
                            }
                        }
                    }
                    _ => buffer.push(character),
                }
            }
        }
        if !buffer.is_empty() {
            if let Some(index) = names.get(&buffer) {
                data.push(AtomicFormulaPart::Variable(*index));
            } else {
                let index = names.len();
                names.insert(buffer.clone(), index);
                data.push(AtomicFormulaPart::Variable(index));
                buffer.clear();
            }
        }
        loop {
            let operator = stack.pop();
            match operator {
                None => {
                    break;
                }
                Some(op) => match op {
                    FormulaOperator::OpenParenthisies { line, column } => {
                        return Err(InvalidFormula {
                            line,
                            column,
                            error: InvalidFormulaPart::UnclosedParenthisies,
                        });
                    }
                    FormulaOperator::And => {
                        data.push(AtomicFormulaPart::And);
                    }
                    FormulaOperator::Not => {
                        data.push(AtomicFormulaPart::Not);
                    }
                    FormulaOperator::Or => {
                        data.push(AtomicFormulaPart::Or);
                    }
                    FormulaOperator::Implies => {
                        let mut count = 1;
                        let mut position: Option<usize> = None;
                        for (index, element) in data.iter().rev().enumerate() {
                            match element {
                                AtomicFormulaPart::And => count += 2,
                                AtomicFormulaPart::Constant(_) => count -= 1,
                                AtomicFormulaPart::Not => count += 1,
                                AtomicFormulaPart::Variable(_) => count -= 1,
                                AtomicFormulaPart::Or => count += 2,
                            };
                            if count == 0 {
                                position = Some(index);
                                break;
                            }
                        }
                        match position {
                            Some(index) => {
                                data.insert(index + 1, AtomicFormulaPart::Not);
                                data.push(AtomicFormulaPart::Or);
                            }
                            None => {
                                return Err(InvalidFormula {
                                    line: 0,
                                    column: 0,
                                    error: InvalidFormulaPart::InvalidOperand(FormulaPart::Not),
                                });
                            }
                        }
                    }
                },
            }
        }
        let mut out_names: Vec<String> = vec!["".to_string(); names.len()];
        for key in names.keys() {
            out_names[*names.get(key).unwrap()] = key.clone();
        }
        debug!("Got formula: {:?}", data);
        Ok(Formula {
            names: out_names,
            data: Arc::new(data),
        })
    }
}
