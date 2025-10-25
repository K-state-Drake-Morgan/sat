use super::parser::{HumanOperator, Sentance};
use num_bigint::BigUint;
use num_traits::Zero;
use rayon::iter::{ParallelBridge, ParallelIterator};
use std::collections::HashMap;

#[derive(Debug, PartialEq, Eq)]
pub enum FormulaPart {
    And,
    Or,
    Not,
    Implies,
    Variable(usize), // using usize as identifier, will use hashmap to go from string to ussize
                     // The usize is the 2^n for a big int for use to bit mask
}

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

#[derive(Debug)]
pub struct Formula {
    /// stored in postfix
    data: Vec<FormulaPart>,
    names: HashMap<String, usize>,
}

impl Formula {
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
            }
        }

        assert_eq!(stack.len(), 1, "formula not fully reduced");
        stack.pop().unwrap()
    }

    pub fn fully_solve(&self) -> Option<BigUint> {
        let one: BigUint = BigUint::from(1_u8);
        let to = one << self.names.len();
        let zero = BigUint::from(0_u8);
        num_iter::range(zero, to)
            .into_iter()
            .par_bridge()
            .find_any(|x| {
                return self.solve(&x);
            })
    }
}

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
            data: output,
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
                == vec![
                    FormulaPart::Variable(0),
                    FormulaPart::Variable(1),
                    FormulaPart::Not,
                    FormulaPart::And,
                    FormulaPart::Variable(2),
                    FormulaPart::Or
                ]
        );
    }
}
