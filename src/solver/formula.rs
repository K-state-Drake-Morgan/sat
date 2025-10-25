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
    Constant(bool), // for clause elimination
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
        println!(
            "Tried: {:0width$b} and got: {}",
            variables,
            result,
            width = self.names.len()
        );
        result
    }

    pub fn fully_solve(&self) -> Option<BigUint> {
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
                    let right = stack.pop().expect("Nothing to pop");
                    let left = stack.pop().expect("Nothing to pop");
                    if let FormulaPart::Variable(x) = left {
                        if let Some(value) = should_values.get(&x)
                            && *value != false
                        {
                            should_values.insert(x, true);
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
