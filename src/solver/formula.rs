//! The Parts needed to solve a boolean sat problem

use log::{debug, trace};
use num_bigint::BigUint;
use num_traits::One;
use num_traits::Zero;
use rayon::iter::{ParallelBridge, ParallelIterator};
use std::collections::HashMap;
use std::error::Error;
use std::fmt::Display;
use std::ops::BitAnd;
use std::ops::BitOr;
use std::ops::Deref;
use std::ops::DerefMut;
use std::ops::Not;
// use std::sync::Arc; so far I have found that for large formulas the

/// A Value that could be a true or false
struct MaybeBool(Option<bool>);

impl Deref for MaybeBool {
    type Target = Option<bool>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for MaybeBool {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl Not for MaybeBool {
    type Output = Self;
    fn not(self) -> Self::Output {
        match *self {
            Some(v) => MaybeBool(Some(!v)),
            None => MaybeBool(None),
        }
    }
}

impl BitAnd for MaybeBool {
    type Output = MaybeBool;
    fn bitand(self, rhs: Self) -> Self::Output {
        match (*self, *rhs) {
            (Some(false), _) | (_, Some(false)) => MaybeBool(Some(false)),
            (Some(true), Some(true)) => MaybeBool(Some(true)),
            (Some(true), None) | (None, Some(true)) => MaybeBool(None),
            (None, None) => MaybeBool(None),
        }
    }
}

impl BitOr for MaybeBool {
    type Output = MaybeBool;
    fn bitor(self, rhs: Self) -> Self::Output {
        match (*self, *rhs) {
            (Some(true), _) | (_, Some(true)) => MaybeBool(Some(true)),
            (Some(false), Some(false)) => MaybeBool(Some(false)),
            (Some(false), None) | (None, Some(false)) => MaybeBool(None),
            (None, None) => MaybeBool(None),
        }
    }
}

impl MaybeBool {
    /// Unknown condition
    const fn unknown() -> Self {
        MaybeBool(None)
    }

    /// Condition is known
    const fn some(value: bool) -> Self {
        MaybeBool(Some(value))
    }

    /// For sat
    fn is_conflict(&self) -> bool {
        matches!(self.0, Some(false))
    }

    /// for sat
    fn is_satisfied(&self) -> bool {
        matches!(self.0, Some(true))
    }
}

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

#[derive(Clone, Copy)]
#[repr(u8)]
enum FormulaOperator {
    And,
    Or,
    Not,
    Implies,
    OpenParenthisies { line: usize, column: usize },
}

impl FormulaOperator {
    /// ordering of elements
    pub fn precedence(&self) -> usize {
        match self {
            FormulaOperator::OpenParenthisies { .. } => 0,
            FormulaOperator::Implies => 1, // lowest precedence
            FormulaOperator::Or => 2,
            FormulaOperator::And => 3,
            FormulaOperator::Not => 4, // highest precedence
        }
    }

    /// is the operand is right assosiate
    pub fn right_assosiate(&self) -> bool {
        matches!(self, FormulaOperator::Not | FormulaOperator::Implies)
    }
}

/// A Formula with names to varible position
#[derive(Debug)]
pub struct Formula {
    /// data stored in postfix
    data: Vec<AtomicFormulaPart>,
    /// named variables
    pub names: Vec<String>,
}

impl Formula {
    // /// Creates and empty formula
    // pub fn empty() -> Formula {
    //     Formula {
    //         names: Vec::new(),
    //         data: Vec::new(),
    //     }
    // }

    // /// a check to see if the formula is empty
    // pub fn is_empty(&self) -> bool {
    //     self.names.is_empty() && self.data.is_empty()
    // }

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
                    trace!(
                        "{} is {}",
                        self.names.get(*var).unwrap(),
                        stack.last().unwrap()
                    );
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

    /// deduce a SAT problem via CDCL-style deduction over postfix form
    pub fn deduce(&self) -> Option<BigUint> {
        let mut assignment: Vec<Option<bool>> = vec![None; self.names.len()];
        let mut decisions: Vec<(usize, bool)> = Vec::new();

        loop {
            let mut stack: Vec<MaybeBool> = Vec::with_capacity(self.data.len());
            for part in &self.data {
                match part {
                    AtomicFormulaPart::Variable(i) => stack.push(match assignment[*i] {
                        Some(b) => MaybeBool::some(b),
                        None => MaybeBool::unknown(),
                    }),
                    AtomicFormulaPart::Not => {
                        let a = stack.pop().unwrap();
                        stack.push(!a);
                    }
                    AtomicFormulaPart::And => {
                        let r = stack.pop().unwrap();
                        let l = stack.pop().unwrap();
                        stack.push(l & r);
                    }
                    AtomicFormulaPart::Or => {
                        let r = stack.pop().unwrap();
                        let l = stack.pop().unwrap();
                        stack.push(l | r);
                    }
                    AtomicFormulaPart::Constant(b) => stack.push(MaybeBool::some(*b)),
                }
            }

            let result = stack.pop().unwrap();

            if result.is_satisfied() {
                let mut bits = BigUint::zero();
                for bit in assignment.iter().rev() {
                    bits <<= 1;
                    if bit.unwrap_or(false) {
                        bits += BigUint::one();
                    }
                }
                return Some(bits);
            }

            if result.is_conflict() {
                if let Some((var, val)) = decisions.pop() {
                    assignment[var] = Some(!val);
                    continue;
                } else {
                    return None;
                }
            }

            if let Some(i) = assignment.iter().position(|a| a.is_none()) {
                assignment[i] = Some(true);
                decisions.push((i, true));
            } else {
                return None;
            }
        }
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
    line: isize,
    /// Column in the string the error occured on
    column: isize,
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
    InvalidOperand,
    ///
    TooFewOperands,
    ///
    TooManyOperands,
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
        let mut previous: Option<&FormulaOperator> = None;
        for (line_number, line) in value.lines().enumerate() {
            'reading: for (column, character) in line.chars().enumerate() {
                trace!("Testing: {}", character);
                trace!("Buffer: {}", buffer);
                if character.is_whitespace() {
                    trace!("Skipping");
                    continue;
                }
                match character {
                    '(' => {
                        // Push any pending variable in buffer first
                        if !buffer.is_empty() {
                            if buffer == "T".to_string() || buffer == "F".to_string() {
                                trace!("Pushing Constant: {}", buffer);
                                if buffer == "T".to_string() {
                                    data.push(AtomicFormulaPart::Constant(true));
                                } else {
                                    data.push(AtomicFormulaPart::Constant(false));
                                }

                                buffer.clear();
                            } else {
                                trace!("Pushing Variable: {}", buffer);
                                let l = names.len();
                                let index = *names.entry(buffer.clone()).or_insert(l);
                                data.push(AtomicFormulaPart::Variable(index));
                                buffer.clear();
                            }
                        }
                        stack.push(FormulaOperator::OpenParenthisies {
                            line: line_number,
                            column,
                        });
                        previous = stack.last();
                    }

                    ')' => {
                        if !buffer.is_empty() {
                            if buffer == "T".to_string() || buffer == "F".to_string() {
                                trace!("Pushing Constant: {}", buffer);
                                if buffer == "T".to_string() {
                                    data.push(AtomicFormulaPart::Constant(true));
                                } else {
                                    data.push(AtomicFormulaPart::Constant(false));
                                }

                                buffer.clear();
                            } else {
                                trace!("Pushing Variable: {}", buffer);
                                let l = names.len();
                                let index = *names.entry(buffer.clone()).or_insert(l);
                                data.push(AtomicFormulaPart::Variable(index));
                                buffer.clear();
                            }
                        }

                        // Pop until '('
                        while let Some(op) = stack.pop() {
                            match op {
                                FormulaOperator::OpenParenthisies { .. } => {
                                    previous = None;
                                    continue 'reading;
                                }
                                FormulaOperator::And => data.push(AtomicFormulaPart::And),
                                FormulaOperator::Or => data.push(AtomicFormulaPart::Or),
                                FormulaOperator::Not => data.push(AtomicFormulaPart::Not),
                                FormulaOperator::Implies => {
                                    data.push(AtomicFormulaPart::Or);
                                }
                            }
                        }
                        return Err(InvalidFormula {
                            line: line_number as isize + 1,
                            column: column as isize + 1,
                            error: InvalidFormulaPart::ExtraParenthisies,
                        });
                    }

                    '&' | '|' | '!' | '>' => {
                        if character != '!'
                            && let Some(prev) = previous
                        {
                            match prev {
                                FormulaOperator::And
                                | FormulaOperator::Or
                                | FormulaOperator::Implies
                                    if buffer.is_empty() =>
                                {
                                    return Err(InvalidFormula {
                                        line: line_number as isize + 1,
                                        column: column as isize + 1,
                                        error: InvalidFormulaPart::InvalidOperand,
                                    });
                                }
                                _ => {}
                            }
                        }

                        if !buffer.is_empty() {
                            if buffer == "T".to_string() || buffer == "F".to_string() {
                                trace!("Pushing Constant: {}", buffer);
                                if buffer == "T".to_string() {
                                    data.push(AtomicFormulaPart::Constant(true));
                                } else {
                                    data.push(AtomicFormulaPart::Constant(false));
                                }

                                buffer.clear();
                            } else {
                                trace!("Pushing Variable: {}", buffer);
                                let l = names.len();
                                let index = *names.entry(buffer.clone()).or_insert(l);
                                data.push(AtomicFormulaPart::Variable(index));
                                buffer.clear();
                            }
                        }

                        let current = match character {
                            '&' => FormulaOperator::And,
                            '|' => FormulaOperator::Or,
                            '!' => FormulaOperator::Not,
                            '>' => {
                                if let Some(element) = stack.last()
                                    && element.right_assosiate()
                                {
                                    match stack.pop().unwrap() {
                                        FormulaOperator::And => unreachable!(),
                                        FormulaOperator::Or => unreachable!(),
                                        FormulaOperator::Not => data.push(AtomicFormulaPart::Not),
                                        FormulaOperator::Implies => {
                                            data.push(AtomicFormulaPart::Or);
                                        }
                                        FormulaOperator::OpenParenthisies { .. } => unreachable!(),
                                    }
                                }
                                data.push(AtomicFormulaPart::Not);
                                FormulaOperator::Implies
                            }
                            _ => unreachable!(),
                        };

                        while let Some(top) = stack.last() {
                            let top_prec = top.precedence();
                            let curr_prec = current.precedence();

                            let should_pop = if current.right_assosiate() {
                                curr_prec < top_prec
                            } else {
                                curr_prec <= top_prec
                            };

                            if !should_pop {
                                break;
                            }

                            match stack.pop().unwrap() {
                                FormulaOperator::And => data.push(AtomicFormulaPart::And),
                                FormulaOperator::Or => data.push(AtomicFormulaPart::Or),
                                FormulaOperator::Not => data.push(AtomicFormulaPart::Not),
                                FormulaOperator::Implies => {
                                    data.push(AtomicFormulaPart::Or);
                                }
                                FormulaOperator::OpenParenthisies { .. } => break,
                            }
                        }

                        stack.push(current);

                        previous = Some(stack.last().unwrap());
                    }

                    _ => buffer.push(character),
                }
            }
        }
        if !buffer.is_empty() {
            if buffer == "T".to_string() || buffer == "F".to_string() {
                trace!("Pushing Constant: {}", buffer);
                if buffer == "T".to_string() {
                    data.push(AtomicFormulaPart::Constant(true));
                } else {
                    data.push(AtomicFormulaPart::Constant(false));
                }

                buffer.clear();
            } else {
                trace!("Pushing Variable: {}", buffer);
                let l = names.len();
                let index = *names.entry(buffer.clone()).or_insert(l);
                data.push(AtomicFormulaPart::Variable(index));
                buffer.clear();
            }
        }
        trace!("Backtracing!");
        while let Some(op) = stack.pop() {
            match op {
                FormulaOperator::OpenParenthisies { line, column } => {
                    // Any unclosed '(' is an error
                    return Err(InvalidFormula {
                        line: line as isize + 1,
                        column: column as isize + 1,
                        error: InvalidFormulaPart::UnclosedParenthisies,
                    });
                }

                FormulaOperator::And => {
                    data.push(AtomicFormulaPart::And);
                }

                FormulaOperator::Or => {
                    data.push(AtomicFormulaPart::Or);
                }

                FormulaOperator::Not => {
                    data.push(AtomicFormulaPart::Not);
                }

                FormulaOperator::Implies => {
                    data.push(AtomicFormulaPart::Or);
                }
            }
        }

        let mut out_names: Vec<String> = vec!["".to_string(); names.len()];
        for key in names.keys() {
            out_names[*names.get(key).unwrap()] = key.clone();
        }
        debug!("Got formula!");
        trace!("formula: {:?}", data);
        let mut total: usize = 0;
        for op in &data {
            match op {
                AtomicFormulaPart::Variable(_) | AtomicFormulaPart::Constant(_) => total += 1,
                AtomicFormulaPart::And | AtomicFormulaPart::Or => {
                    let new_total = total.checked_sub(1);
                    match new_total {
                        Some(x) => total = x,
                        None => {
                            return Err(InvalidFormula {
                                line: -1,
                                column: -1,
                                error: InvalidFormulaPart::TooManyOperands,
                            });
                        }
                    }
                }
                AtomicFormulaPart::Not => {
                    if total == 0 {
                        return Err(InvalidFormula {
                            line: -1,
                            column: -1,
                            error: InvalidFormulaPart::TooManyOperands,
                        });
                    }
                }
            }
        }
        if total != 1 {
            return Err(InvalidFormula {
                line: -1,
                column: -1,
                error: InvalidFormulaPart::TooFewOperands,
            });
        }
        Ok(Formula {
            names: out_names,
            data: data,
        })
    }
}

#[cfg(test)]
mod formula_tests {
    use super::*;
    use num_bigint::BigUint;
    use num_traits::{One, Zero};

    fn bool_to_biguint(bools: &[bool]) -> BigUint {
        // Converts [true, false, true] → bit pattern 101 (binary)
        bools.iter().rev().fold(BigUint::zero(), |acc, &bit| {
            (acc << 1) + if bit { BigUint::one() } else { BigUint::zero() }
        })
    }

    #[test]
    fn test_simple_and() {
        let formula = Formula::try_from("a&b".to_string()).unwrap();
        let a_both_true = bool_to_biguint(&[true, true]);
        let a_false = bool_to_biguint(&[false, true]);
        let b_false = bool_to_biguint(&[true, false]);

        assert!(formula.solve(&a_both_true));
        assert!(!formula.solve(&a_false));
        assert!(!formula.solve(&b_false));
    }

    #[test]
    fn test_simple_or() {
        let formula = Formula::try_from("a|b".to_string()).unwrap();
        let both_false = bool_to_biguint(&[false, false]);
        let one_true = bool_to_biguint(&[true, false]);
        let other_true = bool_to_biguint(&[false, true]);

        assert!(!formula.solve(&both_false));
        assert!(formula.solve(&one_true));
        assert!(formula.solve(&other_true));
    }

    #[test]
    fn test_not_operator() {
        let formula = Formula::try_from("!a".to_string()).unwrap();
        let a_true = bool_to_biguint(&[true]);
        let a_false = bool_to_biguint(&[false]);

        assert!(!formula.solve(&a_true));
        assert!(formula.solve(&a_false));
    }

    #[test]
    fn test_and_or_precedence() {
        // should parse as (a & b) | c
        let formula = Formula::try_from("a&b|c".to_string()).unwrap();

        let vals = [
            ([false, false, false], false),
            ([true, false, false], false),
            ([true, true, false], true),
            ([false, false, true], true),
        ];

        for (input, expected) in vals {
            let vars = bool_to_biguint(&input);
            assert_eq!(formula.solve(&vars), expected, "failed on {:?}", input);
        }
    }

    #[test]
    fn test_or_and_precedence() {
        // should parse as a | (b & c)
        let formula = Formula::try_from("a|b&c".to_string()).unwrap();

        let vals = [
            ([false, false, false], false),
            ([false, true, false], false),
            ([false, true, true], true),
            ([true, false, false], true),
        ];

        for (input, expected) in vals {
            let vars = bool_to_biguint(&input);
            assert_eq!(formula.solve(&vars), expected, "failed on {:?}", input);
        }
    }

    #[test]
    fn test_double_not() {
        let formula = Formula::try_from("!!a".to_string()).unwrap();
        let a_true = bool_to_biguint(&[true]);
        let a_false = bool_to_biguint(&[false]);
        assert!(formula.solve(&a_true));
        assert!(!formula.solve(&a_false));
    }

    #[test]
    fn test_implies_basic() {
        // a > b  means (!a) | b
        let formula = Formula::try_from("a>b".to_string()).unwrap();

        let vals = [
            ([false, false], true), // ¬a ⇒ true
            ([false, true], true),
            ([true, false], false),
            ([true, true], true),
        ];

        for (input, expected) in vals {
            let vars = bool_to_biguint(&input);
            assert_eq!(formula.solve(&vars), expected, "failed on {:?}", input);
        }
    }

    #[test]
    fn test_implies_chain() {
        // (a > b) > c → (!(!a | b)) | c → (a & !b) | c
        let formula = Formula::try_from("a>b>c".to_string()).unwrap();

        let vals = [
            ([false, false, false], false),
            ([true, false, false], true),
            ([true, false, true], true),
            ([true, true, false], false),
        ];

        for (input, expected) in vals {
            let vars = bool_to_biguint(&input);
            assert_eq!(formula.solve(&vars), expected, "failed on {:?}", input);
        }
    }

    #[test]
    fn test_nested_complex() {
        // (!(a & b)) | (c & (a > b))
        let formula = Formula::try_from("!(a&b)|c&(a>b)".to_string()).unwrap();

        let vals = [
            // c     b       a
            ([false, false, false], true),
            ([true, false, false], true),
            ([true, true, false], false),
            ([true, false, true], true),
        ];

        for (input, expected) in vals {
            let vars = bool_to_biguint(&input);
            assert_eq!(formula.solve(&vars), expected, "failed on {:?}", input);
        }
    }

    #[test]
    fn test_parentheses_override() {
        // a | b & c normally parses as a | (b & c)
        // but here parentheses force (a | b) & c
        let formula = Formula::try_from("(a|b)&c".to_string()).unwrap();

        let vals = [
            ([false, false, false], false),
            ([true, false, false], false),
            ([false, true, false], false),
            ([true, true, true], true),
            ([true, false, true], true),
            ([false, true, true], true),
        ];

        for (input, expected) in vals {
            assert_eq!(
                formula.solve(&bool_to_biguint(&input)),
                expected,
                "failed on {:?}",
                input
            );
        }
    }

    #[test]
    fn test_nested_parentheses() {
        let formula = Formula::try_from("((a&b)|(!c))>d".to_string()).unwrap();

        let vals = [
            //  d     c     b       a
            ([false, false, false, false], false),
            ([true, true, false, false], false),
            ([true, true, true, true], true),
            ([false, true, false, true], true),
        ];

        for (input, expected) in vals {
            assert_eq!(
                formula.solve(&bool_to_biguint(&input)),
                expected,
                "Expected: {} from: {:?}",
                expected,
                input
            );
        }
    }

    #[test]
    fn test_tautology_and_contradiction() {
        let taut = Formula::try_from("a|!a".to_string()).unwrap();
        let contradiction = Formula::try_from("a&!a".to_string()).unwrap();

        for val in [true, false] {
            let input = bool_to_biguint(&[val]);
            assert!(taut.solve(&input));
            assert!(!contradiction.solve(&input));
        }
    }

    #[test]
    fn test_whitespace_tolerance() {
        let spaced = Formula::try_from(" ( a  &  b )  |  ! c ".to_string()).unwrap();
        let compact = Formula::try_from("(a&b)|!c".to_string()).unwrap();

        for input in [
            [false, false, false],
            [true, true, false],
            [false, true, true],
            [true, false, true],
        ] {
            let vars = bool_to_biguint(&input);
            assert_eq!(spaced.solve(&vars), compact.solve(&vars));
        }
    }

    #[test]
    fn test_complex_chain_mixed() {
        // a > b & (c | !d)
        let formula = Formula::try_from("a>b&(c|!d)".to_string()).unwrap();

        let vals = [
            ([false, false, false, false], true),
            ([true, false, true, false], false),
            ([true, false, false, false], false),
            ([true, true, false, true], false),
        ];

        for (input, expected) in vals {
            let vars = bool_to_biguint(&input);
            assert_eq!(formula.solve(&vars), expected, "failed on {:?}", input);
        }
    }

    #[test]
    fn test_repeated_variables() {
        let formula = Formula::try_from("a & (a | !a)".to_string()).unwrap();

        let vals = [([false], false), ([true], true)];

        for (input, expected) in vals {
            assert_eq!(formula.solve(&bool_to_biguint(&input)), expected);
        }
    }

    #[test]
    fn test_long_chain_of_variables() {
        // Ensure parser handles more than a few variables
        let formula = Formula::try_from("a&b&c&d&e".to_string()).unwrap();
        let all_true = bool_to_biguint(&[true, true, true, true, true]);
        let one_false = bool_to_biguint(&[true, true, false, true, true]);

        assert!(formula.solve(&all_true));
        assert!(!formula.solve(&one_false));
    }

    fn run_deduction_test(size: usize) {
        let data =
            std::fs::read_to_string(format!("sat_formulas/sat_{size}x{size}_expression.txt"))
                .expect("Unable to read file");
        let parser = Formula::try_from(data).unwrap();
        assert!(
            parser.deduce().is_some_and(|x| parser.solve(&x)),
            "Failed on: {}",
            size
        );
    }

    #[test]
    fn deduction_correctly_finds_satisabillity_2() {
        run_deduction_test(2);
    }
    #[test]
    fn deduction_correctly_finds_satisabillity_3() {
        run_deduction_test(3);
    }
    #[test]
    fn deduction_correctly_finds_satisabillity_4() {
        run_deduction_test(4);
    }
    #[test]
    fn deduction_correctly_finds_satisabillity_5() {
        run_deduction_test(5);
    }
    #[test]
    fn deduction_correctly_finds_satisabillity_6() {
        run_deduction_test(6);
    }
    #[test]
    fn deduction_correctly_finds_satisabillity_7() {
        run_deduction_test(7);
    }
    #[test]
    fn deduction_correctly_finds_satisabillity_8() {
        run_deduction_test(8);
    }
    #[test]
    fn deduction_correctly_finds_satisabillity_9() {
        run_deduction_test(9);
    }
    #[test]
    fn deduction_correctly_finds_satisabillity_10() {
        run_deduction_test(10);
    }
    #[test]
    fn deduction_correctly_finds_satisabillity_11() {
        run_deduction_test(11);
    }
    #[test]
    fn deduction_correctly_finds_satisabillity_12() {
        run_deduction_test(12);
    }
    #[test]
    fn deduction_correctly_finds_satisabillity_13() {
        run_deduction_test(13);
    }
    #[test]
    fn deduction_correctly_finds_satisabillity_14() {
        run_deduction_test(14);
    }
    #[test]
    fn deduction_correctly_finds_satisabillity_15() {
        run_deduction_test(15);
    }
    #[test]
    fn deduction_correctly_finds_satisabillity_16() {
        run_deduction_test(16);
    }
    #[test]
    fn deduction_correctly_finds_satisabillity_17() {
        run_deduction_test(17);
    }
    #[test]
    fn deduction_correctly_finds_satisabillity_18() {
        run_deduction_test(18);
    }
    #[test]
    fn deduction_correctly_finds_satisabillity_19() {
        run_deduction_test(19);
    }
    #[test]
    fn deduction_correctly_finds_satisabillity_20() {
        run_deduction_test(20);
    }

    #[test]
    fn deduction_correctly_detects_unsatisfiable_formula() {
        // This is a simple contradiction: (a AND !a)
        let data = "a & !a";
        let parser = Formula::try_from(data.to_string()).unwrap();

        // Expect `deduce()` to return None because the formula is unsatisfiable
        assert!(
            parser.deduce().is_none(),
            "Expected unsatisfiable formula to return None"
        );
    }

    #[test]
    fn deduction_detects_unsatisfiable_complex_formula() {
        // Example: (a OR b) AND (!a OR !b) AND (a) AND (b)
        // This forces a=true and b=true, but then (!a OR !b) becomes false → unsatisfiable
        let data = "(a | b) & (!a | !b) & a & b";
        let parser = Formula::try_from(data.to_string()).unwrap();

        assert!(
            parser.deduce().is_none(),
            "Expected complex unsatisfiable formula to return None"
        );
    }
}
