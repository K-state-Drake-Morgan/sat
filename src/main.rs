use clap::{Parser, ValueEnum};
use log::{info, warn};
use num_bigint::BigUint;
use num_traits::identities::Zero;
use rayon::iter::{ParallelBridge, ParallelIterator};
use std::{collections::HashMap, path::PathBuf};

#[derive(Debug, PartialEq, Eq)]
enum FormulaPart {
    And,
    Or,
    Not,
    Implies,
    Variable(usize), // using usize as identifier, will use hashmap to go from string to ussize
                     // The usize is the 2^n for a big int for use to bit mask
}

#[derive(Debug)]
struct UnReadableError;

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
struct Formula {
    /// stored in postfix
    data: Vec<FormulaPart>,
    names: HashMap<String, usize>,
}

impl Formula {
    /// panics if the formula is nonsensical
    fn solve(&self, variables: &BigUint) -> bool {
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

    fn fully_solve(&self) {
        let one: BigUint = BigUint::from(1_u8);
        let to = one << self.names.len();
        let zero = BigUint::from(0_u8);
        num_iter::range(zero, to)
            .into_iter()
            .par_bridge()
            .for_each(|x| {
                println!(
                    "{:0width$b} | {}",
                    x,
                    self.solve(&x),
                    width = self.names.len()
                );
            });
    }
}

#[derive(Debug)]
enum FormulaFromSentanceError {}

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
mod FormulaTests {
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

enum HumanOperator {
    And,
    Or,
    Not,
    Implies, // becomes not a or b
    Variable(String),
    OpeningParenthesis,
    ClosingParenthesis,
    OpeningBracket,
    ClosingBracket,
    OpeningCurly,
    ClosingCurly,
}

impl HumanOperator {
    fn precedence(&self) -> usize {
        match self {
            HumanOperator::Variable(_) => 0,
            HumanOperator::Not => 1,
            HumanOperator::And => 2,
            HumanOperator::Or => 3,
            HumanOperator::Implies => 4,
            _ => usize::MAX,
        }
    }

    fn is_right_associative(&self) -> bool {
        matches!(self, HumanOperator::Implies | HumanOperator::Not)
    }
}

struct Sentance {
    data: Vec<HumanOperator>,
}

impl From<String> for Sentance {
    fn from(value: String) -> Self {
        let mut data = Vec::new();
        let mut buffer = String::new();

        for ch in value.chars() {
            match ch {
                '(' => {
                    push_buffer(&mut buffer, &mut data);
                    data.push(HumanOperator::OpeningParenthesis);
                }
                ')' => {
                    push_buffer(&mut buffer, &mut data);
                    data.push(HumanOperator::ClosingParenthesis);
                }
                '[' => {
                    push_buffer(&mut buffer, &mut data);
                    data.push(HumanOperator::OpeningBracket);
                }
                ']' => {
                    push_buffer(&mut buffer, &mut data);
                    data.push(HumanOperator::ClosingBracket);
                }
                '{' => {
                    push_buffer(&mut buffer, &mut data);
                    data.push(HumanOperator::OpeningCurly);
                }
                '}' => {
                    push_buffer(&mut buffer, &mut data);
                    data.push(HumanOperator::ClosingCurly);
                }

                '|' => {
                    push_buffer(&mut buffer, &mut data);
                    data.push(HumanOperator::Or);
                }
                '&' => {
                    push_buffer(&mut buffer, &mut data);
                    data.push(HumanOperator::And);
                }
                '!' => {
                    push_buffer(&mut buffer, &mut data);
                    data.push(HumanOperator::Not);
                }
                '>' => {
                    push_buffer(&mut buffer, &mut data);
                    data.push(HumanOperator::Implies);
                }

                ' ' => {
                    push_buffer(&mut buffer, &mut data);
                }

                _ => buffer.push(ch),
            }
        }

        push_buffer(&mut buffer, &mut data);

        Sentance { data }
    }
}

fn push_buffer(buffer: &mut String, data: &mut Vec<HumanOperator>) {
    if buffer.is_empty() {
        return;
    }

    let token = buffer.trim().to_lowercase();
    let op = match token.as_str() {
        "and" => HumanOperator::And,
        "or" => HumanOperator::Or,
        "not" => HumanOperator::Not,
        "implies" => HumanOperator::Implies,
        _ => HumanOperator::Variable(token),
    };
    data.push(op);
    buffer.clear();
}

#[derive(Parser, Debug)]
#[command(
    version,
    about = "Check if a given SAT (satisfiability) problem can be satisfied",
    long_about = "A command-line tool that evaluates whether a propositional logic formula represents a satisfiable problem"
)]
struct Arguments {
    /// What interface to interact with the program
    #[arg(short, long, value_enum, default_value_t = Interface::CLI)]
    interface: Interface,

    /// File containing a Satisfiability Problem
    #[arg(short, long, group = "sat_problem")]
    file: Option<PathBuf>,

    /// A Satisfiability Problem
    #[arg(group = "sat_problem")]
    problem: Option<String>,
}

#[derive(Debug, Clone, Copy, Default, ValueEnum, PartialEq, Eq)]
#[clap(rename_all = "lower")]
enum Interface {
    #[clap(alias = "g", alias = "GUI", help = "Use the graphical user interface")]
    GUI,
    #[clap(alias = "t", alias = "TUI", help = "Use the terminal interface")]
    TUI,
    #[default]
    #[clap(alias = "c", alias = "CLI", help = "Use the command-line interface")]
    CLI,
}

fn main_cli(contents: String) {
    let s = Sentance::from(contents);
    let f = Formula::try_from(s).unwrap();
    dbg!(&f);
    f.fully_solve();
}

fn main() -> color_eyre::Result<()> {
    color_eyre::install()?;

    env_logger::init();

    let args = Arguments::parse();

    match args.interface {
        Interface::CLI => {
            let input_contents = match (&args.file, &args.problem) {
                // I don't know when this became unneeded du to error: the argument '--file <FILE>' cannot be used with '[PROBLEM]' but I'll keep it here incase things change
                (Some(file_path), Some(problem_str)) => {
                    if file_path.exists() && file_path.is_file() {
                        info!(
                            "Both file and problem provided; using file at {:?}",
                            file_path
                        );
                        std::fs::read_to_string(file_path)?
                    } else {
                        warn!(
                            "File {:?} does not exist; using problem string instead",
                            file_path
                        );
                        problem_str.clone()
                    }
                }
                (Some(file_path), None) => {
                    if file_path.exists() && file_path.is_file() {
                        std::fs::read_to_string(file_path)?
                    } else {
                        eprintln!(
                            "Error: File {:?} does not exist or is not a valid file.",
                            file_path
                        );
                        std::process::exit(1);
                    }
                }
                (None, Some(problem_str)) => problem_str.clone(),
                (None, None) => {
                    // Neither provided
                    eprintln!("Error: Must provide either --file <path> or --problem <string>.");
                    std::process::exit(1);
                }
            };

            main_cli(input_contents);
        }
        Interface::TUI => {} // ratatui
        Interface::GUI => {} // egui works for this
    }

    Ok(())
}
