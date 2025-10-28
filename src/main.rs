//! Command to solve a sat problem

use clap::{Parser, ValueEnum};
use log::{info, warn};
use std::path::PathBuf;

pub mod solver;
use solver::formula::Formula;
use solver::parser::Sentance;

/// Configuration for running this command
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

    /// Where to send the output, on non just use the terminal out
    #[arg(short, long)]
    output: Option<PathBuf>,

    #[command(flatten)]
    verbosity: clap_verbosity_flag::Verbosity,

    /// A Satisfiability Problem
    #[arg(group = "sat_problem")]
    problem: Option<String>,
}

/// The user interface to use
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

/// The user only cares about the output, so only work on that
fn main_cli(contents: String) {
    let s = Sentance::from(contents);
    let f = Formula::try_from(s).unwrap();
    if let Some(result) = f.fully_solve() {
        println!("{:0width$b} is True", result, width = f.operands());
    } else {
        println!("Continuety");
    }
}

fn main() -> color_eyre::Result<()> {
    color_eyre::install()?;

    let args = Arguments::parse();

    env_logger::Builder::new()
        .filter_level(args.verbosity.into())
        .init();

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
