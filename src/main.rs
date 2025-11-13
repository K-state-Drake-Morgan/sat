//! Command to solve a sat problem

use clap::{Parser, ValueEnum};
use log::{info, warn};
use num_bigint::BigUint;
use num_traits::One;
use num_traits::Zero;
use std::path::PathBuf;
use tracing::trace;

mod solver;
use solver::formula::Formula;

mod tui;

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

    /// If we shoud deduce the anwser using CDCL or brute force it
    #[arg(short, long)]
    deduce: bool,

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
fn main_cli(args: Arguments) {
    trace!("Getting formulas");
    let input_contents = match (&args.file, &args.problem) {
        (Some(file_path), Some(problem_str)) => {
            if file_path.exists() && file_path.is_file() {
                warn!(
                    "Both file and problem provided; using file at {:?}",
                    file_path
                );
                std::fs::read_to_string(file_path).expect("Unable to read file path")
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
                std::fs::read_to_string(file_path).expect("Unable to read file path")
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
            eprintln!("Error: Must provide either --file <path> or --problem <string>.");
            std::process::exit(1);
        }
    };

    info!("Creating formula");
    let f = Formula::try_from(input_contents).unwrap();
    info!("Solving");
    let output = if args.deduce {
        f.deduce()
    } else {
        f.fully_solve()
    };

    if let Some(result) = output {
        let mut headers = String::new();
        for name in &f.names {
            headers.push_str(&format!("{}\t", name));
        }
        println!("{}", headers.trim_end());

        let mut values = String::new();
        for i in 0..f.operands() {
            let bit = (result.clone() >> i) & BigUint::one();
            let val = if bit == BigUint::one() {
                "true"
            } else {
                "false"
            };
            values.push_str(&format!("{}\t", val));
        }
        println!("{}", values.trim_end());
    } else {
        println!("Unsatisfiable");
    }
}

fn main_tui(args: Arguments) {
    let input_contents = match (&args.file, &args.problem) {
        (Some(file_path), Some(problem_str)) => {
            if file_path.exists() && file_path.is_file() {
                warn!(
                    "Both file and problem provided; using file at {:?}",
                    file_path
                );
                std::fs::read_to_string(file_path).expect("Unable to read file path")
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
                std::fs::read_to_string(file_path).expect("Unable to read file path")
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
            "".to_string()
        }
    };
    let terminal = ratatui::init();
    let _ = tui::run(terminal, input_contents);
    ratatui::restore();
}

fn main_gui(args: Arguments) {
    let mut sat_formula_string = match (&args.file, &args.problem) {
        (Some(file_path), Some(problem_str)) => {
            if file_path.exists() && file_path.is_file() {
                warn!(
                    "Both file and problem provided; using file at {:?}",
                    file_path
                );
                std::fs::read_to_string(file_path).expect("Unable to read file path")
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
                std::fs::read_to_string(file_path).expect("Unable to read file path")
            } else {
                eprintln!(
                    "Error: File {:?} does not exist or is not a valid file.",
                    file_path
                );
                std::process::exit(1);
            }
        }
        (None, Some(problem_str)) => problem_str.clone(),
        (None, None) => "(a|b)>(b&c)".to_owned(),
    };

    let options = eframe::NativeOptions {
        viewport: egui::ViewportBuilder::default().with_inner_size([480.0, 400.0]),
        ..Default::default()
    };

    let mut last_solve: Option<BigUint> = None;
    let mut last_formula: Option<Formula> = None;
    let mut last_error: Option<String> = None;

    let _ = eframe::run_simple_native("SAT Solver GUI", options, move |ctx, _frame| {
        egui::CentralPanel::default().show(ctx, |ui| {
            ui.heading("SAT Solver");
            ui.separator();

            ui.label(
                "Enter boolean formula (use a,b,c,... and operators |, &, !, >, parentheses):",
            );

            // Stretch horizontally: fill the available width
            // Give it a fixed or flexible height if you want
            egui::ScrollArea::vertical()
                .id_salt("Sat Equation")
                .max_height(150.0)
                .show(ui, |ui| {
                    ui.add_sized(
                        ui.available_size(),
                        egui::TextEdit::multiline(&mut sat_formula_string),
                    );
                });

            ui.horizontal(|ui| {
                if ui.button("Solve").clicked() {
                    match Formula::try_from(sat_formula_string.clone()) {
                        Ok(f) => {
                            last_error = None;
                            last_solve = f.fully_solve();
                            last_formula = Some(f);
                        }
                        Err(e) => {
                            last_error = Some(format!("{}", e));
                            last_formula = None;
                        }
                    }
                }

                if ui.button("Deduce").clicked() {
                    match Formula::try_from(sat_formula_string.clone()) {
                        Ok(f) => {
                            last_error = None;
                            last_solve = f.deduce();
                            last_formula = Some(f);
                        }
                        Err(e) => {
                            last_error = Some(format!("{}", e));
                            last_formula = None;
                        }
                    }
                }
            });

            ui.separator();

            if let Some(err) = &last_error {
                ui.colored_label(egui::Color32::RED, format!("Error: {}", err));
            }

            // --- Output area fills remaining space ---
            egui::ScrollArea::vertical()
                .id_salt("Sat Table")
                .show(ui, |ui| {
                    ui.set_min_height(ui.available_height()); // <- ensures it expands

                    if let Some(result) = &last_solve {
                        if result.is_zero() {
                            ui.colored_label(egui::Color32::LIGHT_RED, "Unsatisfiable");
                        } else {
                            ui.colored_label(egui::Color32::GREEN, "Satisfiable");
                        }

                        if let Some(formula) = &last_formula {
                            ui.separator();
                            ui.label("Variable assignments:");
                            if result.is_zero() {
                                ui.label("No satisfying assignment found.");
                            } else {
                                let bits_str = format!("{:0b}", result);
                                let mut bits: Vec<char> = bits_str.chars().rev().collect();
                                while bits.len() < formula.names.len() {
                                    bits.push('0');
                                }
                                for (i, name) in formula.names.iter().enumerate() {
                                    let bit = bits[i];
                                    let val = if bit == '1' { "true" } else { "false" };
                                    ui.label(format!("{} = {}", name, val));
                                }
                            }
                        }
                    } else if last_formula.is_some() {
                        ui.colored_label(
                            egui::Color32::YELLOW,
                            "No result yet — click Solve or Deduce.",
                        );
                    }
                });
        });
    });
}

fn main() -> color_eyre::Result<()> {
    color_eyre::install()?;

    let args = Arguments::parse();

    env_logger::Builder::new()
        .filter_level(args.verbosity.into())
        .init();

    match args.interface {
        Interface::CLI => {
            main_cli(args);
        }
        Interface::TUI => {
            main_tui(args);
        } // ratatui
        Interface::GUI => {
            main_gui(args);
        } // egui works for this
    }

    Ok(())
}
