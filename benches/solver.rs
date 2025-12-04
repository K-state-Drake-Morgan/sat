#![allow(missing_docs)]

//! Benchmarking the SAT solvers: full vs. deduction-based.

use std::path::PathBuf;

use criterion::{BenchmarkId, Criterion, SamplingMode, criterion_group, criterion_main};
use sat::{self, from_cnf, solver::formula::Formula};

/// Benchmarks both the full solver and the deduction solver for comparison.
pub fn bench_solver_comparison(c: &mut Criterion) {
    let mut group = c.benchmark_group("SAT Solver Comparison");

    for size in 2..24 {
        let data =
            std::fs::read_to_string(format!("sat_formulas/sat_{size}x{size}_expression.txt"))
                .expect("Unable to read file");
        let parser = Formula::try_from(data).unwrap();

        // Adjust sample size and duration by problem size
        let (csize, target_time) = if size < 10 {
            (30, std::time::Duration::from_secs(5))
        } else if size < 15 {
            (15, std::time::Duration::from_secs(3))
        } else {
            (10, std::time::Duration::from_secs(1))
        };

        group
            .sample_size(csize)
            .measurement_time(target_time)
            .sampling_mode(SamplingMode::Flat);

        // --- Bench full solver ---
        group.bench_with_input(
            BenchmarkId::new("fully_solve", size),
            &parser,
            |b, parser| {
                b.iter(|| {
                    std::hint::black_box(parser.fully_solve());
                });
            },
        );

        // --- Bench deduction solver ---
        group.bench_with_input(BenchmarkId::new("deduce", size), &parser, |b, parser| {
            b.iter(|| {
                std::hint::black_box(parser.deduce());
            });
        });
    }

    for size in 2..24 {
        let cnf = from_cnf(&PathBuf::from(format!(
            "sat_formulas/unsat_24x{size}_cnf.cnf"
        )));
        let parser = Formula::try_from(cnf).unwrap();

        group
            .sample_size(5)
            .measurement_time(std::time::Duration::from_secs(10))
            .sampling_mode(SamplingMode::Flat);

        // commented this out to avoid infinite bench time
        // group.bench_with_input(
        //     BenchmarkId::new("unsat_fully_solve", size),
        //     &parser,
        //     |b, parser| {
        //         b.iter(|| parser.fully_solve());
        //     },
        // );

        group.bench_with_input(
            BenchmarkId::new("unsat_deduce", size),
            &parser,
            |b, parser| {
                b.iter(|| parser.deduce());
            },
        );
    }

    group.finish();
}

pub fn bench_parser(c: &mut Criterion) {
    let mut group = c.benchmark_group("Get Sat Equation");

    for size in 2..24 {
        let data =
            std::fs::read_to_string(format!("sat_formulas/sat_{size}x{size}_expression.txt"))
                .expect("Unable to read file");

        // Adjust sample size and duration by problem size
        let (csize, target_time) = if size < 10 {
            (30, std::time::Duration::from_secs(5))
        } else if size < 15 {
            (15, std::time::Duration::from_secs(3))
        } else {
            (10, std::time::Duration::from_secs(1))
        };

        group
            .sample_size(csize)
            .measurement_time(target_time)
            .sampling_mode(SamplingMode::Flat);

        // --- Bench full solver ---
        group.bench_with_input(BenchmarkId::new("NxN Parsing", size), &data, |b, data| {
            b.iter(|| {
                std::hint::black_box(
                    Formula::try_from(data.clone()).expect(
                        "Something In Testing Failed as we are unable to bench this Parser",
                    ),
                );
            });
        });
    }

    for size in 2..24 {
        let data = from_cnf(&PathBuf::from(format!(
            "sat_formulas/unsat_24x{size}_cnf.cnf"
        )));

        // Adjust sample size and duration by problem size
        let (csize, target_time) = if size < 10 {
            (30, std::time::Duration::from_secs(5))
        } else if size < 15 {
            (15, std::time::Duration::from_secs(3))
        } else {
            (10, std::time::Duration::from_secs(1))
        };

        group
            .sample_size(csize)
            .measurement_time(target_time)
            .sampling_mode(SamplingMode::Flat);

        // --- Bench full solver ---
        group.bench_with_input(
            BenchmarkId::new("24xN Unsat Parsing", size),
            &data,
            |b, data| {
                b.iter(|| {
                    std::hint::black_box(Formula::try_from(data.clone()).expect(
                        "Something In Testing Failed as we are unable to bench this Parser",
                    ));
                });
            },
        );
    }

    group.finish();
}

criterion_group!(benches, bench_parser, bench_solver_comparison);
criterion_main!(benches);
