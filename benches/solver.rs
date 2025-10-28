#![allow(missing_docs)]

//! benching
use criterion::{Criterion, criterion_group, criterion_main};

use sat::{
    self,
    solver::{formula::Formula, parser::Sentance},
};

/// Bench fully solving a problem that allways has a true ness
pub fn bench_full_solver(c: &mut Criterion) {
    let mut full_sat_group = c.benchmark_group("Full Sat Solver");

    for size in 2..=26 {
        let data: String =
            std::fs::read_to_string(format!("sat_formulas/sat_{size}x{size}_expression.txt"))
                .expect("Unable to read file");
        let human_sentace = Sentance::from(data);
        let parser = Formula::try_from(human_sentace).unwrap();
        full_sat_group.bench_function(format!("{size}x{size}"), |b| {
            b.iter(|| {
                std::hint::black_box(for _ in 2..=100 {
                    parser.fully_solve();
                })
            });
        });
    }
}

criterion_group!(benches, bench_full_solver);
criterion_main!(benches);
