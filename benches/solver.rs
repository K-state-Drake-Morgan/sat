#![allow(missing_docs)]

//! benching
use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};

use sat::{self, solver::formula::Formula};

/// Bench fully solving a problem that allways has a true ness
pub fn bench_full_solver(c: &mut Criterion) {
    let mut full_sat_group = c.benchmark_group("Full Sat Solver");

    for size in 2..=20 {
        let data =
            std::fs::read_to_string(format!("sat_formulas/sat_{size}x{size}_expression.txt"))
                .expect("Unable to read file");

        let parser = Formula::try_from(data).unwrap();

        let csize;
        // Reduce Criterion's own measurement time for large inputs
        let target_time = if size < 10 {
            csize = 30;
            std::time::Duration::from_secs(5)
        } else if size < 15 {
            csize = 15;
            std::time::Duration::from_secs(3)
        } else {
            csize = 10;
            std::time::Duration::from_secs(1)
        };

        full_sat_group
            .sample_size(csize) // fewer samples → faster
            .measurement_time(target_time) // shorter runs for large cases
            .sampling_mode(criterion::SamplingMode::Flat);

        full_sat_group.bench_function(BenchmarkId::from_parameter(size), |b| {
            b.iter(|| {
                std::hint::black_box(parser.fully_solve());
            });
        });
    }

    full_sat_group.finish();
}

criterion_group!(benches, bench_full_solver);
criterion_main!(benches);
