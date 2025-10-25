use criterion::{Criterion, criterion_group, criterion_main};

use sat::{
    self,
    solver::{formula::Formula, parser::Sentance},
};

fn bench_full_solver(c: &mut Criterion) {
    let data: String = include_str!("../sat_formulas/sat_2x2_expression.txt").to_string();
    let human_sentace = Sentance::from(data);
    let parser = Formula::try_from(human_sentace).unwrap();
    let mut full_sat_group = c.benchmark_group("Full Sat Solver");
    full_sat_group.bench_function("2x2", |b| {
        b.iter(|| {
            std::hint::black_box(for _ in 1..=100 {
                parser.fully_solve();
            })
        });
    });

    let data: String = include_str!("../sat_formulas/sat_3x3_expression.txt").to_string();
    let human_sentace = Sentance::from(data);
    let parser = Formula::try_from(human_sentace).unwrap();
    full_sat_group.bench_function("3x3", |b| {
        b.iter(|| {
            std::hint::black_box(for _ in 2..=100 {
                parser.fully_solve();
            })
        });
    });

    let data: String = include_str!("../sat_formulas/sat_4x4_expression.txt").to_string();
    let human_sentace = Sentance::from(data);
    let parser = Formula::try_from(human_sentace).unwrap();
    full_sat_group.bench_function("4x4", |b| {
        b.iter(|| {
            std::hint::black_box(for _ in 1..=100 {
                parser.fully_solve();
            })
        });
    });

    let data: String = include_str!("../sat_formulas/sat_5x5_expression.txt").to_string();
    let human_sentace = Sentance::from(data);
    let parser = Formula::try_from(human_sentace).unwrap();
    full_sat_group.bench_function("5x5", |b| {
        b.iter(|| {
            std::hint::black_box(for _ in 1..=100 {
                parser.fully_solve();
            })
        });
    });

    let data: String = include_str!("../sat_formulas/sat_6x6_expression.txt").to_string();
    let human_sentace = Sentance::from(data);
    let parser = Formula::try_from(human_sentace).unwrap();
    full_sat_group.bench_function("6x6", |b| {
        b.iter(|| {
            std::hint::black_box(for _ in 1..=100 {
                parser.fully_solve();
            })
        });
    });

    let data: String = include_str!("../sat_formulas/sat_7x7_expression.txt").to_string();
    let human_sentace = Sentance::from(data);
    let parser = Formula::try_from(human_sentace).unwrap();
    full_sat_group.bench_function("7x7", |b| {
        b.iter(|| {
            std::hint::black_box(for _ in 1..=100 {
                parser.fully_solve();
            })
        });
    });

    let data: String = include_str!("../sat_formulas/sat_8x8_expression.txt").to_string();
    let human_sentace = Sentance::from(data);
    let parser = Formula::try_from(human_sentace).unwrap();
    full_sat_group.bench_function("8x8", |b| {
        b.iter(|| {
            std::hint::black_box(for _ in 1..=100 {
                parser.fully_solve();
            })
        });
    });

    let data: String = include_str!("../sat_formulas/sat_9x9_expression.txt").to_string();
    let human_sentace = Sentance::from(data);
    let parser = Formula::try_from(human_sentace).unwrap();
    full_sat_group.bench_function("9x9", |b| {
        b.iter(|| {
            std::hint::black_box(for _ in 1..=100 {
                parser.fully_solve();
            })
        });
    });
}

criterion_group!(benches, bench_full_solver);
criterion_main!(benches);
