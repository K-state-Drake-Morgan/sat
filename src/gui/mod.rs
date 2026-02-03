use std::sync::{Arc, Mutex, atomic::AtomicBool};

use gpui::{Render, div};
use num_bigint::BigUint;

pub struct Application {
    solving: Arc<AtomicBool>,
    result: Arc<Mutex<Option<BigUint>>>,
    operands: Arc<Mutex<Option<Vec<String>>>>,
    error: Arc<Mutex<Option<String>>>,
}

impl Render for Application {
    fn render(
        &mut self,
        window: &mut gpui::Window,
        cx: &mut gpui::Context<Self>,
    ) -> impl gpui::IntoElement {
        div()
    }
}
