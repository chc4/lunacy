use std::sync::atomic::{AtomicUsize, Ordering};
#[derive(Default, Debug)]
pub struct Counter {
    count: AtomicUsize,
}
impl std::fmt::Display for Counter {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        #[cfg(feature = "counters")]
        {
            let num = self.count.load(Ordering::Acquire).to_string()
                .as_bytes()
                .rchunks(3)
                .rev()
                .map(std::str::from_utf8)
                .collect::<Result<Vec<&str>, _>>()
                .unwrap()
                .join("_");  // separator
            write!(f, "{}", num)
        }
        #[cfg(not(feature = "counters"))]
        {
            write!(f, "xxx")
        }
    }
}

#[cfg(feature = "counters")]
impl Counter {
    pub fn increment(&mut self) {
        self.count.update(Ordering::Release, Ordering::Relaxed, |u| u + 1);
    }
}

#[cfg(not(feature = "counters"))]
impl Counter {
    pub fn increment(&mut self) {
        // no-op
    }
}

#[derive(Default)]
pub struct PerfCounters {
    pub interpreter_count: Counter,
    pub versioned_count: Counter,
}

impl std::fmt::Debug for PerfCounters {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "PerfCounters {{")?;
        write!(f, " interpreter_count({})", self.interpreter_count)?;
        write!(f, " versioned_count({})", self.versioned_count)?;
        write!(f, " }}")
    }
}
