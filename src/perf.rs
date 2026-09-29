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
    pub versioned_count: Counter,
    /// Array part stores (SETTABLE into a table's array part, or at a number key
    /// past it) run, by what the specializer knew of the value's type: nothing,
    /// that it's a number, or its type. Feature `store_types`.
    pub array_stores: [Counter; 3],
}

impl std::fmt::Debug for PerfCounters {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "PerfCounters {{")?;
        write!(f, " versioned_count({})", self.versioned_count)?;
        #[cfg(feature = "store_types")]
        write!(f, " array_stores(unknown {}, number {}, typed {})", self.array_stores[0], self.array_stores[1], self.array_stores[2])?;
        write!(f, " }}")
    }
}
