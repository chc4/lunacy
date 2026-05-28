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
    pub fn increment(&self) {
        self.count.fetch_add(1, Ordering::Relaxed);
    }
}

#[cfg(feature = "jit_dump")]
impl serde::Serialize for Counter {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serializer.serialize_u64(self.count.load(Ordering::Relaxed) as u64)
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
