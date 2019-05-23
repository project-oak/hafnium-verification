use core::sync::atomic::spin_loop_hint;

pub fn spin_loop() -> ! {
    loop {
        spin_loop_hint();
    }
}

pub trait OptReduce<T> {
    fn opt_reduce<F>(self, f: F) -> Option<T>
    where
        Self: Sized,
        F: FnMut(T, T) -> Option<T>;
}

impl<T, I> OptReduce<T> for I
where
    I: Iterator<Item = Option<T>>,
{
    #[inline]
    fn opt_reduce<F>(mut self, mut f: F) -> Option<T>
    where
        Self: Sized,
        F: FnMut(T, T) -> Option<T>,
    {
        let mut acc = self.next()??;
        for val in self {
            acc = f(acc, val?)?;
        }
        Some(acc)
    }
}
