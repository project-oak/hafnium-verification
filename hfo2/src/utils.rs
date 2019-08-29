/*
 * Copyright 2019 Jeehoon Kang
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

use core::sync::atomic::spin_loop_hint;

#[macro_export]
macro_rules! ok_or_return {
    ($e:expr, $err:expr) => {{
        match $e {
            Ok(r) => r,
            Err(_) => return $err,
        }
    }};
}

pub fn spin_loop() -> ! {
    loop {
        spin_loop_hint();
    }
}

#[inline]
pub fn div_ceil(a: usize, b: usize) -> usize {
    (a + b - 1) / b
}

#[inline]
pub fn div_floor(a: usize, b: usize) -> usize {
    a / b
}

#[inline]
pub fn round_up(a: usize, b: usize) -> usize {
    div_ceil(a, b) * b
}

#[inline]
pub fn round_down(a: usize, b: usize) -> usize {
    div_floor(a, b) * b
}

pub trait ResReduce<T, E> {
    fn res_reduce<F>(self, f: F) -> Result<T, E>
    where
        Self: Sized,
        F: FnMut(T, T) -> Result<T, E>;
}

impl<T, E, I> ResReduce<T, E> for I
where
    I: Iterator<Item = Result<T, E>>,
    E: Default,
{
    #[inline]
    fn res_reduce<F>(mut self, mut f: F) -> Result<T, E>
    where
        Self: Sized,
        F: FnMut(T, T) -> Result<T, E>,
    {
        let mut acc = self.next().ok_or_else(E::default)??;
        for val in self {
            acc = f(acc, val?)?;
        }
        Ok(acc)
    }
}
