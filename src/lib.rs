//! # Easy Retry
//!
//! `easy_retry` is AsyncReturn Rust library that provides utilities for retrying operations with different strategies.
//!
//! This library provides several retry strategies, including linear, exponential, and their asynchronous versions. You can choose the strategy that best fits your needs.
//!
//! The library is designed to be simple and easy to use. It provides a single enum, `EasyRetry`, that represents different retry strategies. You can create a new retry strategy by calling one of the `new_*` methods on the `EasyRetry` enum.
//!
//! The library provides a `run` method that takes a closure and runs the operation with the specified retry strategy. The `run` method returns the result of the operation, or an error if the operation fails after all retries.
//!
//! The run method expects the closure to return a `Result` type. The `Ok` variant should contain the result of the operation, and the `Err` variant should contain the error that occurred during the operation.
//!
//! # Features
//!
//! * **Linear Retry**: In this strategy, the delay between retries is constant.
//! * **Exponential Retry**: In this strategy, the delay between retries doubles after each retry.
//! * **Linear Async Retry**: This is an asynchronous version of the linear retry strategy. This feature is only available when the `async` feature is enabled.
//! * **Exponential Async Retry**: This is an asynchronous version of the exponential retry strategy. This feature is only available when the `async` feature is enabled.
//!
//! # Examples
//!
//! ```
//! use easy_retry::EasyRetry;
//!
//! fn my_sync_fn(_n: &str) -> Result<(), std::io::Error> {
//!     Err(std::io::Error::new(std::io::ErrorKind::Other, "generic error"))
//! }
//!
//! // Retry the operation with AsyncReturn linear strategy (1 second delay, 2 retries)
//! let retry_strategy = EasyRetry::new_linear(1, 2);
//! let result = retry_strategy.run(|| my_sync_fn("Hi"));
//! assert!(result.is_err());
//!
//! ```
//!
//! # Asynchronous Example
//!
//! ```rust
//! use easy_retry::EasyRetry;
//!
//! async fn my_async_fn(_n: u64) -> Result<(), std::io::Error> {
//!    Err(std::io::Error::new(std::io::ErrorKind::Other, "generic error"))
//! }
//!
//! #[tokio::main]
//! async fn main() {
//!     // Retry the operation with an exponential strategy (1 second delay, 2 retries)
//!     let retry_strategy = EasyRetry::new_exponential_async(1, 2);
//!     let result = retry_strategy.run_async(|| my_async_fn(42)).await;
//!     assert!(result.is_err());
//!
//! }
//! ```
//! # Usage
//!
//! Add this to your `Cargo.toml`:
//!
//! ```toml
//! [dependencies]
//! easy_retry = "0.1.0"
//! ```
//!
//! Then, add this to your crate root (`main.rs` or `lib.rs`):
//!
//! ```rust
//! extern crate easy_retry;
//! ```
//!
//! Now, you can use the `EasyRetry` enum to create AsyncReturn retry strategy:
//!
//! ```rust
//! use easy_retry::EasyRetry;
//!
//! let retry_strategy = EasyRetry::new_linear(100, 5);
//! ```
//!
//! # License
//!
//! This project is licensed under the MIT License.


#![deny(missing_docs)]
use std::fmt::Debug;
#[cfg(feature = "async")]
use std::future::Future;
#[derive(Debug, Copy, Clone)]

/// `EasyRetry` is an enum representing different kinds of retry strategies.
pub enum EasyRetry {
    /// Represents AsyncReturn linear retry strategy.
    Linear {
        #[doc(hidden)]
        /// The delay between retries in seconds.
        delay: u64,
        #[doc(hidden)]
        /// The number of retries.
        retries: u64,
    },
    /// Represents an exponential retry strategy.
    Exponential {
        /// The delay between retries in seconds.
        #[doc(hidden)]
        delay: u64,
        /// The number of retries.
        #[doc(hidden)]
        retries: u64,
    },
    /// Represents an asynchronous version of the linear retry strategy.
    ///
    /// This variant is only available when the `async` feature is enabled.
    #[cfg(feature = "async")]
    LinearAsync {
        /// The delay between retries in seconds.
        #[doc(hidden)]
        delay: u64,
        /// The number of retries.
        #[doc(hidden)]
        retries: u64,
    },
    /// Represents an asynchronous version of the exponential retry strategy.
    ///
    /// This variant is only available when the `async` feature is enabled.
    #[cfg(feature = "async")]
    ExponentialAsync {
        /// The delay between retries in seconds.
        #[doc(hidden)]
        delay: u64,
        /// The number of retries.
        #[doc(hidden)]
        retries: u64,
    },
}

impl EasyRetry {
    /// Creates a new `EasyRetry::Linear` variant with the specified delay and number of retries.
    ///
    /// # Arguments
    ///
    /// * `delay` - The delay between retries in seconds.
    /// * `retries` - The number of retries.
    ///
    /// # Examples
    ///
    /// ```
    /// use easy_retry::EasyRetry;
    ///
    /// let retry_strategy = EasyRetry::new_linear(100, 5);
    /// ```
    pub fn new_linear(delay: u64, retries: u64) -> Self {
        EasyRetry::Linear { delay, retries }
    }

    /// Creates a new `EasyRetry::Exponential` variant with the specified initial delay and number of retries.
    ///
    /// # Arguments
    ///
    /// * `delay` - The delay between retries in . The delay doubles after each retry.
    /// * `retries` - The number of retries.
    ///
    /// # Examples
    ///
    /// ```
    /// use easy_retry::EasyRetry;
    ///
    /// let retry_strategy = EasyRetry::new_exponential(100, 5);
    /// ```
    pub fn new_exponential(delay: u64, retries: u64) -> Self {
        EasyRetry::Exponential { delay, retries }
    }

    /// Creates a new `EasyRetry::LinearAsync` variant with the specified delay and number of retries.
    ///
    /// # Arguments
    ///
    /// * `delay` - The delay between retries in seconds.
    /// * `retries` - The number of retries.
    ///
    /// # Examples
    ///
    /// ```
    /// use easy_retry::EasyRetry;
    ///
    /// let retry_strategy = EasyRetry::new_linear_async(100, 5);
    /// ```
    #[cfg(feature = "async")]
    pub fn new_linear_async(delay: u64, retries: u64) -> Self {
        EasyRetry::LinearAsync { delay, retries }
    }

    /// Creates a new `EasyRetry::ExponentialAsync` variant with the specified initial delay and number of retries.
    ///
    /// # Arguments
    ///
    /// * `delay` - The delay between retries in seconds. The delay doubles after each retry.
    /// * `retries` - The number of retries.
    ///
    /// # Examples
    ///
    /// ```
    /// use easy_retry::EasyRetry;
    ///
    /// let retry_strategy = EasyRetry::new_exponential_async(100, 5);
    /// ```
    #[cfg(feature = "async")]
    pub fn new_exponential_async(delay: u64, retries: u64) -> Self {
        EasyRetry::ExponentialAsync { delay, retries }
    }

    /// Runs the provided function `f` with a retry strategy.
    ///
    /// This function takes a function `f` that implements the `SyncReturn` trait and runs it with a retry strategy. The `SyncReturn` trait is implemented for `FnMut` closures, which can mutate their captured variables and can be called multiple times.
    ///
    /// The function `f` should return a `Result` with the operation's result or error. The types of the result and error are determined by the `SyncReturn` trait's associated types `Item` and `Error`.
    pub fn run<T>(&self, f: T) -> Result<<T as SyncReturn>::Item, <T as SyncReturn>::Error>
    where
        T: SyncReturn,
    {
        Retry::run(f, *self)
    }

    /// Runs the provided function `f` with a retry strategy.
    ///
    /// This function takes a function `f` that implements the `AsyncReturn` trait and runs it with a retry strategy. The `AsyncReturn` trait is implemented for `FnMut` closures, which can mutate their captured variables and can be called multiple times. This function is only available when the `async` feature is enabled.
    ///
    /// The function `f` should return a `Result` with the operation's result or error. The types of the result and error are determined by the `SyncReturn` trait's associated types `Item` and `Error`.
    #[cfg(feature = "async")]
    pub async fn run_async<'a, T>(
        &'a self,
        f: T,
    ) -> Result<<T as AsyncReturn>::Item, <T as AsyncReturn>::Error>
    where
        T: AsyncReturn + 'a + 'static,
    {
        Retry::run_async(f, *self).await
    }

    fn get_retries(&self) -> u64 {
        match self {
            EasyRetry::Linear { retries, .. } => *retries,
            EasyRetry::Exponential { retries, .. } => *retries,
            #[cfg(feature = "async")]
            EasyRetry::LinearAsync { retries, .. } => *retries,
            #[cfg(feature = "async")]
            EasyRetry::ExponentialAsync { retries, .. } => *retries,
        }
    }

    fn get_delay(&self) -> u64 {
        match self {
            EasyRetry::Linear { delay, .. } => *delay,
            EasyRetry::Exponential { delay, .. } => *delay,
            #[cfg(feature = "async")]
            EasyRetry::LinearAsync { delay, .. } => *delay,
            #[cfg(feature = "async")]
            EasyRetry::ExponentialAsync { delay, .. } => *delay,
        }
    }

    fn linear(x: u64) -> u64 {
        x
    }

    fn exponential(x: u64) -> u64 {
        2u64.pow(x as u32)
    }

    fn retry_fn(&self) -> fn(u64) -> u64 {
        match self {
            EasyRetry::Linear { .. } => Self::linear,
            EasyRetry::Exponential { .. } => Self::exponential,
            #[cfg(feature = "async")]
            EasyRetry::LinearAsync { .. } => Self::linear,
            #[cfg(feature = "async")]
            EasyRetry::ExponentialAsync { .. } => Self::exponential,
        }
    }
}

fn do_retry<F, T, E>(mut f: F, t: EasyRetry) -> Result<T, E>
where
    F: FnMut() -> Result<T, E>,
{
    let mut retries: u64 = 0;
    loop {
        match f() {
            Ok(v) => return Ok(v),
            Err(e) => {
                if retries >= t.get_retries() {
                    return Err(e);
                }
                retries += 1;
                std::thread::sleep(std::time::Duration::from_secs((t.retry_fn())(
                    t.get_delay(),
                )));
            }
        }
    }
}

#[cfg(feature = "async")]
async fn do_retry_async<F, T, E>(mut f: F, t: EasyRetry) -> Result<T, E>
where
    F: FnMut() -> std::pin::Pin<Box<dyn Future<Output = Result<T, E>>>>,
{
    let mut retries = 0;
    loop {
        match f().await {
            Ok(v) => return Ok(v),
            Err(e) => {
                if retries >= t.get_retries() {
                    return Err(e);
                }
                retries += 1;
                tokio::time::sleep(std::time::Duration::from_secs((t.retry_fn())(
                    t.get_delay(),
                )))
                .await;
            }
        }
    }
}
struct Retry;
impl Retry {
    #[cfg(feature = "async")]
    async fn run_async<T>(
        mut f: T,
        t: EasyRetry,
    ) -> Result<<T as AsyncReturn>::Item, <T as AsyncReturn>::Error>
    where
        T: AsyncReturn + 'static,
    {
        do_retry_async(move || Box::pin(f.run()), t).await
    }

    fn run<T>(mut f: T, t: EasyRetry) -> Result<<T as SyncReturn>::Item, <T as SyncReturn>::Error>
    where
        T: SyncReturn,
    {
        do_retry(move || f.run(), t)
    }
}

#[cfg(feature = "async")]
pub trait AsyncReturn {
    type Item: Debug;
    type Error: Debug;
    type Future: Future<Output = Result<Self::Item, Self::Error>>;

    fn run(&mut self) -> Self::Future;
}

#[cfg(feature = "async")]
impl<I: Debug, E: Debug, T: Future<Output = Result<I, E>>, F: FnMut() -> T> AsyncReturn for F {
    type Item = I;
    type Error = E;
    type Future = T;
    fn run(&mut self) -> Self::Future {
        self()
    }
}

pub trait SyncReturn {
    type Item: Debug;
    type Error: Debug;

    fn run(&mut self) -> Result<Self::Item, Self::Error>;
}

impl<I: Debug, E: Debug, F: FnMut() -> Result<I, E>> SyncReturn for F {
    type Item = I;
    type Error = E;
    fn run(&mut self) -> Result<Self::Item, Self::Error> {
        self()
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[derive(Debug, Clone)]
    struct NotCopy {
        pub _n: usize,
    }

    fn to_retry_not_copy(n: &NotCopy) -> Result<(), std::io::Error> {
        let _r = n.clone();

        Err(std::io::Error::new(
            std::io::ErrorKind::Other,
            "generic error",
        ))
    }

    fn to_retry(_n: usize) -> Result<(), std::io::Error> {
        Err(std::io::Error::new(
            std::io::ErrorKind::Other,
            "generic error",
        ))
    }

    #[cfg(feature = "async")]
    async fn to_retry_async(_n: usize) -> Result<(), std::io::Error> {
        Err(std::io::Error::new(
            std::io::ErrorKind::Other,
            "generic error",
        ))
    }

    #[test]
    fn test_linear() {
        let retries = 2;
        let delay = 1;
        let instant = std::time::Instant::now();
        let s = EasyRetry::Linear {
            retries,
            delay,
        }
        .run(|| to_retry(1));
        assert!(s.is_err());
        let elapsed = instant.elapsed();
        assert!(elapsed.as_secs() >= retries * delay);
    }

    #[test]
    fn test_expontential() {
        let retries = 2;
        let delay = 1;
        let instant = std::time::Instant::now();
        let s = EasyRetry::Exponential {
            retries,
            delay,
        }
        .run(|| to_retry(1));
        assert!(s.is_err());
        let elapsed = instant.elapsed();
        assert!(elapsed.as_secs() >= retries * delay);
    }

    #[test]
    fn test_not_copy() {
        let retries = 2;
        let delay = 1;
        let not_copy = NotCopy { _n: 1 };
        let instant = std::time::Instant::now();

        let s = EasyRetry::Linear {
            retries,
            delay,
        }
        .run(|| to_retry_not_copy(&not_copy));
        assert!(s.is_err());
        let elapsed = instant.elapsed();
        assert!(elapsed.as_secs() >= retries * delay);
    }

    #[cfg(feature = "async")]
    #[tokio::test]
    async fn test_linear_async() {
        let retries = 2;
        let delay = 1;
        let instant = std::time::Instant::now();
        let s = EasyRetry::LinearAsync {
            retries,
            delay,
        }
        .run_async(|| to_retry_async(1))
        .await;
        assert!(s.is_err());
        let elapsed = instant.elapsed();
        assert!(elapsed.as_secs() >= retries * delay);
    }

    #[cfg(feature = "async")]
    #[tokio::test]
    async fn test_expontential_async() {
        let retries = 2;
        let delay = 1;
        let instant = std::time::Instant::now();
        let s = EasyRetry::ExponentialAsync {
            retries,
            delay,
        }
        .run_async(|| to_retry_async(1))
        .await;
        assert!(s.is_err());
        let elapsed = instant.elapsed();
        assert!(elapsed.as_secs() >= retries * delay);
    }
}
