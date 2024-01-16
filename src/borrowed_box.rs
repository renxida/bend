use std::{ptr::NonNull, marker::PhantomData};

pub struct BorrowedBox<'t, T> {
  /// Invariant: `inner` is mutably borrowed for `'t`, so it must not be dropped
  /// for the duration of `'t`.
  inner: NonNull<T>,
  // establish contravariance over `'t``
  __: PhantomData<fn(&'t mut ())>,
}

impl<'t, T> BorrowedBox<'t, T> {
  pub fn new(value: T) -> (&'t mut T, Self) {
    let mut inner = NonNull::from(Box::leak(Box::new(value)));
    let borrow = unsafe { &mut *inner.as_mut() };
    (borrow, BorrowedBox { inner, __: PhantomData })
  }
  pub fn place_option(self, into: &'t mut Option<Box<T>>) {
    unsafe {
      let into = into as *mut _;
      drop(std::ptr::read(into));
      std::ptr::write(into as *mut _, Some(self.inner));
    };
    std::mem::forget(self);
  }
  pub fn place(self, into: &'t mut Box<T>) {
    unsafe {
      let into = into as *mut _;
      drop(std::ptr::read(into));
      std::ptr::write(into as *mut _, self.inner);
    };
    std::mem::forget(self);
  }
}

impl<'t, T> Drop for BorrowedBox<'t, T> {
  fn drop(&mut self) {
    if !std::thread::panicking() {
      panic!("memory leak: cannot drop BorrowedFrom")
    }
  }
}

#[test]
fn test() {
  let (r, b) = BorrowedBox::new(0);
  *r = 1;
  let mut x = Box::new(0);
  b.place(&mut x);
  *r = 2;
  assert_eq!(*x, 2);
}
