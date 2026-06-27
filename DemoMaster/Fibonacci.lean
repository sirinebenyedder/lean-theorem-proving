import Std

def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib (n + 1) + fib n


theorem fib_rec (n : Nat) :
  fib (n + 2) = fib (n + 1) + fib n := by
  rfl

#eval do
  let n_values := List.range 11
  -- iterate over the list in the IO monad and print Fibonacci values
  n_values.forM fun n => do
    let v := fib n
    IO.println s!"n={n} | Fib={v}"
