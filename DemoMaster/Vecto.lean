import Std

/-!
Proving fundamental properties about list operations via structural induction.
-/

-- map preserves length
theorem map_preserves_length (f : α → β) (xs : List α) :
    (xs.map f).length = xs.length := by
  induction xs with
  | nil => simp [List.map]
  | cons x xs ih => simp [List.map, ih]

-- map distributes over composition
theorem map_comp (f : β → γ) (g : α → β) (xs : List α) :
    (xs.map g).map f = xs.map (f ∘ g) := by
  induction xs with
  | nil => simp [List.map]
  | cons x xs ih => simp [List.map, ih]

-- map over append = append of maps
theorem map_append (f : α → β) (xs ys : List α) :
    (xs ++ ys).map f = xs.map f ++ ys.map f := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [List.map, ih]

-- reverse preserves length
theorem reverse_preserves_length (xs : List α) :
    xs.reverse.length = xs.length := by
  exact List.length_reverse

-- foldl over a sum accumulator
-- We prove: foldl (· + ·) init xs = init + foldl (· + ·) 0 xs
theorem foldl_add_shift (xs : List Nat) (init : Nat) :
    xs.foldl (· + ·) init = init + xs.foldl (· + ·) 0 := by
  induction xs generalizing init with
  | nil => simp [List.foldl]
  | cons x xs ih =>
      simp [List.foldl]
      rw [ih (init + x), ih x]
      omega

-- sum of a list via foldl distributes over append
theorem sum_append (xs ys : List Nat) :
    (xs ++ ys).foldl (· + ·) 0 = xs.foldl (· + ·) 0 + ys.foldl (· + ·) 0 := by
  induction xs with
  | nil => simp [List.foldl]
  | cons x xs ih =>
      simp only [List.cons_append, List.foldl, Nat.zero_add]
      rw [foldl_add_shift (xs ++ ys) x, ih, foldl_add_shift xs x]
      omega

/-!
Using Fin-indexed functions as fixed-size "vectors" and proving properties.
-/

-- A simple vector as a function from Fin n → to use Float you need Mathlib.
-- Define the Vector and prove structural properties.
inductive Vec (α : Type) : Nat → Type where
  | nil  : Vec α 0
  | cons : α → Vec α n → Vec α (n + 1)

namespace Vec

def map (f : α → β) : Vec α n → Vec β n
  | .nil => .nil
  | .cons x xs => .cons (f x) (xs.map f)

def zipWith (f : α → β → γ) : Vec α n → Vec β n → Vec γ n
  | .nil, .nil => .nil
  | .cons x xs, .cons y ys => .cons (f x y) (xs.zipWith f ys)

def foldr (f : α → β → β) (init : β) : Vec α n → β
  | .nil => init
  | .cons x xs => f x (xs.foldr f init)

def toList : Vec α n → List α
  | .nil => []
  | .cons x xs => x :: xs.toList

-- map preserves vector length
-- This is *free* because Vec carries its length in the type index.
-- toList length matches length of the vector:
theorem toList_length : (v : Vec α n) → v.toList.length = n
  | .nil => rfl
  | .cons _ xs => by simp [toList, toList_length xs]

-- map-map fusion for Vec
theorem map_map_fusion (f : β → γ) (g : α → β) (v : Vec α n) :
    (v.map g).map f = v.map (f ∘ g) := by
  induction v with
  | nil => rfl
  | cons x xs ih => simp [map, ih]

-- zipWith is commutative when f is commutative
theorem zipWith_comm (f : α → α → β) (hf : ∀ a b, f a b = f b a)
    (xs ys : Vec α n) : xs.zipWith f ys = ys.zipWith f xs := by
  induction xs with
  | nil => match ys with | .nil => rfl
  | cons x xs ih =>
      match ys with
      | .cons y ys => simp [zipWith, hf x y, ih ys]

end Vec

/-!
A toy formalization: we define dot product, a threshold activation,
and prove that the neuron output is deterministic.
-/

-- Dot product on List Nat
def dot : List Nat → List Nat → Nat
  | [], _ => 0
  | _, [] => 0
  | x :: xs, w :: ws => x * w + dot xs ws

-- Threshold activation: 1 if above threshold, else 0
def threshold (t : Nat) (x : Nat) : Nat :=
  if x ≥ t then 1 else 0

-- A single neuron: dot product then threshold
def neuron (weights : List Nat) (bias : Nat) (thresh : Nat) (inputs : List Nat) : Nat :=
  threshold thresh (dot inputs weights + bias)

-- determinism:Same inputs + same weights = same output
theorem neuron_deterministic (w : List Nat) (b t : Nat) (x : List Nat) :
    neuron w b t x = neuron w b t x := by
  rfl

-- Dot product with zero weights is zero
theorem dot_zero_weights (xs : List Nat) (n : Nat) :
    dot xs (List.replicate n 0) = 0 := by
  induction xs generalizing n with
  | nil => simp [dot]
  | cons x xs ih =>
      match n with
      | 0 => simp [dot]
      | n + 1 => simp [dot, List.replicate, ih n]

-- neuron with zero weights outputs threshold
theorem neuron_zero_weights (n : Nat) (b t : Nat) (xs : List Nat) :
    neuron (List.replicate n 0) b t xs = threshold t b := by
  simp [neuron, dot_zero_weights]

-- eval
#eval do
  let weights := [2, 3, 1]
  let inputs  := [1, 0, 4]
  let b := 1
  let t := 5
  let out := neuron weights b t inputs
  IO.println s!"neuron({inputs}, w={weights}, b={b}, t={t}) = {out}"
  -- dot = 1*2 + 0*3 + 4*1 = 6, +bias=7, ≥5 → 1

#eval do
  IO.println "--- Vec demo ---"
  let v : Vec Nat 3 := .cons 10 (.cons 20 (.cons 30 .nil))
  let doubled := v.map (· * 2)
  IO.println s!"original: {v.toList}"
  IO.println s!"doubled:  {doubled.toList}"
