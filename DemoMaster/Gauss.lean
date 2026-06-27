def somme_arithmetique : Nat → Nat
  | 0     => 0
  | n + 1 => (n + 1) + somme_arithmetique n

theorem preuve_gauss (n : Nat) : 2 * somme_arithmetique n = n * (n + 1) := by
  induction n with
  | zero =>
      simp [somme_arithmetique]
  | succ n ih =>
      calc
        2 * somme_arithmetique (n + 1)
          = 2 * ((n + 1) + somme_arithmetique n) := by simp [somme_arithmetique]
        _ = 2 * (n + 1) + 2 * somme_arithmetique n := by rw [Nat.left_distrib]
        _ = 2 * (n + 1) + n * (n + 1)             := by rw [ih]
        _ = (2 + n) * (n + 1)                     := by rw [← Nat.right_distrib]
        _ = (n + 2) * (n + 1)                     := by rw [Nat.add_comm]
        _ = (n + 1) * (n + 2)                     := by rw [Nat.mul_comm]

#eval (id (do
  let n_values := List.range 11
  for n in n_values do
    let s := somme_arithmetique n
    let formula := n * (n + 1) / 2
    let bar := String.ofList (List.replicate (s / 2) '█')
    IO.println s!"n={n} | Somme={s} | Formule={formula} | {bar}"
  return () : IO Unit))
