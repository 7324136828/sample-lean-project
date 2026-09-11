/-!
# Example.Basic

A minimalistic sample module demonstrating Lean 4 definitions, theorems, and tactic proofs.
-/

namespace Example

/-- A simple greeting function. -/
def hello : String := "Hello, Lean 4!"

/-- Addition of natural numbers is commutative. -/
theorem nat_add_comm (n m : Nat) : n + m = m + n := by
  omega

/-- Addition of natural numbers is associative. -/
theorem nat_add_assoc (a b c : Nat) : (a + b) + c = a + (b + c) := by
  omega

/-- Double of `n` equals `n + n`. -/
theorem double_eq_add (n : Nat) : 2 * n = n + n := by
  omega

/-- Any natural number is less than or equal to its sum with another natural number. -/
theorem le_add_right (n m : Nat) : n ≤ n + m := by
  omega

end Example
