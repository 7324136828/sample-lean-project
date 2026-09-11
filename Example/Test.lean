import Example.Basic

/-!
# Example.Test

Unit tests and sanity checks for the `Example.Basic` declarations.
-/

namespace Example.Test

-- Check that hello produces the expected string
#eval Example.hello

/-- Unit test: commutativity with zero. -/
theorem test_nat_add_comm_zero : 0 + 42 = 42 + 0 := by
  exact Example.nat_add_comm 0 42

/-- Unit test: associativity on concrete values. -/
theorem test_nat_add_assoc_concrete : (10 + 20) + 30 = 10 + (20 + 30) := by
  exact Example.nat_add_assoc 10 20 30

/-- Unit test: doubling small and larger values. -/
theorem test_double_eq_add_val : 2 * 17 = 17 + 17 := by
  exact Example.double_eq_add 17

theorem test_double_large : 2 * 10000 = 10000 + 10000 := by
  omega

/-- Unit test: order inequality with zero. -/
theorem test_le_add_zero (n : Nat) : n ≤ n + 0 := by
  exact Example.le_add_right n 0

/-- Unit test: reflexivity of equality. -/
theorem test_hello_value : Example.hello = "Hello, Lean 4!" := by
  rfl

end Example.Test
