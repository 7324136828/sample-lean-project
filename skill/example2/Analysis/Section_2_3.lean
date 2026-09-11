import Mathlib.Tactic
import Analysis.Section_2_2

/-!
# Analysis I, Section 2.3: Multiplication

This file is a translation of Section 2.3 of Analysis I to Lean 4. All numbering refers to the
original text.

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Definition of multiplication and exponentiation for the "Chapter 2" natural numbers,
  {name}`Chapter2.Nat`.

Note: at the end of this chapter, the {name}`Chapter2.Nat` class will be deprecated in favor of the
standard Mathlib class {name}`_root_.Nat`, or {lean}`ℕ`.  However, we will develop the properties of
{name}`Chapter2.Nat` "by hand" for pedagogical purposes.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Chapter2

/-- Definition 2.3.1 (Multiplication of natural numbers) -/
abbrev Nat.mul (n m : Nat) : Nat := Nat.recurse (fun _ prod ↦ prod + m) 0 n

/-- This instance allows for the {kw (of := «term_*_»)}`*` notation to be used for natural number multiplication. -/
instance Nat.instMul : Mul Nat where
  mul := mul

/-- Definition 2.3.1 (Multiplication of natural numbers)
Compare with Mathlib's {name}`Nat.zero_mul` -/
theorem Nat.zero_mul (m: Nat) : 0 * m = 0 := recurse_zero (fun _ prod ↦ prod+m) _

/-- Definition 2.3.1 (Multiplication of natural numbers)
Compare with Mathlib's {name}`Nat.succ_mul` -/
theorem Nat.succ_mul (n m: Nat) : (n++) * m = n * m + m := recurse_succ (fun _ prod ↦ prod+m) _ _

theorem Nat.one_mul' (m: Nat) : 1 * m = 0 + m := by
  rw [←zero_succ, succ_mul, zero_mul]

/-- Compare with Mathlib's {name}`Nat.one_mul` -/
theorem Nat.one_mul (m: Nat) : 1 * m = m := by
  rw [one_mul', zero_add]

theorem Nat.two_mul (m: Nat) : 2 * m = 0 + m + m := by
  rw [←one_succ, succ_mul, one_mul']

/-- This lemma will be useful to prove Lemma 2.3.2.
Compare with Mathlib's {name}`Nat.mul_zero` -/
lemma Nat.mul_zero (n: Nat) : n * 0 = 0 := by
  revert n
  apply induction
  . apply zero_mul
  intro n ih
  rw [succ_mul, ih]
  simp

/-- This lemma will be useful to prove Lemma 2.3.2.
Compare with Mathlib's {name}`Nat.mul_succ` -/

theorem Nat.add_left_add (a b c:Nat) (habc:  b =  c) : a + b = a + c := by
  revert a
  apply induction
  . rw [zero_add]
    conv =>
      rhs
      rw [zero_add]
    exact habc
  intro n ih
  rw [succ_add, ih , ← succ_add]



lemma Nat.mul_succ (n m:Nat) : n * m++ = n * m + n := by
  revert m n
  apply induction
  . intro m
    rw [zero_mul, add_zero, zero_mul] at *
  intro n ih c
  have h1 : (n++) * (c++) =  n * (c++)  + (c++) := by
    apply succ_mul
  have h2 : (n++) * c = n * c + c := by
    apply succ_mul
  rw [h1, h2]
  have h3 := ih c
  rw [h3]
  rw [add_assoc]
  conv =>
    rhs
    rw [add_assoc]
  have h4 := add_left_add (n * c) (n + c++) (c + n++)
  have h5 : n + c++ = c + n++ := by
    rw [add_succ, add_comm, ← add_succ]
  have h6 := h4 h5
  exact h6



/-- Lemma 2.3.2 (Multiplication is commutative) / Exercise 2.3.1
Compare with Mathlib's {name}`Nat.mul_comm` -/
lemma Nat.mul_comm (n m: Nat) : n * m = m * n := by
  revert n
  apply induction
  . rw [mul_zero, zero_mul]
  intro n ih
  rw [succ_mul, mul_succ, ih]


/-- Compare with Mathlib's {name}`Nat.mul_one` -/
theorem Nat.mul_one (m: Nat) : m * 1 = m := by
  rw [mul_comm, one_mul]

/-- This lemma will be useful to prove Lemma 2.3.3.
Compare with Mathlib's {name}`Nat.mul_pos` -/
lemma Nat.pos_mul_pos {n m: Nat} (h₁: n.IsPos) (h₂: m.IsPos) : (n * m).IsPos := by
  have h3 := succ_pred n h₁
  rw [← h3, succ_mul]
  have h4 := add_pos_left (n.pred * m) h₂
  rw [add_comm] at h4
  exact h4

/-- Lemma 2.3.3 (Positive natural numbers have no zero divisors) / Exercise 2.3.2.
    Compare with Mathlib's {name}`Nat.mul_eq_zero`.  -/
lemma Nat.mul_eq_zero (n m: Nat) : n * m = 0 ↔ n = 0 ∨ m = 0 := by
  constructor
  . contrapose
    intro h
    rw [not_or] at h
    obtain ⟨h1, h2⟩ := h
    rw [← ne_eq] at *
    rw [← isPos_iff] at *
    have h3 := pos_mul_pos h1 h2
    exact h3
  intro h
  rcases h with h | h
  . rw [h, zero_mul]
  . rw [h, mul_zero]

/-- Proposition 2.3.4 (Distributive law)
Compare with Mathlib's {name}`Nat.mul_add` -/
theorem Nat.mul_add (a b c: Nat) : a * (b + c) = a * b + a * c := by
  -- This proof is written to follow the structure of the original text.
  revert c; apply induction
  . rw [add_zero]
    rw [mul_zero, add_zero]
  intro c habc
  rw [add_succ, mul_succ]
  rw [mul_succ, ←add_assoc, ←habc]

/-- Proposition 2.3.4 (Distributive law)
Compare with Mathlib's {name}`Nat.add_mul`  -/
theorem Nat.add_mul (a b c: Nat) : (a + b)*c = a*c + b*c := by
  simp only [mul_comm, mul_add]

/-- Proposition 2.3.5 (Multiplication is associative) / Exercise 2.3.3
Compare with Mathlib's {name}`Nat.mul_assoc` -/
theorem Nat.mul_assoc (a b c: Nat) : (a * b) * c = a * (b * c) := by
  revert a
  apply induction
  . rfl
  . intro n ih
    rw [succ_mul, add_mul, add_comm]
    conv =>
      rhs
      rw [succ_mul, add_comm]
    have h1 := add_left_add (b*c) (n * b * c) (n * (b * c)) ih
    exact h1

/-- (Not from textbook)  {name}`Nat` is a commutative semiring.
    This allows tactics such as {tactic}`ring` to apply to the Chapter 2 natural numbers. -/
instance Nat.instCommSemiring : CommSemiring Nat where
  left_distrib := mul_add
  right_distrib := add_mul
  zero_mul := zero_mul
  mul_zero := mul_zero
  mul_assoc := mul_assoc
  one_mul := one_mul
  mul_one := mul_one
  mul_comm := mul_comm

/-- This illustration of the {tactic}`ring` tactic is not from the
    textbook. -/
example (a b c d:ℕ) : (a+b)*1*(c+d) = d*b+a*c+c*b+a*d+0 := by ring


/-- Proposition 2.3.6 (Multiplication preserves order)
Compare with Mathlib's {name}`Nat.mul_lt_mul_of_pos_right` -/
theorem Nat.mul_lt_mul_of_pos_right {a b c: Nat} (h: a < b) (hc: c.IsPos) : a * c < b * c := by
  -- This proof is written to follow the structure of the original text.
  rw [lt_iff_add_pos] at h
  choose d hdpos hd using h
  replace hd := congr($hd * c)
  rw [add_mul] at hd
  have hdcpos : (d * c).IsPos := pos_mul_pos hdpos hc
  rw [lt_iff_add_pos]
  use d*c

/-- Proposition 2.3.6 (Multiplication preserves order) -/
theorem Nat.mul_gt_mul_of_pos_right {a b c: Nat} (h: a > b) (hc: c.IsPos) :
    a * c > b * c := mul_lt_mul_of_pos_right h hc

/-- Proposition 2.3.6 (Multiplication preserves order)
Compare with Mathlib's {name}`Nat.mul_lt_mul_of_pos_left` -/
theorem Nat.mul_lt_mul_of_pos_left {a b c: Nat} (h: a < b) (hc: c.IsPos) : c * a < c * b := by
  simp [mul_comm]
  exact mul_lt_mul_of_pos_right h hc

/-- Proposition 2.3.6 (Multiplication preserves order) -/
theorem Nat.mul_gt_mul_of_pos_left {a b c: Nat} (h: a > b) (hc: c.IsPos) :
    c * a > c * b := mul_lt_mul_of_pos_left h hc

/-- Corollary 2.3.7 (Cancellation law)
Compare with Mathlib's {name}`Nat.mul_right_cancel` -/
lemma Nat.mul_cancel_right {a b c: Nat} (h: a * c = b * c) (hc: c.IsPos) : a = b := by
  -- This proof is written to follow the structure of the original text.
  have := trichotomous a b
  obtain hlt | rfl | hgt := this
  . replace hlt := mul_lt_mul_of_pos_right hlt hc
    apply ne_of_lt at hlt
    contradiction
  . rfl
  replace hgt := mul_gt_mul_of_pos_right hgt hc
  apply ne_of_gt at hgt
  contradiction

/-- (Not from textbook) {name}`Nat` is an ordered semiring.
This allows tactics such as {tactic}`gcongr` to apply to the Chapter 2 natural numbers. -/
instance Nat.isOrderedRing : IsOrderedRing Nat where
  zero_le_one := zero_le 1
  mul_le_mul_of_nonneg_left := by
    intro a h b c h1
    by_cases h2 : a = 0
    . subst a
      rw [zero_mul]
      apply zero_le
    . rw [← ne_eq, ← isPos_iff] at h2
      rw [le_iff_lt_or_eq] at h1
      rcases h1 with h1 | h1
      . have h3 :=  mul_lt_mul_of_pos_left h1 h2
        rw [le_iff_lt_or_eq]
        apply Or.inl h3
      have h4 := congr(a * $h1)
      rw [le_iff_lt_or_eq (a*b) (a*c)]
      exact Or.inr h4
  mul_le_mul_of_nonneg_right := by
    intro a h b c h1
    rw [le_iff_lt_or_eq] at h
    rw [le_iff_lt_or_eq] at h1
    rcases h with h | h
    . rw [le_iff_lt_or_eq]
      have h2 := (isPos_iff a).mpr ((ne_of_gt a 0) h)
      rcases h1 with h1 | h1
      . have h3 :=  mul_lt_mul_of_pos_right h1 h2
        apply Or.inl h3
      have h4 := congr($h1*a)
      apply Or.inr h4
    subst a
    rw [mul_zero]
    apply zero_le



/-- This illustration of the {tactic}`gcongr` tactic is not from the
    textbook. -/
example (a b c d:Nat) (hab: a ≤ b) : c*a*d ≤ c*b*d := by
  gcongr
  . exact d.zero_le
  exact c.zero_le


theorem Nat.positive_means_gt_zero (n:Nat):  n.IsPos ↔ n > 0 := by
  constructor
  . intro h
    rw [isPos_iff] at h
    simp
    have h1 := n.zero_le
    rw [le_iff_lt_or_eq] at h1
    rcases h1 with h1 | h1
    . exact h1
    rw [h1] at h
    contradiction
  intro  h
  simp at h
  have h1 := ne_of_lt 0 n h
  rw [isPos_iff]
  by_contra h2
  rw [h2] at h1
  contradiction



/-- Proposition 2.3.9 (Euclid's division lemma) / Exercise 2.3.5
Compare with Mathlib's {name}`Nat.mod_eq_iff` -/
theorem Nat.exists_div_mod (n:Nat) {q: Nat} (hq: q.IsPos) :
    ∃ m r: Nat, 0 ≤ r ∧ r < q ∧ n = m * q + r := by
  revert n
  have h1 := (positive_means_gt_zero q).mp hq
  simp at h1
  apply induction
  . use 0
    use 0
    simp
    exact h1
  . intro n ih
    obtain ⟨m, r, ⟨h4, ⟨h5, h6⟩⟩⟩ := ih
    by_cases h3 : r++ = q
    . use (m+1)
      use 0
      constructor
      . exact zero_le 0
      constructor
      . exact h1
      have h7 := congr($h6++)
      rw [← add_succ, h3] at h7
      have h8 := one_mul q
      nth_rewrite 2 [← h8] at h7
      rw [← add_mul] at h7
      rw [add_zero]
      exact h7
    use m
    use (r+1)
    constructor
    . exact zero_le (r+1)
    constructor
    . have h9 := (lt_iff_succ_le r q).mp h5
      rw [le_iff_lt_or_eq] at h9
      rcases h9 with h9 | h9
      . rw [← one_add, add_comm] at h9
        exact h9
      contradiction
    have h7 := congr($h6++)
    rw [← add_succ] at h7
    conv at h7 =>
      rhs
      rw [← one_add]
    have h9 : 1 + r = r + 1 := add_comm 1 r
    rw [h9] at h7
    exact h7


/-- Definition 2.3.11 (Exponentiation for natural numbers) -/
abbrev Nat.pow (m n: Nat) : Nat := Nat.recurse (fun _ prod ↦ prod * m) 1 n

instance Nat.instPow : HomogeneousPow Nat where
  pow := Nat.pow

/-- Definition 2.3.11 (Exponentiation for natural numbers)
Compare with Mathlib's {name}`Nat.pow_zero` -/
@[simp]
theorem Nat.pow_zero (m: Nat) : m ^ (0:Nat) = 1 := recurse_zero (fun _ prod ↦ prod * m) _

/-- Definition 2.3.11 (Exponentiation for natural numbers) -/
@[simp]
theorem Nat.zero_pow_zero : (0:Nat) ^ 0 = 1 := recurse_zero (fun _ prod ↦ prod * 0) _

/-- Definition 2.3.11 (Exponentiation for natural numbers)
Compare with Mathlib's {name}`Nat.pow_succ` -/
theorem Nat.pow_succ (m n: Nat) : (m:Nat) ^ n++ = m^n * m :=
  recurse_succ (fun _ prod ↦ prod * m) _ _

/-- Compare with Mathlib's {name}`Nat.pow_one` -/
@[simp]
theorem Nat.pow_one (m: Nat) : m ^ (1:Nat) = m := by
  rw [←zero_succ, pow_succ]; simp

/-- Exercise 2.3.4-/
theorem Nat.sq_add_eq (a b: Nat) :
    (a + b) ^ (2 : Nat) = a ^ (2 : Nat) + 2 * a * b + b ^ (2 : Nat) := by
  have h: 2 = 1++ := by rfl
  have h1 : (a + b) ^ (2 : Nat) = (a + b) ^ (2 : Nat) := by rfl
  conv at h1 =>
    rhs
    rw [h, pow_succ, pow_one, add_mul, mul_add, mul_add, add_assoc]
  nth_rewrite 2 [← add_assoc] at h1
  have h2 : a * b = b * a := mul_comm a b
  rw [← h2] at h1
  have h3 : a * b + a * b = 2 * (a * b) := two_mul (a*b)
  rw [← mul_assoc] at h3
  have h4 : ∀x:Nat, x * x = x ^ (2 : Nat) := by
    intro x
    apply pow_one
  rw [h3] at h1
  have h5 := h4 a
  have h6 := h4 b
  rw [h5] at h1
  rw [h6] at h1
  rw [← add_assoc] at h1
  exact h1


end Chapter2
