import Mathlib.Tactic
import Analysis.Section_2_1

/-!
# Analysis I, Section 2.2: Addition

This file is a translation of Section 2.2 of Analysis I to Lean 4.  All numbering refers to the
original text.

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Definition of addition and order for the "Chapter 2" natural numbers, {name}`Chapter2.Nat`.
- Establishment of basic properties of addition and order.

Note: at the end of this chapter, the {name}`Chapter2.Nat` class will be deprecated in favor of the
standard Mathlib class {name}`_root_.Nat`, or {lean}`ℕ`.  However, we will develop the properties of
{name}`Chapter2.Nat` "by hand" for pedagogical purposes.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their
tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Chapter2

/-- Definition 2.2.1. (Addition of natural numbers).
    Compare with Mathlib's {name}`Nat.add` -/
abbrev Nat.add (n m : Nat) : Nat := Nat.recurse (fun _ sum ↦ sum++) m n

theorem Nat.add_iterate (n m : Nat) : Nat.iterate (fun x ↦ x++) n m = Nat.add n m := by
   unfold iterate
   unfold add
   unfold recurse
   cases n with
   | zero => rfl
   | succ n => simp


/-- This instance allows for the {kw (of := «term_+_»)}`+` notation to be used for natural number
    addition.-/
instance Nat.instAdd : Add Nat where add := add

/-- Compare with Mathlib's {name}`Nat.zero_add`. -/
@[simp]
theorem Nat.zero_add (m: Nat) : 0 + m = m := recurse_zero (fun _ sum ↦ sum++) _

/-- Compare with Mathlib's {name}`Nat.succ_add`. -/
theorem Nat.succ_add (n m: Nat) : n++ + m = (n+m)++ := by rfl

/-- Compare with Mathlib's {name}`Nat.one_add`. -/
theorem Nat.one_add (m:Nat) : 1 + m = m++ := by
  rw [show 1 = 0++ from rfl, succ_add, zero_add]

theorem Nat.two_add (m:Nat) : 2 + m = (m++)++ := by
  rw [show 2 = 1++ from rfl, succ_add, one_add]

example : (2:Nat) + 3 = 5 := by
  rw [Nat.two_add, show 3++=4 from rfl, show 4++=5 from rfl]

-- The sum of two natural numbers is again a natural number.
#check (fun (n m:Nat) ↦ n + m)

/-- Lemma 2.2.2 ({lean}`n + 0 = n`). Compare with Mathlib's {name}`Nat.add_zero`. -/
@[simp]
lemma Nat.add_zero (n:Nat) : n + 0 = n := by
  -- This proof is written to follow the structure of the original text.
  revert n
  apply induction
  . rfl
  . intro n h
    calc
      (n++) + 0 = (n+0)++ := by rfl
    _ = n ++ := by rw [h]



/-- Lemma 2.2.3 ({lean}`n+(m++) = (n+m)++`). Compare with Mathlib's {name}`Nat.add_succ`. -/
lemma Nat.add_succ (n m:Nat) : n + (m++) = (n + m)++ := by
  -- this proof is written to follow the structure of the original text.
  revert n
  apply induction
  . rfl
  . intro n h
    rw [succ_add, h]
    rfl


/-- {lean}`n++ = n + 1` (Why?). Compare with Mathlib's {name}`Nat.succ_eq_add_one` -/
theorem Nat.succ_eq_add_one (n:Nat) : n++ = n + 1 := by
  revert n
  apply induction
  . rfl
  . intro n h
    rw [show 1 = 0++ from rfl, add_succ, add_zero]

/-- Proposition 2.2.4 (Addition is commutative). Compare with Mathlib's {name}`Nat.add_comm` -/
theorem Nat.add_comm (n m:Nat) : n + m = m + n := by
  -- this proof is written to follow the structure of the original text.
  revert n
  apply induction
  . rw [add_zero, zero_add]
  . intro n h
    rw [add_succ, ← h]
    rfl


/-- Proposition 2.2.5 (Addition is associative) / Exercise 2.2.1
    Compare with Mathlib's {name}`Nat.add_assoc`. -/
theorem Nat.add_assoc (a b c:Nat) : (a + b) + c = a + (b + c) := by
  revert a
  apply induction
  . rfl
  . intro n h
    rw [succ_add, succ_add]
    rw [h]
    rw [← succ_add]



/-- Proposition 2.2.6 (Cancellation law).
    Compare with Mathlib's {name}`Nat.add_left_cancel`. -/
theorem Nat.add_left_cancel (a b c:Nat) (habc: a + b = a + c) : b = c := by
  -- This proof is written to follow the structure of the original text.
  revert a
  apply induction
  . intro h
    rw [zero_add, zero_add] at h
    exact h
  . intro n h1 h2
    rw [succ_add, succ_add] at h2
    apply succ_cancel at h2
    exact h1 h2



/-- (Not from textbook) {name}`Nat` can be given the structure of a commutative additive monoid.
    This permits tactics such as {tactic}`abel` to apply to the Chapter 2 natural numbers. -/
instance Nat.addCommMonoid : AddCommMonoid Nat where
  add_assoc := add_assoc
  add_comm := add_comm
  zero_add := zero_add
  add_zero := add_zero
  nsmul := nsmulRec

/-- This illustration of the {tactic}`abel` tactic is not from the
    textbook. -/
example (a b c d:Nat) : (a+b)+(c+0+d) = (b+c)+(d+a) := by abel

/-- Definition 2.2.7 (Positive natural numbers).-/
def Nat.IsPos (n:Nat) : Prop := n ≠ 0

theorem Nat.isPos_iff (n:Nat) : n.IsPos ↔ n ≠ 0 := by rfl

theorem Nat.succ_isPos (n:Nat): (n++).IsPos := by
  apply (isPos_iff (n++)).mpr
  apply succ_ne


  -- revert n; apply induction
  -- . intro h
  --   replace h := (Nat.isPos_iff 0).mp h
  --   contradiction
  -- . intro n ih
  --   intro ih2
  --   apply isPos_iff
/-- Proposition 2.2.8 (positive plus natural number is positive).
    Compare with Mathlib's {name}`Nat.add_pos_left`. -/
theorem Nat.add_pos_left {a:Nat} (b:Nat) (ha: a.IsPos) : (a + b).IsPos := by
  -- This proof is written to follow the structure of the original text.
  revert b; apply induction
  . rw [add_zero]
    exact ha
  . intro n ih
    apply (isPos_iff (a+n++)).mpr
    rw [add_succ]
    apply succ_isPos



/-- Compare with Mathlib's {name}`Nat.add_pos_right`.

This theorem is a consequence of the previous theorem and {name}`add_comm`, and {tactic}`grind` can
automatically discover such proofs. -/
theorem Nat.add_pos_right {a:Nat} (b:Nat) (ha: a.IsPos) : (b + a).IsPos := by
  grind [add_comm, add_pos_left]

/-- Corollary 2.2.9 (if sum vanishes, then summands vanish).
    Compare with Mathlib's {name}`Nat.add_eq_zero`. -/
theorem Nat.add_eq_zero (a b:Nat) (hab: a + b = 0) : a = 0 ∧ b = 0 := by
  -- This proof is written to follow the structure of the original text.
  by_contra h
  simp only [not_and_or, ← ne_eq] at h
  obtain ha | hb := h
  . rw [← isPos_iff] at ha
    have hac := add_pos_left b ha
    replace hac := (Nat.isPos_iff (a+b)).mp hac
    contradiction
  rw [← isPos_iff] at hb
  observe : (a + b).IsPos
  contradiction



/-
The API in `Tools/ExistsUnique.Lean`, and the method `existsUnique_of_exists_of_unique` in
particular, may be useful for the next problem.  Also, the `obtain` tactic is
useful for extracting witnesses from existential statements; for instance, `obtain ⟨ x, hx ⟩ := h`
extracts a witness `x` and a proof `hx : P x` of the property from a hypothesis `h : ∃ x, P x`.
-/

#check existsUnique_of_exists_of_unique

theorem Nat.succ_pred (n : Nat) (ha: n.IsPos) : (pred n)++ = n := by
  unfold pred recurse
  cases n with
  | zero => contradiction
  | succ n => simp


/-- Lemma 2.2.10 (unique predecessor) / Exercise 2.2.2 -/
lemma Nat.uniq_succ_eq (a:Nat) (ha: a.IsPos) : ∃! b, b++ = a := by
  replace ha := succ_pred a ha
  apply ExistsUnique.intro (pred a)
  . exact ha
  intro y hb
  rw [← ha] at hb
  exact succ_cancel hb


/-- Definition 2.2.11 (Ordering of the natural numbers).
    This defines the {kw (of := «term_≤_»)}`≤` notation on the natural numbers. -/
instance Nat.instLE : LE Nat where
  le n m := ∃ a:Nat, m = n + a

/-- Definition 2.2.11 (Ordering of the natural numbers).
    This defines the {kw (of := «term_<_»)}`<` notation on the natural numbers. -/
instance Nat.instLT : LT Nat where
  lt n m := n ≤ m ∧ n ≠ m

/-- Compare with Mathlib's {name}`le_iff_exists_add`. -/
lemma Nat.le_iff (n m:Nat) : n ≤ m ↔ ∃ a:Nat, m = n + a := by rfl

lemma Nat.lt_iff (n m:Nat) : n < m ↔ (∃ a:Nat, m = n + a) ∧ n ≠ m := by rfl

/-- Compare with Mathlib's {name}`ge_iff_le`. -/
@[symm]
lemma Nat.ge_iff_le (n m:Nat) : n ≥ m ↔ m ≤ n := by rfl

/-- Compare with Mathlib's {name}`gt_iff_lt`. -/
@[symm]
lemma Nat.gt_iff_lt (n m:Nat) : n > m ↔ m < n := by rfl

/-- Compare with Mathlib's {name}`Nat.le_of_lt`. -/
lemma Nat.le_of_lt {n m:Nat} (hnm: n < m) : n ≤ m := hnm.1

/-- Compare with Mathlib's {name}`Nat.le_iff_lt_or_eq`. -/
lemma Nat.le_iff_lt_or_eq (n m:Nat) : n ≤ m ↔ n < m ∨ n = m := by
  rw [Nat.le_iff]
  rw [Nat.lt_iff]
  by_cases h : n = m
  . simp [h]
    use 0
    rw [add_zero]
  simp [h]

example : (8:Nat) > 5 := by
  rw [Nat.gt_iff_lt]
  rw [Nat.lt_iff]
  constructor
  . use 3
    decide
  decide

/-- Compare with Mathlib's {name}`Nat.lt_succ_self`. -/
@[symm]
theorem Nat.succ_gt_self (n:Nat) : n++ > n := by
  rw [Nat.gt_iff_lt]
  rw [Nat.lt_iff]
  constructor
  . use 1
    apply succ_eq_add_one
  symm
  apply succ_no_fixed_point

/-- Proposition 2.2.12 (Basic properties of order for natural numbers) / Exercise 2.2.3

(a) (Order is reflexive). Compare with Mathlib's {name}`Nat.le_refl`.-/
theorem Nat.ge_refl (a:Nat) : a ≥ a := by
  rw [Nat.ge_iff_le]
  rw [Nat.le_iff]
  use 0
  apply add_comm 0 a


@[refl]
theorem Nat.le_refl (a:Nat) : a ≤ a := a.ge_refl

/-- The refl tag allows for the {tactic}`rfl` tactic to work for inequalities. -/
example (a b:Nat): a+b ≥ a+b := by rfl

/-- (b) (Order is transitive).  The {tactic}`obtain` tactic will be useful here.
    Compare with Mathlib's {name}`Nat.le_trans`. -/
theorem Nat.ge_trans {a b c:Nat} (hab: a ≥ b) (hbc: b ≥ c) : a ≥ c := by
  rw [Nat.ge_iff_le, Nat.le_iff] at hab
  rw [Nat.ge_iff_le, Nat.le_iff] at hbc
  rw [Nat.ge_iff_le, Nat.le_iff]
  obtain ⟨x, hx⟩ := hab
  obtain ⟨y, hy⟩ := hbc
  use y + x
  rw [← add_assoc, ← hy]
  exact hx



theorem Nat.le_trans {a b c:Nat} (hab: a ≤ b) (hbc: b ≤ c) : a ≤ c := Nat.ge_trans hbc hab

/-- (c) (Order is anti-symmetric). Compare with Mathlib's {name}`Nat.le_antisymm`. -/
theorem Nat.ge_antisymm {a b:Nat} (hab: a ≥ b) (hba: b ≥ a) : a = b := by
  rw [Nat.ge_iff_le, Nat.le_iff] at hab
  rw [Nat.ge_iff_le, Nat.le_iff] at hba
  obtain ⟨x, hx⟩ := hab
  obtain ⟨y, hy⟩ := hba
  rw [hx] at hy
  conv at hy =>
    lhs
    rw [← add_zero b]
  rw [add_assoc] at hy
  replace hy := add_left_cancel b 0 (x + y) hy
  symm at hy
  replace hy := add_eq_zero x y hy
  have hz := And.left hy
  rw [hz, add_zero] at hx
  exact hx

theorem Nat.add_term_when_eq (a b c: Nat) (h: a = b):  c + a = c + b := by
  revert c
  apply induction
  . simp
    exact h
  . intro n ih
    rw [succ_add]
    rw [ih]
    rw [← succ_add]

/-- (d) (Addition preserves order).  Compare with Mathlib's {name}`Nat.add_le_add_right`. -/
theorem Nat.add_ge_add_right (a b c:Nat) : a ≥ b ↔ a + c ≥ b + c := by
  constructor
  . intro h1
    rw [Nat.ge_iff_le, Nat.le_iff] at h1
    rw [Nat.ge_iff_le, Nat.le_iff]
    obtain ⟨x, h2⟩ := h1
    use x
    conv =>
      lhs
      rw [add_comm]
    rw [add_assoc]
    conv =>
      rhs
      rw [add_comm]
    conv at h2 =>
      rhs
      rw [add_comm]
    have h3 := add_term_when_eq a (x+b) c h2
    rw [← add_assoc] at h3
    exact h3
  . intro h4
    rw [Nat.ge_iff_le, Nat.le_iff] at h4
    rw [Nat.ge_iff_le, Nat.le_iff]
    obtain ⟨x, h5⟩ := h4
    use x
    rw [add_comm] at h5
    conv at h5 =>
      rhs
      rw [add_assoc]
      rw [add_comm]
    rw [add_assoc] at h5
    have h6 := add_left_cancel c a (x+b) h5
    rw [add_comm] at h6
    exact h6


/-- (d) (Addition preserves order).  Compare with Mathlib's {name}`Nat.add_le_add_left`.  -/
theorem Nat.add_ge_add_left (a b c:Nat) : a ≥ b ↔ c + a ≥ c + b := by
  simp only [add_comm]
  exact add_ge_add_right _ _ _

/-- (d) (Addition preserves order).  Compare with Mathlib's {name}`Nat.add_le_add_right`.  -/
theorem Nat.add_le_add_right (a b c:Nat) : a ≤ b ↔ a + c ≤ b + c := add_ge_add_right _ _ _

/-- (d) (Addition preserves order).  Compare with Mathlib's {name}`Nat.add_le_add_left`.  -/
theorem Nat.add_le_add_left (a b c:Nat) : a ≤ b ↔ c + a ≤ c + b := add_ge_add_left _ _ _

/-- (e) a < b iff a++ ≤ b.  Compare with Mathlib's {name}`Nat.succ_le_iff`. -/
theorem Nat.lt_iff_succ_le (a b:Nat) : a < b ↔ a++ ≤ b := by
  constructor
  . intro h
    rw [lt_iff] at h
    rw [le_iff]
    have h1 := And.left h
    have h3 := And.right h
    obtain ⟨x, h2⟩ := h1
    use x.pred
    by_cases hx : x = 0
    . rw [hx, add_zero] at h2
      rw [h2] at h3
      contradiction
    rw [← ne_eq] at hx
    rw [succ_add, ← add_succ, succ_pred]
    exact h2
    exact hx
  intro h
  rw [le_iff] at h
  rw [lt_iff]
  obtain ⟨x, h4⟩ := h
  rw [succ_add, ← add_succ, succ_eq_add_one] at h4
  constructor
  . use (x + 1)
  by_contra h5
  rw [h5] at h4
  conv at h4 =>
    lhs
    rw [← add_zero b]
  have h6 := add_left_cancel b 0 (x+1) h4
  symm at h6
  replace h6 := add_eq_zero x 1 h6
  have h7 := And.right h6
  contradiction


/-- (f) a < b if and only if b = a + d for positive d. -/
theorem Nat.lt_iff_add_pos (a b:Nat) : a < b ↔ ∃ d:Nat, d.IsPos ∧ b = a + d := by
  constructor
  . intro h
    rw [lt_iff] at h
    obtain ⟨⟨x, h1⟩, h2⟩ := h
    use x
    constructor
    . apply (isPos_iff x).mpr
      by_contra h3
      rw [h3, add_zero] at h1
      rw [h1] at h2
      contradiction
    exact h1
  . intro h
    obtain ⟨x, ⟨ h4, h5 ⟩ ⟩ := h
    rw [lt_iff]
    constructor
    . use x
    replace h4 := (isPos_iff x).mp h4
    by_contra h6
    rw [h6] at h5
    conv at h5 =>
      lhs
      rw [← add_zero b]
    replace h5 := add_left_cancel b 0 x h5
    rw [h5] at h4
    contradiction



/-- If a < b then a ̸= b,-/
theorem Nat.ne_of_lt (a b:Nat) : a < b → a ≠ b := by
  intro h; exact h.2

/-- if a > b then a ̸= b. -/
theorem Nat.ne_of_gt (a b:Nat) : a > b → a ≠ b := by
  intro h; exact h.2.symm

/-- If a > b and a < b then contradiction -/
theorem Nat.not_lt_of_gt (a b:Nat) : a < b ∧ a > b → False := by
  intro h
  have := (ge_antisymm (le_of_lt h.1) (le_of_lt h.2)).symm
  have := ne_of_lt _ _ h.1
  contradiction

theorem Nat.not_lt_self {a: Nat} (h : a < a) : False := by
  apply not_lt_of_gt a a
  simp [h]

theorem Nat.lt_of_le_of_lt {a b c : Nat} (hab: a ≤ b) (hbc: b < c) : a < c := by
  rw [lt_iff_add_pos] at *
  choose d hd using hab
  choose e he1 he2 using hbc
  use d + e; split_ands
  . exact add_pos_right d he1
  . rw [he2, hd, add_assoc]

/-- This lemma was a {lit}`why?` statement from Proposition 2.2.13,
but is more broadly useful, so is extracted here. -/
theorem Nat.zero_le (a:Nat) : 0 ≤ a := by
  rw [le_iff]
  use a
  simp

/-- Proposition 2.2.13 (Trichotomy of order for natural numbers) / Exercise 2.2.4
    Compare with Mathlib's {name}`trichotomous`.  Parts of this theorem have been placed
    in the preceding Lean theorems. -/
theorem Nat.trichotomous (a b:Nat) : a < b ∨ a = b ∨ a > b := by
  -- This proof is written to follow the structure of the original text.
  revert a; apply induction
  . observe why : 0 ≤ b
    tauto
  intro a ih
  obtain case1 | case2 | case3 := ih
  . rw [lt_iff_succ_le] at case1
    tauto
  . have why : a++ > b := by
      rw [gt_iff_lt, lt_iff]
      rw [case2]
      constructor
      . use 1
        apply succ_eq_add_one
      exact (succ_no_fixed_point_all b).symm
    tauto
  have why : a++ > b := by
    have h1 := (succ_gt_self a)
    rw [gt_iff_lt] at *
    exact lt_of_le_of_lt (le_of_lt case3) h1
  tauto

/--
  (Not from textbook) Establish the decidability of this order computably.  The portion of the proof
  involving decidability has been provided; the remaining sorries involve claims about the natural
  numbers.  One could also have established this result by the {tactic}`classical` tactic followed
  by {syntax tactic}`exact Classical.decRel _`, but this would make this definition (as well as some
  instances below) noncomputable.

  Compare with Mathlib's {name}`Nat.decLe`.
-/

theorem Nat.gt_iff_not_le (a b:Nat) : a > b ↔ ¬ a ≤ b := by
  constructor
  . intro h
    rw [le_iff]
    by_contra h
    obtain ⟨x, h1⟩ := h
    rw [gt_iff_lt, lt_iff] at h
    obtain ⟨⟨y,h2⟩, h3⟩ := h
    rw [h1] at h2
    conv at h2 =>
      lhs
      rw [← add_zero a]
    rw [add_assoc] at h2
    have h3 := add_eq_zero x y (add_left_cancel a 0 (x+y) h2).symm
    obtain ⟨h4, h5⟩ := h3
    rw [h4, add_zero a] at h1
    rw [h1] at h3
    contradiction
  . intro h5
    have h6 := trichotomous a b
    rw [le_iff_lt_or_eq, not_or] at h5
    obtain ⟨h7, h8⟩ := h5
    obtain hlt | heq | hgt := h6
    . contradiction
    . contradiction
    . exact hgt




def Nat.decLe : (a b : Nat) → Decidable (a ≤ b)
  | 0, b => by
    apply isTrue
    apply zero_le
  | a++, b => by
    cases decLe a b with
    | isTrue h =>
      cases decEq a b with
      | isTrue h =>
        apply isFalse
        rw [h]
        have h1 := succ_gt_self b
        exact (gt_iff_not_le (b++) b).mp h1
      | isFalse h1 =>
        apply isTrue
        have h2 := (le_iff_lt_or_eq a b).mp h
        obtain h3 | h4 := h2
        . apply (lt_iff_succ_le a b).mp h3
        . contradiction
    | isFalse h =>
      apply isFalse
      by_contra h1
      have h2 := (gt_iff_not_le a b).mpr h
      rw [gt_iff_lt] at h2
      have h3 := lt_of_le_of_lt h1 h2
      have h4 := succ_gt_self a
      rw [gt_iff_lt] at h4
      have h5 := And.intro h4 h3
      apply (not_lt_of_gt a (a++)) h5


instance Nat.decidableRel : DecidableRel (· ≤ · : Nat → Nat → Prop) := Nat.decLe

/-- (Not from textbook) {name}`Nat` has the structure of a linear ordering. This allows for tactics
such as {tactic}`order` and {tactic}`calc` to be applicable to the Chapter 2 natural numbers. -/
instance Nat.instLinearOrder : LinearOrder Nat where
  le_refl := ge_refl
  le_trans a b c hab hbc := ge_trans hbc hab
  lt_iff_le_not_ge a b := by
    constructor
    . intro h1
      refine ⟨le_of_lt   h1, ?_ ⟩
      by_contra h2
      have h3 := not_lt_self (lt_of_le_of_lt h2 h1)
      contradiction
    intro h4
    obtain ⟨h5, h6⟩ := h4
    have h7 := ((gt_iff_not_le b a).mpr h6)
    rw [gt_iff_lt] at h7
    exact h7
  le_antisymm a b hab hba := ge_antisymm hba hab
  le_total a b := by
    by_cases h : a ≤ b
    . left; exact h
    right
    exact le_of_lt ((gt_iff_lt a b).mpr ((gt_iff_not_le a b).mpr h))
  toDecidableLE := decidableRel

/-- This illustration of the {tactic}`order` tactic is not from the
    textbook. -/
example (a b c d:Nat) (hab: a ≤ b) (hbc: b ≤ c) (hcd: c ≤ d)
        (hda: d ≤ a) : a = c := by order

/-- An illustration of the {tactic}`calc` tactic with {kw (of := «term_≤_»)}`≤`/
    {kw (of :=«term_<_»)}`<`. -/
example (a b c d e:Nat) (hab: a ≤ b) (hbc: b < c) (hcd: c ≤ d)
        (hde: d ≤ e) : a + 0 < e := by
  calc
    a + 0 = a := by simp
        _ ≤ b := hab
        _ < c := hbc
        _ ≤ d := hcd
        _ ≤ e := hde

/-- (Not from textbook) {name}`Nat` has the structure of an ordered monoid. This allows for tactics
    such as {tactic}`gcongr` to be applicable to the Chapter 2 natural numbers. -/
instance Nat.isOrderedAddMonoid : IsOrderedAddMonoid Nat where
  add_le_add_left a b hab c := (Nat.add_le_add_right a b c).mp hab

/-- This illustration of the {tactic}`gcongr` tactic is not from the
    textbook. -/
example (a b c d e:Nat) (hab: a ≤ b) (hbc: b < c) (hde: d < e) :
  a + d ≤ c + e := by
  gcongr
  order

/-- Proposition 2.2.14 (Strong principle of induction) / Exercise 2.2.5
    Compare with Mathlib's {name}`Nat.strong_induction_on`.
-/

theorem Nat.zero_is_zero : 0 = zero := by rfl

theorem Nat.succ_lt_iff_le {b a:Nat}: b < a++ ↔ b ≤ a := by
  rw [lt_iff_succ_le]
  have h1 := succ_eq_add_one b
  have h2 := succ_eq_add_one a
  rw [ h1,  h2]
  have h3 := add_ge_add_right a b 1
  have h4 := h3.symm
  simp at h4
  exact h4

theorem Nat.not_lt_iff_le {a b: Nat}:  ¬a < b ↔ b ≤ a := by
  contrapose
  have h := gt_iff_not_le b a
  simp

-- trichotomous
theorem Nat.le_and_ge_iff_eq {a : Nat} {b: Nat}: a ≤ b ∧ b ≤ a ↔ a = b := by
  constructor
  . intro h
    obtain ⟨h1, h2⟩ := h
    rw [← not_lt_iff_le] at h1
    rw [← not_lt_iff_le] at h2
    have h3 := trichotomous a b
    obtain h31 | h32 | h33 := h3
    . contradiction
    . exact h32
    . contradiction
  intro h
  constructor
  . rw [le_iff_lt_or_eq]
    exact Or.inr h
  . rw [le_iff_lt_or_eq]
    exact Or.inr h.symm

theorem Nat.strong_induction_prelude {m₀:Nat} {P: Nat → Prop}
  (hind: ∀ b, 0 ≤ b → (∀ a, 0 ≤ a ∧ a < b → P (m₀ + a)) → P (m₀ + b)) :
    ∀ b, 0 ≤ b → P (m₀ + b) := by
      suffices sh : ∀ n, ∀ a, 0 ≤ a ∧ a < n → P (m₀ + a)
      apply induction
      . intro h
        have h1 := hind 0
        simp at h1
        have h2 := add_zero m₀
        rw [h2]
        exact h1
      intro n
      intro h3
      intro h4
      exact hind (n++) h4 (sh (n++))
      apply induction
      . intro a h
        obtain ⟨h1, h2⟩ := h
        have h3 := lt_of_le_of_lt h1 h2
        contradiction
      intro n h1 a h2
      obtain ⟨ h3, h4⟩ := h2
      have h5 := lt_of_le_of_lt h3 h4
      rw [succ_lt_iff_le] at h5
      have h6 := hind n h5
      by_cases h7 : a = n
      . have h8 := h6 h1
        subst a
        exact h8
      have h9 : a < n := by
        by_contra h10
        rw [not_lt_iff_le] at h10
        rw [succ_lt_iff_le] at h4
        have h11 := And.intro h4 h10
        rw [le_and_ge_iff_eq] at h11
        contradiction
      have h10 := And.intro h3 h9
      exact h1 a h10

theorem Nat.add_gt_add_left (a b c:Nat) : a > b ↔ c + a > c + b := by
  contrapose
  simp
  exact add_le_add_left a b c

theorem Nat.add_lt_add_left (a b c:Nat) : a < b ↔ c + a < c + b := add_gt_add_left _ _ _


theorem Nat.strong_induction {m₀:Nat} {P: Nat → Prop}
  (hind: ∀ m, m ≥ m₀ → (∀ m', m₀ ≤ m' ∧ m' < m → P m') → P m) :
    ∀ m, m ≥ m₀ → P m := by
  intro m h
  have h1 : (∀ b, 0 ≤ b → (∀ a, 0 ≤ a ∧ a < b → P (m₀ + a)) → P (m₀ + b)) := by
    intro b h2 h3
    have h4 := hind (m₀ + b)
    simp at h4
    simp at h3
    rw [add_le_add_left 0 b m₀, add_zero] at h2
    replace h4 := h4 h2
    have h5 :  ∀ (m' : Nat), m₀ ≤ m' → m' < m₀ + b → P m' := by
      intro m' h5 h6
      obtain ⟨a, ha⟩ := (le_iff m₀ m').mp h5
      have hab : a < b := by
        rw [ha, ← add_lt_add_left] at h6
        exact h6
      have hP := h3 a (Nat.zero_le _) hab
      rw [← ha] at hP
      exact hP
    have h6 := h4 h5
    exact h6
  have h2 := strong_induction_prelude h1
  simp at h
  obtain ⟨a, ha⟩ := (le_iff m₀ m).mp h
  have h3 := zero_le a
  have h4 := h2 a h3
  rw [← ha] at h4
  exact h4



/-- Exercise 2.2.6 (backwards induction)
    Compare with Mathlib's {name}`Nat.decreasingInduction`. -/
theorem Nat.backwards_induction {n:Nat} {P: Nat → Prop}
  (hind: ∀ m, P (m++) → P m) (hn: P n) :
    ∀ m, m ≤ n → P m := by
  suffices sh : ∀ a :Nat, ∀ n:Nat, P (n + a) → P (n)
  intro m h
  obtain ⟨a, ha⟩ := (le_iff m n).mp h
  have hb := sh a m
  rw [← ha] at hb
  replace hb := hb hn
  exact hb
  apply induction
  . intro c h
    simp at h
    exact h
  intro c ih d h1
  have h2 := ih (d + 1)
  rw [← one_add,← add_assoc] at h1
  replace h2 := h2 h1
  rw [add_comm, one_add] at h2
  exact (hind d) h2



/-- Exercise 2.2.7 (induction from a starting point)
    Compare with Mathlib's {name}`Nat.le_induction`. -/
theorem Nat.induction_from {n:Nat} {P: Nat → Prop} (hind: ∀ m, P m → P (m++)) :
    P n → ∀ m, m ≥ n → P m := by
  suffices sh : ∀ a :Nat, ∀ n:Nat,  P (n) → P (n + a)
  intro h m h1
  simp at h1
  obtain ⟨a, ha⟩ := (le_iff n m).mp h1
  have h2 := (sh a n) h
  rw [← ha] at h2
  exact h2
  apply induction
  . intro n h1
    simp
    exact h1
  . intro m ih w h1
    have h2 := (ih w) h1
    have h3 := (hind (w+m)) h2
    rw [← one_add,  ← add_assoc]
    rw [← one_add, ← add_assoc] at h3
    rw [add_comm, ← add_assoc, add_comm]
    have h4 : w + m = m + w := by
      rw [add_comm]
    rw  [← h4, ← add_assoc]
    exact h3


end Chapter2
