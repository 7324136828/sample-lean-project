import Mathlib.Tactic
import Analysis.Section_2_3

/-!
# Analysis I, Chapter 2 epilogue: Isomorphism with the Mathlib natural numbers

In this (technical) epilogue, we show that the "Chapter 2" natural numbers {name}`Chapter2.Nat` are
isomorphic in various senses to the standard natural numbers {lean}`ℕ`.

After this epilogue, {name}`Chapter2.Nat` will be deprecated, and we will instead use the standard
natural numbers {lean}`ℕ` throughout.  In particular, one should use the full Mathlib API for {lean}`ℕ` for
all subsequent chapters, in lieu of the {name}`Chapter2.Nat` API.

Filling the sorries here requires both the {name}`Chapter2.Nat` API and the Mathlib API for the standard
natural numbers {lean}`ℕ`.  As such, they are excellent exercises to prepare you for the aforementioned
transition.

In second half of this section we also give a fully axiomatic treatment of the natural numbers
via the Peano axioms. The treatment in the preceding three sections was only partially axiomatic,
because we used a specific construction {name}`Chapter2.Nat` of the natural numbers that was an inductive
type, and used that inductive type to construct a recursor.  Here, we give some exercises to show
how one can accomplish the same tasks directly from the Peano axioms, without knowing the specific
implementation of the natural numbers.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

/-- Converting a Chapter 2 natural number to a Mathlib natural number. -/
abbrev Chapter2.Nat.toNat (n : Chapter2.Nat) : ℕ := match n with
  | zero => 0
  | succ n' => n'.toNat + 1

lemma Chapter2.Nat.zero_toNat : (0 : Chapter2.Nat).toNat = 0 := rfl

lemma Chapter2.Nat.succ_toNat (n : Chapter2.Nat) : (n++).toNat = n.toNat + 1 := rfl

/-- The conversion is a bijection. Here we use the existing capability (from Section 2.1) to map
the Mathlib natural numbers to the Chapter 2 natural numbers. -/
abbrev Chapter2.Nat.equivNat : Chapter2.Nat ≃ ℕ where
  toFun := toNat
  invFun n := (n:Chapter2.Nat)
  left_inv n := by
    induction' n with n hn; rfl
    simp [hn]
    rw [succ_eq_add_one]
  right_inv n := by
    induction' n with n hn; rfl
    simp [←succ_eq_add_one]
    simp [hn]


/-- The conversion preserves addition. -/
abbrev Chapter2.Nat.map_add : ∀ (n m : Nat), (n + m).toNat = n.toNat + m.toNat := by
  intro n m
  induction' n with n hn
  · rw [show zero = 0 from rfl, zero_add, _root_.Nat.zero_add]
  have h1 :  n.toNat + m.toNat =  m.toNat + n.toNat := _root_.Nat.add_comm n.toNat m.toNat
  rw [h1] at hn
  conv =>
    rhs
    rw [succ_toNat, _root_.Nat.add_assoc, _root_.Nat.add_comm,  _root_.Nat.add_assoc, ← hn, _root_.Nat.add_comm]
  have h2 : n++ + m = (n+m)++ := succ_add n m
  rw [h2, succ_toNat]




/-- The conversion preserves multiplication. -/
abbrev Chapter2.Nat.map_mul : ∀ (n m : Nat), (n * m).toNat = n.toNat * m.toNat := by
  intro n m
  induction' n with n hn
  · rw [show zero = 0 from rfl, zero_mul, _root_.Nat.zero_mul]
  conv =>
    rhs
    rw [succ_toNat, _root_.Nat.add_mul, ← hn, _root_.Nat.one_mul, ← Chapter2.Nat.map_add]
  rw [succ_mul]


theorem Chapter2.le_iff : ∀ {n m : Nat}, n.toNat ≤ m.toNat ↔ (∃ d : Nat, n.toNat + d.toNat = m.toNat) := by
  intro n m
  constructor
  · intro h
    -- Mathlib extracts a ℕ-valued gap k with m.toNat = n.toNat + k
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h
    -- Cast k back to Chapter2.Nat; equivNat.right_inv tells us its .toNat equals k
    use (k : Chapter2.Nat)
    have hr := Chapter2.Nat.equivNat.right_inv k
    simp at hr
    omega
  · rintro ⟨d, hd⟩
    omega


/-- The conversion preserves order. -/
abbrev Chapter2.Nat.map_le_map_iff : ∀ {n m : Nat}, n.toNat ≤ m.toNat ↔ n ≤ m := by
  intro n m
  constructor
  . intro h1
    rw [Chapter2.le_iff] at h1
    rw [le_iff]
    obtain ⟨d, h2⟩ := h1
    use d
    rw [← Chapter2.Nat.map_add] at h2
    have h3 := congr(Chapter2.Nat.equivNat.invFun $h2)
    rw [Chapter2.Nat.equivNat.left_inv] at h3
    conv at h3 =>
      rhs
      rw [Chapter2.Nat.equivNat.left_inv]
    rw [h3]
  intro h1
  rw [le_iff] at h1
  rw [Chapter2.le_iff]
  obtain ⟨d, h2⟩ := h1
  use d
  rw [← Chapter2.Nat.map_add]
  have h3 := congr(Chapter2.Nat.equivNat.toFun $h2)
  simp at h3
  rw [h3]


abbrev Chapter2.Nat.equivNat_ordered_ring : Chapter2.Nat ≃+*o ℕ where
  toEquiv := equivNat
  map_add' := map_add
  map_mul' := map_mul
  map_le_map_iff' := map_le_map_iff

/-- The conversion preserves exponentiation. -/
lemma Chapter2.Nat.pow_eq_pow (n m : Chapter2.Nat) :
    n.toNat ^ m.toNat = (n^m).toNat := by
  induction' m with m ih
  . have h1 : n ^ zero = 1 := by
      rw [← zero_is_zero, pow_zero]
    have h2 : n.toNat ^ zero.toNat = (succ zero).toNat := by
      rw [succ_toNat, _root_.Nat.zero_add,  _root_.Nat.pow_zero]
    rw [h1, h2]
  rw [_root_.Nat.pow_succ]
  conv =>
    rhs
    rw [pow_succ, map_mul]
  rw [ih]


/-- The Peano axioms for an abstract type {name}`Nat` -/
@[ext]
structure PeanoAxioms where
  Nat : Type
  zero : Nat -- Axiom 2.1
  succ : Nat → Nat -- Axiom 2.2
  succ_ne : ∀ n : Nat, succ n ≠ zero -- Axiom 2.3
  succ_cancel : ∀ {n m : Nat}, succ n = succ m → n = m -- Axiom 2.4
  induction : ∀ (P : Nat → Prop),
    P zero → (∀ n : Nat, P n → P (succ n)) → ∀ n : Nat, P n -- Axiom 2.5

namespace PeanoAxioms

/-- The Chapter 2 natural numbers obey the Peano axioms. -/
def Chapter2_Nat : PeanoAxioms where
  Nat := Chapter2.Nat
  zero := Chapter2.Nat.zero
  succ := Chapter2.Nat.succ
  succ_ne := Chapter2.Nat.succ_ne
  succ_cancel := Chapter2.Nat.succ_cancel
  induction := Chapter2.Nat.induction

/-- The Mathlib natural numbers obey the Peano axioms. -/
def Mathlib_Nat : PeanoAxioms where
  Nat := ℕ
  zero := 0
  succ := Nat.succ
  succ_ne := Nat.succ_ne_zero
  succ_cancel := Nat.succ_inj.mp
  induction _ := Nat.rec

/-- One can map the Mathlib natural numbers into any other structure obeying the Peano axioms. -/
abbrev natCast (P : PeanoAxioms) : ℕ → P.Nat := fun n ↦ match n with
  | Nat.zero => P.zero
  | Nat.succ n => P.succ (natCast P n)


theorem simplify (n : Chapter2.Nat) : n ≠ 0 ↔ ∃ b, ((b++) = n) := by
  contrapose
  constructor
  . intro h
    rw [h]
    exact Chapter2.Nat.no_succ_is_zero
  contrapose
  intro h
  rw [← ne_eq] at h
  use n.pred
  rw [← Chapter2.Nat.isPos_iff] at h
  exact Chapter2.Nat.succ_pred n h

theorem simplify_contrapose (n : Chapter2.Nat) : n = 0 ↔ ∀ b, ((b++) ≠ n) := by
  contrapose
  push_neg
  apply simplify


theorem not_equal_Nat_simplify (n m : Chapter2.Nat) : n ≠ m ↔ n.toNat ≠ m.toNat := by
  contrapose
  constructor
  . intro h
    have h1 := congr(Chapter2.Nat.equivNat.toFun $h)
    simp at h1
    exact h1
  intro h
  have h1 := congr(Chapter2.Nat.equivNat.invFun $h)
  simp at h1
  have h2 := Chapter2.Nat.equivNat.left_inv n
  have h3 := Chapter2.Nat.equivNat.left_inv m
  simp at h2 h3
  rw [← h2, ← h3]
  exact h1

theorem not_equal_N_simplify (n m : ℕ) :  (n:Chapter2.Nat) ≠  (m:Chapter2.Nat) ↔ n ≠ m := by
  constructor
  . intro h1
    by_contra h2
    have h3 :=  congr(Chapter2.Nat.equivNat.invFun $h2)
    simp at h3
    contradiction
  intro h1
  by_contra h2
  have h3 := congr(Chapter2.Nat.equivNat.toFun $h2)
  simp at h3
  have h4 := Chapter2.Nat.equivNat.right_inv n
  have h5 := Chapter2.Nat.equivNat.right_inv m
  simp at h4 h5
  rw [h4, h5] at h3
  contradiction



theorem simplify_Nat (n : ℕ) : n ≠ 0 ↔ ∃ b:ℕ, (Nat.succ b = n) := by
  contrapose
  push_neg
  constructor
  intro h
  have h1 := congr(Chapter2.Nat.equivNat.invFun $h)
  simp at h1
  have h2 := (simplify_contrapose n).mp h1
  simp at h2
  by_contra h3
  push_neg at h3
  obtain ⟨b, h4⟩ := h3
  replace h4 := congr(Chapter2.Nat.equivNat.invFun $h4)
  simp at h4
  have h5 := h2 b
  push_neg at h5
  rw [Chapter2.Nat.succ_eq_add_one] at h5
  contradiction
  contrapose
  push_neg
  intro h
  have h6 := ((not_equal_N_simplify n 0).mpr h)
  simp at h6
  have h7 := (simplify n).mp
  simp at h7
  have h8 := h7 h6
  obtain ⟨b, h9⟩ := h8
  use b.toNat
  simp
  replace h9 := congr(Chapter2.Nat.equivNat.toFun $h9)
  simp at h9
  rw [Chapter2.Nat.succ_toNat] at h9
  rw [h9]
  have h10 := Chapter2.Nat.equivNat.right_inv n
  simp at h10
  exact h10



/-- One can start the proof here with {syntax tactic}`unfold Function.Injective`, although it is not strictly necessary. -/
theorem natCast_injective (P : PeanoAxioms) : Function.Injective P.natCast := by
  unfold Function.Injective
  intro a
  induction' a with a ih
  . intro b h
    rw [natCast] at h
    by_contra h1
    rw [← ne_eq] at h1
    replace h1 := h1.symm
    have h2 := (simplify_Nat b).mp h1
    obtain ⟨c, h3⟩ := h2
    rw [← h3] at h
    conv at h =>
      rhs
      rw [natCast]
    have h4 := PeanoAxioms.succ_ne P (P.natCast c)
    replace h := h.symm
    contradiction
  intro b h
  rw [← Nat.succ_eq_add_one] at h
  rw [natCast] at h
  by_cases h1 : b = 0
  . rw [h1] at h
    conv at h =>
      rhs
      rw [natCast]
    have h4 := PeanoAxioms.succ_ne P (P.natCast a)
    contradiction
  push_neg at h1
  have h5 := (simplify_Nat b).mp h1
  obtain ⟨c, h6⟩ := h5
  rw [← h6] at h
  conv at h =>
    rw [natCast]
  have h7 := PeanoAxioms.succ_cancel P h
  have h8 := ih h7
  have h9 := congr(Nat.succ $h8)
  rw [h6] at h9
  simp at h9
  exact h9

theorem peanoAxioms_not_equal_zero_exists_prefix (P : PeanoAxioms) (b : P.Nat) :  b ≠ P.zero ↔ ∃ c, P.succ c = b := by
  constructor
  revert b
  apply P.induction
  . intro h
    contradiction
  intro n ih h
  use n
  revert b
  apply P.induction
  . intro h
    obtain ⟨c, h1 ⟩ := h
    have h2 := P.succ_ne c
    contradiction
  intro n ih h
  have h2 := PeanoAxioms.succ_ne P n
  exact h2


/-- One can start the proof here with {syntax tactic}`unfold Function.Surjective`, although it is not strictly necessary. -/
theorem natCast_surjective (P : PeanoAxioms) : Function.Surjective P.natCast := by
  unfold Function.Surjective
  apply P.induction
  . use 0
  intro n ih
  obtain ⟨a, h⟩ := ih
  use (a.succ)
  rw [natCast]
  rw [h]



/-- The notion of an equivalence between two structures obeying the Peano axioms.
    The symbol {kw (of := «term_≃_»)}`≃` is an alias for Mathlib's {name}`Equiv` class; for instance {lean}`P.Nat ≃ Q.Nat` is
    an alias for {lean}`_root_.Equiv P.Nat Q.Nat`. -/
class Equiv (P Q : PeanoAxioms) where
  equiv : P.Nat ≃ Q.Nat
  equiv_zero : equiv P.zero = Q.zero
  equiv_succ : ∀ n : P.Nat, equiv (P.succ n) = Q.succ (equiv n)

/-- This exercise will require application of Mathlib's API for the {name}`Equiv` class.
    Some of this API can be invoked automatically via the {tactic}`simp` tactic. -/
abbrev Equiv.symm {P Q: PeanoAxioms} (equiv : Equiv P Q) : Equiv Q P where
  equiv := equiv.equiv.symm
  equiv_zero := by
    have eq := equiv.equiv_zero
    rw [← eq]
    simp
  equiv_succ n := by
    have zero := equiv.equiv_zero
    have succ := equiv.equiv_succ
    revert n
    apply Q.induction
    . have h1 := succ (Equiv.equiv.symm Q.zero)
      simp at h1
      rw [← h1]
      simp
    intro n ih
    have h1 := succ (Equiv.equiv.symm (Q.succ n))
    simp at h1
    rw [← h1]
    simp

/-- This exercise will require application of Mathlib's API for the {name}`Equiv` class.
    Some of this API can be invoked automatically via the {tactic}`simp` tactic. -/
abbrev Equiv.trans {P Q R: PeanoAxioms} (equiv1 : Equiv P Q) (equiv2 : Equiv Q R) : Equiv P R where
  equiv := equiv1.equiv.trans equiv2.equiv
  equiv_zero := by
    have zero1 := equiv1.equiv_zero
    have zero2 := equiv2.equiv_zero
    simp
    rw [zero1, zero2]
  equiv_succ n := by
    have zero1 := equiv1.equiv_zero
    have zero2 := equiv2.equiv_zero
    have succ1 := equiv1.equiv_succ
    have succ2 := equiv2.equiv_succ
    simp
    have succ3 := succ1 n
    rw [succ3]
    have succ4 := succ2 (equiv n)
    rw [succ4]


theorem natCast_bijective (P : PeanoAxioms) : Function.Bijective P.natCast := by
  unfold Function.Bijective
  constructor
  . exact natCast_injective P
  exact natCast_surjective P



/-- Useful Mathlib tools for inverting bijections include {name}`Function.surjInv` and {name}`Function.invFun`. -/
noncomputable abbrev Equiv.fromNat (P : PeanoAxioms) : Equiv Mathlib_Nat P where
  equiv := {
    toFun := P.natCast
    invFun := Function.surjInv (natCast_surjective P)
    left_inv := by
      have h := Function.leftInverse_surjInv (natCast_bijective P)
      exact h
    right_inv := by
      have h := Function.rightInverse_surjInv (natCast_surjective P)
      exact h
  }
  equiv_zero := by rfl
  equiv_succ n := by rfl

/-- The task here is to establish that any two structures obeying the Peano axioms are equivalent. -/
noncomputable abbrev Equiv.mk' (P Q : PeanoAxioms) : Equiv P Q := by
  have h1 := Equiv.fromNat P
  have h2 := Equiv.fromNat Q
  have h3 := h1.symm
  have h4 := Equiv.trans h3 h2
  exact h4

/-- There is only one equivalence between any two structures obeying the Peano axioms. -/
theorem Equiv.uniq {P Q : PeanoAxioms} (equiv1 equiv2 : PeanoAxioms.Equiv P Q) :
    equiv1 = equiv2 := by
  obtain ⟨equiv1, equiv_zero1, equiv_succ1⟩ := equiv1
  obtain ⟨equiv2, equiv_zero2, equiv_succ2⟩ := equiv2
  congr
  ext n
  revert n
  apply P.induction
  . rw [equiv_zero1, equiv_zero2]
  intro n ih
  have s1 := equiv_succ1 n
  have s2 := equiv_succ2 n
  rw [s1, ih, s2]


noncomputable def Nat.recurse_uniq.f1 {P : PeanoAxioms} (f : P.Nat → P.Nat → P.Nat) (c : P.Nat) :
    Mathlib_Nat.Nat → P.Nat
  | (0:) => c
  | .succ k => f (P.natCast k) (Nat.recurse_uniq.f1 f c k)


/-- A sample result: recursion is well-defined on any structure obeying the Peano axioms-/
theorem Nat.recurse_uniq {P : PeanoAxioms} (f: P.Nat → P.Nat → P.Nat) (c: P.Nat) :
    ∃! (a: P.Nat → P.Nat), a P.zero = c ∧ ∀ n, a (P.succ n) = f n (a n) := by
    have h33 : ∀x, Mathlib_Nat.succ x = x.succ := by
      intro x
      rfl
    let iv := (Equiv.fromNat P).equiv.invFun
    have h55 (n): P.natCast (iv n) = n := by
      unfold iv
      exact (Equiv.fromNat P).equiv.apply_symm_apply n
    unfold iv at h55
    simp at h55
    have zero := (Equiv.fromNat P).equiv_zero
    have zero_iv := congr(iv $zero)
    have succ :=  (Equiv.fromNat P).equiv_succ
    unfold iv at zero_iv
    simp at zero_iv
    let f2 : P.Nat → P.Nat := fun n ↦ Nat.recurse_uniq.f1 f c (iv n)
    apply ExistsUnique.intro f2
    . constructor
      . unfold f2 iv
        simp
        rw [zero_iv.symm]
        unfold Nat.recurse_uniq.f1
        rfl
      intro n
      unfold f2 iv
      simp
      have succ_iv := congrArg iv (succ (iv n))
      unfold iv at succ_iv
      simp at succ_iv
      rw [← succ_iv]
      have h4 := h33 (iv n)
      unfold iv at h4
      conv at h4 =>
        lhs
        simp
      conv =>
        lhs
        rw [h4]
        unfold recurse_uniq.f1
        simp
      conv =>
        lhs
        rw [h55]
    intro f3 h
    obtain ⟨h1, h2⟩ := h
    ext n
    revert n
    apply P.induction
    . rw [h1]
      unfold f2
      unfold iv
      have h3 := (Equiv.fromNat P).equiv_zero
      rw [← h3]
      simp
      unfold recurse_uniq.f1
      rfl
    intro n ih
    have h3 := h2 n
    rw [h3, ih]
    have succ_iv := congrArg iv (succ (iv n))
    unfold iv at succ_iv
    simp at succ_iv
    have h4 := h33 (iv n)
    unfold iv at h4
    conv at h4 =>
        lhs
        simp
    conv =>
      rhs
      unfold f2 iv
      simp
      rw [← succ_iv]
      rw [h4]
      unfold recurse_uniq.f1
      simp
      rw [h55]
    unfold f2 iv
    simp





end PeanoAxioms
