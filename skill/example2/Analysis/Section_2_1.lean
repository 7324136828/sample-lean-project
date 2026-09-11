import Mathlib.Tactic

/-!
# Analysis I, Section 2.1: The Peano Axioms

This file is a translation of Section 2.1 of Analysis I to Lean 4.  All numbering refers to the
original text.

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided doing
so.

Main constructions and results of this section:

- Definition of the "Chapter 2" natural numbers, `Chapter2.Nat`,abbreviated as {name}`Nat` within
  the Chapter2 namespace. (In the book, the natural numbers are treated in a purely axiomatic
  fashion, as a type that obeys the Peano axioms; but here we take advantage of Lean's native
  inductive types to explicitly construct a version of the natural numbers that obey those axioms.
  One could also proceed more axiomatically, as is done in Section 3 for set theory: see the
  epilogue to this chapter.)
- Establishment of the Peano axioms for `Chapter2.Nat`.
- Recursive definitions for `Chapter2.Nat`.

Note: at the end of this chapter, the `Chapter2.Nat` class will be deprecated in favor of the
standard Mathlib class {name}`_root_.Nat`, or {lean}`ℕ`.  However, we will develop the properties of
`Chapter2.Nat` "by hand" in the next few sections for pedagogical purposes.

-/

namespace Chapter2

/--
  Assumption 2.6 (Existence of natural numbers). Here we use an explicit construction of the
  natural numbers (using an inductive type). For a more axiomatic approach, see the epilogue to
  this chapter.
-/
inductive Nat where
| zero : Nat
| succ : Nat → Nat
deriving Repr, DecidableEq  -- this allows `decide` to work on `Nat`

/-- Axiom 2.1 (0 is a natural number) -/
instance Nat.instZero : Zero Nat := ⟨ zero ⟩
#check (0:Nat)

/-- Axiom 2.2 (Successor of a natural number is a natural number) -/
postfix:100 "++" => Nat.succ
#check (fun n ↦ n++)


/-- Definition 2.1.3 (Definition of the numerals 0, 1, 2, etc.). Note: to avoid ambiguity, one may
  need to use explicit casts such as {lean}`(0:Nat)`, {lean}`(1:Nat)`, etc. to refer to this
  chapter's version of the natural numbers.  -/
instance Nat.instOfNat {n:_root_.Nat} : OfNat Nat n where
  ofNat := _root_.Nat.rec 0 (fun _ n ↦ n++) n

instance Nat.instOne : One Nat := ⟨ 1 ⟩
lemma Nat.zero_succ : 0++ = 1 := by rfl
#check (1:Nat)

lemma Nat.one_succ : 1++ = 2 := by rfl
#check (2:Nat)

/-- Proposition 2.1.4 (3 is a natural number)-/
lemma Nat.two_succ : 2++ = 3 := by rfl
#check (3:Nat)

lemma Nat.three_succ : 3++ = 4 := by rfl


lemma Nat.three_not_equal_zero : succ zero ≠ zero := by
  by_contra h
  injection h

lemma Nat.success_equal (n m :Nat) (h: n++=m++) : n = m := by
  injection h

/--
  Axiom 2.3 (0 is not the successor of any natural number).
  Compare with Lean's {name}`Nat.succ_ne_zero`.
-/
theorem Nat.succ_ne (n:Nat) : n++ ≠ 0 := by
  by_contra h
  injection h


/-- Proposition 2.1.6 (4 is not equal to zero) -/
theorem Nat.four_ne : (4:Nat) ≠ 0 := by
  -- By definition, 4 = 3++.
  change 3++ ≠ 0
  -- By axiom 2.3, 3++ is not zero.
  exact succ_ne _

/--
  Axiom 2.4 (Different natural numbers have different successors).
  Compare with Mathlib's {name}`Nat.succ_inj`.
-/
theorem Nat.succ_cancel {n m:Nat} (hnm: n++ = m++) : n = m := by
  injection hnm

/--
  Axiom 2.4 (Different natural numbers have different successors).
  Compare with Mathlib's {name}`Nat.succ_ne_succ`.
-/
theorem Nat.succ_ne_succ (n m:Nat) : n ≠ m → n++ ≠ m++ := by
  intro h
  contrapose! h
  exact succ_cancel h

theorem Nat.three_ne_two : (3:Nat) ≠ 2 := by
  by_contra h
  change 0++++++ = 0++++ at h
  apply succ_cancel at h
  apply succ_cancel at h
  have := succ_ne
  contradiction


/-- Proposition 2.1.8 (6 is not equal to 2) -/
theorem Nat.six_ne_two : (6:Nat) ≠ 2 := by
-- this proof is written to follow the structure of the original text.
  by_contra h
  change 5++ = 1++ at h
  apply succ_cancel at h
  change 4++ = 0++ at h
  apply succ_cancel at h
  have := four_ne
  contradiction

/-- One can also prove this sort of result by the {tactic}`decide` tactic -/
theorem Nat.six_ne_two' : (6:Nat) ≠ 2 := by
  decide

/-- Axiom 2.5 (Principle of mathematical induction). The {tactic}`induction` (or
  {tactic}`induction'`) tactic in Mathlib serves as a substitute for this axiom.  -/
theorem Nat.induction (P : Nat → Prop) (hbase : P 0) (hind : ∀ n, P n → P (n++)) :
    ∀ n, P n := by
  intro n
  induction n with
  | zero => exact hbase
  | succ n ih => exact hind n ih

theorem Nat.induction.constant (f : Nat → Nat) (hbase : f 0 = 0) (hind : ∀ n, f n = 0 → f (n++) = 0) :
    ∀ n, f n = 0 := by
    apply induction
    exact hbase
    exact hind


/--
  Recursion. Analogous to the inbuilt Mathlib method {name}`Nat.rec` associated to
  the Mathlib natural numbers
-/
abbrev Nat.recurse (f: Nat → Nat → Nat) (c: Nat) : Nat → Nat := fun n ↦ match n with
| 0 => c
| n++ => f n (recurse f c n)

/-- Proposition 2.1.16 (recursive definitions). Compare with Mathlib's {name}`Nat.rec_zero`. -/
theorem Nat.recurse_zero (f: Nat → Nat → Nat) (c: Nat) : Nat.recurse f c 0 = c := by constructor

/-- Proposition 2.1.16 (recursive definitions). Compare with Mathlib's {name}`Nat.rec_add_one`. -/
theorem Nat.recurse_succ (f: Nat → Nat → Nat) (c: Nat) (n: Nat) :
    recurse f c (n++) = f n (recurse f c n) := by constructor

/-- Proposition 2.1.16 (recursive definitions). -/
theorem Nat.eq_recurse (f: Nat → Nat → Nat) (c: Nat) (a: Nat → Nat) :
    (a 0 = c ∧ ∀ n, a (n++) = f n (a n)) ↔ a = recurse f c := by
  constructor
  . intro ⟨h1, h2⟩
    apply funext
    apply induction
    apply h1
    intro n h3
    rw [h2, h3, recurse_succ]
  . intro h4
    constructor
    . rw [h4, recurse_zero]
    . intro n
      rw [h4, recurse_succ]


/-- Proposition 2.1.16 (recursive definitions). -/
theorem Nat.recurse_uniq (f: Nat → Nat → Nat) (c: Nat) :
    ∃! (a: Nat → Nat), a 0 = c ∧ ∀ n, a (n++) = f n (a n) := by
  apply ExistsUnique.intro (recurse f c)
  . constructor
    exact recurse_zero _ _
    exact recurse_succ _ _
  intro y
  exact (eq_recurse _ _ _).mp



theorem Nat.succ_succ_cancel {n m : Nat} (h : n++++ = m++++) : n = m := by
  apply success_equal
  apply success_equal
  apply h


/-- Exercise A.2 (★). Restate Axiom 2.3 in "no witness" form. -/
theorem Nat.no_succ_is_zero : ¬ ∃ n : Nat, n++ = 0 := by
  by_contra h
  rcases h with ⟨n, hn⟩
  apply succ_ne
  injection hn
  exact n

theorem Nat.ne_of_succ_ne (n m : Nat) : n++ ≠ m++ → n ≠ m := by
  intro h
  contrapose! h
  rw [h]

theorem Nat.seven_ne_three : (7 : Nat) ≠ 3 := by
  decide

theorem Nat.hundred_ne_ninety_nine : (100 : Nat) ≠ 99 := by
  decide

/- ========================================================================
   Part B: First inductions
   ======================================================================== -/

/-- Exercise B.1 (★★). No natural number is its own successor.
    (Note: this does NOT follow from Axioms 2.1–2.4 alone — you need
    induction. As a thought experiment, find a structure satisfying
    Axioms 2.1–2.4 in which some element *is* its own successor.) -/
theorem Nat.succ_no_fixed_point : ∀n, n++ ≠ n := by
  apply induction
  . apply succ_ne
  . intro n
    apply succ_ne_succ

theorem Nat.succ_no_fixed_point_all (n : Nat) : n++ ≠ n := by
  apply succ_no_fixed_point



/-- Exercise B.2 (★★). No cycles of length two either. Careful: the obvious
    induction hypothesis may not be strong enough. -/
theorem Nat.succ_succ_no_fixed_point (n : Nat) : n++++ ≠ n := by
  revert n
  apply induction
  . decide
  . intro n
    apply succ_ne_succ


theorem Nat.existence_of_success (n : Nat): ∃ m, n++ = m++ := by
  use n

/-- Exercise B.3 (★★). Every natural number is either zero or a successor.
    (Tao alludes to this in the text; here it must be *proved*, e.g. by
    induction or by `cases`. Try to do it via `Nat.induction` for practice.) -/
theorem Nat.eq_zero_or_eq_succ (n : Nat) : n = 0 ∨ ∃ m : Nat, n = m++ := by
  revert n
  apply induction
  . apply Or.inl
    decide
  . intro n h
    apply Or.inr
    use n



/-- Exercise B.4 (★★). The successor function is injective but NOT surjective.
    Which axiom is each half of this statement really about? -/
theorem Nat.succ_injective_not_surjective :
    Function.Injective Nat.succ ∧ ¬ Function.Surjective Nat.succ := by
  constructor
  . unfold Function.Injective
    apply succ_cancel
  . unfold Function.Surjective
    push_neg
    use 0
    apply succ_ne



/-- Exercise B.5 (★★★). A "two-step" induction principle: if a property holds
    at 0 and 1, and propagates from `n` to `n++++`, then it holds everywhere.
    Hint: you cannot apply `Nat.induction` to `P` directly — strengthen the
    property first. -/
theorem Nat.induction_two_step (P : Nat → Prop)
    (h0 : P 0) (h1 : P 1) (hstep : ∀ n, P n → P (n++++)) :
    ∀ n, P n := by
  have hQ : ∀ n, P n ∧ P (n++) := by
    apply induction
    · exact ⟨h0, h1⟩
    · intro n ⟨hn, hsucc⟩
      exact ⟨hsucc, hstep n hn⟩
  intro n
  exact (hQ n).1









/- ========================================================================
   Part C: Playing with `recurse`
   ======================================================================== -/

/-- Exercise C.1 (★). Define the predecessor function using `recurse` (and
    nothing else — no pattern matching!), with the convention `pred 0 = 0`. -/
def Nat.pred : Nat → Nat := recurse (fun n _ => n) 0

/-- Exercise C.1a (★). Your definition should satisfy this. -/
theorem Nat.pred_zero : pred 0 = 0 := by
  decide

/-- Exercise C.1b (★). ... and this. -/
theorem Nat.pred_succ (n : Nat) : pred (n++) = n := by
  rfl


-- theorem Nat.pred_succ (n : Nat) : pred (n++) = n := by
--   rw [pred, recurse]
--   intro m r
--   apply n

/-- Exercise C.1c (★★). Use `pred` to give a *second* proof that successor is
    injective, i.e. re-derive Axiom 2.4 from Exercise C.1b. Moral: a function
    with a left inverse is injective. -/
theorem Nat.succ_cancel' {n m : Nat} (h : n++ = m++) : n = m := by
  have h2 := pred_succ n
  have h3 := pred_succ m
  rw [← h2, ← h3, h]



/-- Exercise C.2 (★). Define an "is zero" indicator using `recurse`:
    `isZero 0 = 1` and `isZero (n++) = 0`. -/
def Nat.isZero : Nat → Nat := recurse (fun _ _ => 0) 1

/-- Exercise C.2a (★★). Prove the indicator is correct. -/
theorem Nat.isZero_correct (n : Nat) : n = 0 ↔ isZero n = 1 := by
  constructor
  · intro h
    rw [h]
    decide
  · intro h
    cases n with
    | zero => rfl
    | succ n =>
      unfold isZero recurse at h
      simp at h

/-- Exercise C.3 (★★). Define iteration: `iterate f n m` applies `f` to `m`
    exactly `n` times. Use `recurse`. (Note the order of arguments!) -/
def Nat.iterate (f : Nat → Nat) (n m : Nat) : Nat := recurse (fun _ b => f b) m n

/-- Exercise C.3a (★). Iterating zero times does nothing. -/
theorem Nat.iterate_zero (f : Nat → Nat) (m : Nat) : iterate f 0 m = m := by
  rfl

/-- Exercise C.3b (★★). Iterating the successor function starting from 0
    recovers the number itself. -/
theorem Nat.iterate_succ_from_zero (n : Nat) : iterate Nat.succ n 0 = n := by
  revert n
  apply induction
  · rfl
  · intro n ih
    exact congrArg Nat.succ ih


/-- Exercise C.3c (★★★). Iterates of the same function commute:
    applying f once more at the "inside" or the "outside" is the same. -/
theorem Nat.iterate_comm (f : Nat → Nat) (n m : Nat) :
    iterate f n (f m) = f (iterate f n m) := by
  revert n
  apply induction
  . rfl
  . intro n h
    unfold iterate
    unfold recurse
    unfold iterate at h
    rw [h]





/-- Exercise C.4 (★★). If two recursion data agree, so do the recursions.
    (A congruence lemma for `recurse`, proved from its defining equations
    rather than by unfolding.) -/
theorem Nat.recurse_congr (f g : Nat → Nat → Nat) (c d : Nat)
    (hf : ∀ n m, f n m = g n m) (hc : c = d) :
    ∀ n, recurse f c n = recurse g d n := by
    apply induction
    . unfold recurse
      exact hc
    . intro n h1
      unfold recurse
      rw [h1]
      apply hf



/-- Exercise C.5 (★★★). A function that satisfies its own recursion equation
    with a "shifted" base must be `recurse` in disguise: if `a 1 = c` and
    `a (n++++) = f n (a (n++))` hold, then `a (n++) = recurse f c n` for all n.
    Hint: consider the function `b n := a (n++)`. -/
theorem Nat.shifted_recursion (f : Nat → Nat → Nat) (c : Nat) (a : Nat → Nat)
    (h1 : a 1 = c) (hstep : ∀ n, a (n++++) = f n (a (n++))) :
    ∀ n, a (n++) = recurse f c n := by
  sorry

/- ========================================================================
   Part D: Previews and challenges
   ======================================================================== -/

/-- Exercise D.1 (★★). A sneak preview of Section 2.2: define addition via
    `recurse`, so that `add 0 m = m` and `add (n++) m = (add n m)++`. -/
def Nat.add' : Nat → Nat → Nat := sorry

/-- Exercise D.1a (★). The defining equations hold. -/
theorem Nat.add'_zero (m : Nat) : add' 0 m = m := by
  sorry

theorem Nat.add'_succ (n m : Nat) : add' (n++) m = (add' n m)++ := by
  sorry

/-- Exercise D.1b (★★). The *other* base case needs induction. Why? -/
theorem Nat.zero_add' (n : Nat) : add' n 0 = n := by
  sorry

/-- Exercise D.2 (★★★). Define `swap : Nat → Nat` that exchanges 0 and 1 and
    fixes everything else — using only `recurse` (no `if`, no `match`).
    Then show it is an involution. Hint: the first argument that `recurse`
    feeds to `f` is the *predecessor*; exploit it. -/
def Nat.swap : Nat → Nat := sorry

theorem Nat.swap_swap (n : Nat) : swap (swap n) = n := by
  sorry

/-- Exercise D.3 (★★★). The Chapter 2 naturals are "the same as" Mathlib's.
    Construct explicit translations in both directions and show they are
    mutually inverse. (This foreshadows the epilogue's claim that the Peano
    axioms pin down the natural numbers up to isomorphism.) -/
def Nat.toMathlib : Nat → _root_.Nat := sorry

def Nat.ofMathlib : _root_.Nat → Nat := sorry

theorem Nat.toMathlib_ofMathlib (n : _root_.Nat) : toMathlib (ofMathlib n) = n := by
  sorry

theorem Nat.ofMathlib_toMathlib (n : Nat) : ofMathlib (toMathlib n) = n := by
  sorry

/-- Exercise D.3a (★). Conclude that the translation is a bijection. -/
theorem Nat.toMathlib_bijective : Function.Bijective Nat.toMathlib := by
  sorry



end Chapter2
