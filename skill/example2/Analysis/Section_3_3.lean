import Mathlib.Tactic
import Analysis.Section_3_1
import Analysis.Tools.ExistsUnique

set_option doc.verso.suggestions false

/-!
# Analysis I, Section 3.3: Functions

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- A notion of function `Function X Y` between two sets `X`, `Y` in the set theory of Section 3.1
- Various relations with the Mathlib notion of a function `X → Y` between two types `X`, `Y`.
  (Note from Section 3.1 that every `Set` `X` can also be viewed as a subtype
  `{x : Object // x ∈ X }` of `Object`.)
- Basic function properties and operations, such as composition, one-to-one and onto functions,
  and inverses.

In the rest of the book we will deprecate the Chapter 3 version of a function, and work with the
Mathlib notion of a function instead.  Even within this section, we will switch to the Mathlib
formalism for some of the examples involving number systems such as {lean}`ℤ` or {lean}`ℝ` that have not been
implemented in the Chapter 3 framework.

We will work here with the version {name}`Nat` of the natural numbers internal to the Chapter 3 set
theory, though usually we will use coercions to then immediately translate to the Mathlib
natural numbers {lean}`ℕ`.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/


namespace Chapter3

export SetTheory (Set Object)

variable [SetTheory]

/--
  Definition 3.3.1. {lean}`Function X Y` is the structure of functions from {lean}`X` to {lean}`Y`.
  Analogous to the Mathlib type {lean}`X → Y`.
-/
@[ext]
structure Function (X Y: Set) where
  P : X → Y → Prop
  unique : ∀ x: X, ∃! y: Y, P x y

#check Function.mk

/--
  Converting a Chapter 3 function {lean}`f: Function X Y` to a Mathlib function {lean}`f: X → Y`.
  The Chapter 3 definition of a function was nonconstructive, so we have to use the
  axiom of choice here.
-/
noncomputable def Function.to_fn {X Y: Set} (f: Function X Y) : X → Y :=
  fun x ↦ (f.unique x).choose

noncomputable instance Function.inst_coefn (X Y: Set) : CoeFun (Function X Y) (fun _ ↦ X → Y) where
  coe := Function.to_fn

theorem Function.to_fn_eval {X Y: Set} (f: Function X Y) (x:X) : f.to_fn x = f x := rfl

/-- Converting a Mathlib function to a Chapter 3 {name}`Function` -/
abbrev Function.mk_fn {X Y: Set} (f: X → Y) : Function X Y :=
  Function.mk (fun x y ↦ y = f x) (by simp)

/-- Definition 3.3.1 -/
theorem Function.eval {X Y: Set} (f: Function X Y) (x: X) (y: Y) : y = f x ↔ f.P x y := by
  have h := ((f.unique x).choose_iff y).symm
  convert h

@[simp]
theorem Function.eval_of {X Y: Set} (f: X → Y) (x:X) : (Function.mk_fn f) x = f x := by
  symm; rw [eval]


/-- Example 3.3.3.   -/
abbrev P_3_3_3a : Nat → Nat → Prop := fun x y ↦ (y:ℕ) = (x:ℕ)+1

theorem SetTheory.Set.P_3_3_3a_existsUnique (x: Nat) : ∃! y: Nat, P_3_3_3a x y := by
  apply ExistsUnique.intro ((x+1:ℕ):Nat)
  . rw [P_3_3_3a]
    simp
  intro y h
  rw [P_3_3_3a] at h
  rw [← h]
  simp

abbrev SetTheory.Set.f_3_3_3a : Function Nat Nat := Function.mk P_3_3_3a P_3_3_3a_existsUnique

theorem SetTheory.Set.f_3_3_3a_eval (x y: Nat) : y = f_3_3_3a x ↔ (y:ℕ) = (x+1:ℕ) :=
  Function.eval f_3_3_3a x y


theorem SetTheory.Set.f_3_3_3a_eval' (n: ℕ) : f_3_3_3a (n:Nat) = (n+1:ℕ) := by
  symm
  simp only [f_3_3_3a_eval]
  aesop

theorem SetTheory.Set.f_3_3_3a_eval'' : f_3_3_3a 4 = 5 :=  f_3_3_3a_eval' 4

theorem SetTheory.Set.f_3_3_3a_eval''' (n:ℕ) : f_3_3_3a (2*n+3: ℕ) = (2*n+4:ℕ) := by
  convert f_3_3_3a_eval' (2*n+3)

abbrev SetTheory.Set.P_3_3_3b : Nat → Nat → Prop := fun x y ↦ (y+1:ℕ) = (x:ℕ)

theorem SetTheory.Set.not_P_3_3_3b_existsUnique : ¬ ∀ x, ∃! y: Nat, P_3_3_3b x y := by
  by_contra h
  choose n hn _ using h (0:Nat)
  have : ((0:Nat):ℕ) = 0 := by simp [OfNat.ofNat]
  rw [P_3_3_3b, this] at hn
  simp at hn

abbrev SetTheory.Set.P_3_3_3c : (Nat \ {(0:Object)}: Set) → Nat → Prop :=
  fun x y ↦ ((y+1:ℕ):Object) = x

theorem SetTheory.Set.P_3_3_3c_existsUnique (x: (Nat \ {(0:Object)}: Set)) :
    ∃! y: Nat, P_3_3_3c x y := by
  -- Some technical unpacking here due to the subtle distinctions between the `Object` type,
  -- sets converted to subtypes of `Object`, and subsets of those sets.
  obtain ⟨ x, hx ⟩ := x; simp at hx; obtain ⟨ hx1, hx2 ⟩ := hx
  set n := ((⟨ x, hx1 ⟩:Nat):ℕ)
  have : x = (n:Nat) := by
    simp [n]
  simp [this, Object.ofnat_eq'] at hx2
  simp [P_3_3_3c, this] at ⊢
  replace hx2 : n = (n-1) + 1 := by omega
  apply ExistsUnique.intro ((n-1:ℕ):Nat)
  . simp [←hx2]
  intro y hy; simp [←hy]

abbrev SetTheory.Set.f_3_3_3c : Function (Nat \ {(0:Object)}: Set) Nat :=
  Function.mk P_3_3_3c P_3_3_3c_existsUnique

theorem SetTheory.Set.f_3_3_3c_eval (x: (Nat \ {(0:Object)}: Set)) (y: Nat) :
    y = f_3_3_3c x ↔ ((y+1:ℕ):Object) = x := Function.eval f_3_3_3c x y

/-- Create a version of a non-zero {lean}`n` inside {lean}`Nat \ {0}` for any natural number n. -/
abbrev SetTheory.Set.coe_nonzero (n:ℕ) (h: n ≠ 0): (Nat \ {(0:Object)}: Set) :=
  ⟨((n:ℕ):Object), by
    simp [Object.ofnat_eq']
    simp [h]
    rw [←Object.ofnat_eq]
    exact Subtype.property _
  ⟩

theorem SetTheory.Set.f_3_3_3c_eval' (n: ℕ) : f_3_3_3c (coe_nonzero (n+1) (by positivity)) = n := by
  symm; simp [f_3_3_3c_eval]

theorem SetTheory.Set.f_3_3_3c_eval'' : f_3_3_3c (coe_nonzero 4 (by positivity)) = 3 := by
  convert f_3_3_3c_eval' 3

theorem SetTheory.Set.f_3_3_3c_eval''' (n:ℕ) :
    f_3_3_3c (coe_nonzero (2*n+3) (by positivity)) = (2*n+2:ℕ) := by convert f_3_3_3c_eval' (2*n+2)

/--
  Example 3.3.4 is a little tricky to replicate with the current formalism as the real numbers
  have not been constructed yet.  Instead, I offer some Mathlib counterparts, using the
  Mathlib API for {name}`NNReal` and {lean}`ℝ`.
-/
example : ¬ ∃ f: ℝ → ℝ, ∀ x y, y = f x ↔ y^2 = x := by
  by_contra h
  obtain ⟨f, hf⟩ := h;
  set y := f (-1)
  have h1 := (hf _ y).mp (by rfl)
  have h2 := sq_nonneg y
  rw [h1] at h2
  exact absurd h2 (by linarith)

example : ¬ ∃ f: NNReal → ℝ, ∀ x y, y = f x ↔ y^2 = x := by
  by_contra h
  obtain ⟨f, hf⟩ := h;
  specialize hf 4;
  set y := f 4
  have hy := (hf y).mp (by rfl)
  have h1 : 2 = y := (hf 2).mpr (by norm_num)
  have h2 : -2 = y := (hf (-2)).mpr (by norm_num)
  rw [← h2] at h1
  exact absurd h1 (by norm_num)

example : ∃ f: NNReal → NNReal, ∀ x y, y = f x ↔ y^2 = x := by
  use NNReal.sqrt;
  intro x y
  constructor <;>
  intro h
  · rw [h, NNReal.sq_sqrt]
  · rw [←h, NNReal.sqrt_sq]

/-- Example 3.3.5. The unused variable {lit}`_x` is underscored to avoid triggering a linter. -/
abbrev SetTheory.Set.P_3_3_5 : Nat → Nat → Prop := fun _x y ↦ y = 7

theorem SetTheory.Set.P_3_3_5_existsUnique (x: Nat) : ∃! y: Nat, P_3_3_5 x y := by
  apply ExistsUnique.intro 7 <;>
  simp [P_3_3_5]

abbrev SetTheory.Set.f_3_3_5 : Function Nat Nat := Function.mk P_3_3_5 P_3_3_5_existsUnique

theorem SetTheory.Set.f_3_3_5_eval (x: Nat) : f_3_3_5 x = 7 := by
  symm;
  rw [Function.eval]

/-- Definition 3.3.8 (Equality of functions) -/
theorem Function.eq_iff {X Y: Set} (f g: Function X Y) : f = g ↔ ∀ x: X, f x = g x := by
  constructor <;>
  intro h
  . simp [h]
  ext x y;
  constructor <;>
  intros
  . rwa [←Function.eval, ←h x, Function.eval]
  rwa [←Function.eval, h x, Function.eval]

/--
  Example 3.3.10 (simplified).  The second part of the example is tricky to replicate in this
  formalism, so a Mathlib substitute is offered instead.
-/
abbrev SetTheory.Set.f_3_3_10a : Function Nat Nat := Function.mk_fn (fun x ↦ (x^2 + 2*x + 1:ℕ))

abbrev SetTheory.Set.f_3_3_10b : Function Nat Nat := Function.mk_fn (fun x ↦ ((x+1)^2:ℕ))

theorem SetTheory.Set.f_3_3_10_eq : f_3_3_10a = f_3_3_10b := by
  simp_rw [Function.eq_iff, Function.eval_of]
  intros;
  simp;
  ring

example : (fun x:NNReal ↦ (x:ℝ)) = (fun x:NNReal ↦ |(x:ℝ)|) := by
  simp_rw [NNReal.abs_eq]

example : (fun x:ℝ ↦ (x:ℝ)) ≠ (fun x:ℝ ↦ |(x:ℝ)|) := by
  by_contra h
  let a := (fun (x:ℝ) ↦ x) (-1)
  let b := (fun x:ℝ ↦ |(x:ℝ)|) (-1)
  have hab : a = b := by
    unfold a
    rw [h]
  norm_num [a, b] at hab

/-- Example 3.3.11 -/
abbrev SetTheory.Set.f_3_3_11 (X:Set) : Function (∅:Set) X :=
  Function.mk (fun _ _ ↦ True) (by intro ⟨ x, hx ⟩; simp at hx)

theorem SetTheory.Set.empty_function_unique {X: Set} (f g: Function (∅:Set) X) : f = g := by
  simp_rw [Function.eq_iff]
  intro x
  have ⟨x, hx⟩ := x
  simp at hx

/-- Definition 3.3.13 (Composition) -/
noncomputable abbrev Function.comp {X Y Z: Set} (g: Function Y Z) (f: Function X Y) :
    Function X Z :=
  Function.mk_fn (fun x ↦ g (f x))

-- `∘` is already taken in Mathlib for the composition of Mathlib functions,
-- so we use `○` here instead to avoid ambiguity.
infix:90 "○" => Function.comp

theorem Function.comp_eval {X Y Z: Set} (g: Function Y Z) (f: Function X Y) (x: X) :
    (g ○ f) x = g (f x) := Function.eval_of (fun x ↦ g (f x)) x

/--
  Compatibility with Mathlib's composition operation.
-/
theorem Function.comp_eq_comp {X Y Z: Set} (g: Function Y Z) (f: Function X Y) :
    (g ○ f).to_fn = g.to_fn ∘ f.to_fn := by
  ext x;
  simp only [Function.comp_eval]
  simp only [Function.comp_apply]

/-- Example 3.3.14 -/
abbrev SetTheory.Set.f_3_3_14 : Function Nat Nat := Function.mk_fn (fun x ↦ (2*x:ℕ))

abbrev SetTheory.Set.g_3_3_14 : Function Nat Nat := Function.mk_fn (fun x ↦ (x+3:ℕ))

theorem SetTheory.Set.g_circ_f_3_3_14 :
    g_3_3_14 ○ f_3_3_14 = Function.mk_fn (fun x ↦ ((2*(x:ℕ)+3:ℕ):Nat)) := by
  simp [Function.eq_iff]

theorem SetTheory.Set.f_circ_g_3_3_14 :
    f_3_3_14 ○ g_3_3_14 = Function.mk_fn (fun x ↦ ((2*(x:ℕ)+6:ℕ):Nat)) := by
  simp [Function.eq_iff]
  intros a ha
  ring

/-- Lemma 3.3.15 (Composition is associative) -/
theorem SetTheory.Set.comp_assoc {W X Y Z: Set} (h: Function Y Z) (g: Function X Y)
  (f: Function W X) :
    h ○ (g ○ f) = (h ○ g) ○ f := by
  simp [Function.eq_iff]

abbrev Function.one_to_one {X Y: Set} (f: Function X Y) : Prop := ∀ x x': X, x ≠ x' → f x ≠ f x'

theorem Function.one_to_one_iff {X Y: Set} (f: Function X Y) :
    f.one_to_one ↔ ∀ x x': X, f x = f x' → x = x' := by
  peel with x y;
  tauto

/--
  Compatibility with Mathlib's {name}`Function.Injective`.  You may wish to use the {tactic}`unfold` tactic to
  understand Mathlib concepts such as {name}`Function.Injective`.
-/
theorem Function.one_to_one_iff' {X Y: Set} (f: Function X Y) :
    f.one_to_one ↔ Function.Injective f.to_fn := by
  rw [one_to_one_iff]
  unfold Function.Injective
  tauto

/--
  Example 3.3.18.  One half of the example requires the integers, and so is expressed using
  Mathlib functions instead of Chapter 3 functions.
-/
theorem SetTheory.Set.f_3_3_18_one_to_one :
    (Function.mk_fn (fun (n:Nat) ↦ ((n^2:ℕ):Nat))).one_to_one := by
  rw [Function.one_to_one_iff]
  intro x y h
  rw [Function.eval, Function.eval_of] at h
  simp only [] at h
  simp at h
  exact h

example : ¬ Function.Injective (fun (n:ℤ) ↦ n^2) := by
  intro h
  have h1 : (fun n ↦ n ^ 2) 1 = (1:ℤ) := by norm_num
  have h2 : (fun n ↦ n ^ 2) (-1) = (1:ℤ) := by norm_num
  nth_rewrite 2 [←h1] at h2
  specialize h h2
  contradiction

example : Function.Injective (fun (n:ℕ) ↦ n^2) := by
  intro x y h;
  rwa [← pow_left_inj₀ (by norm_num) (by norm_num) (show 2 ≠ 0 by norm_num)]

/-- Remark 3.3.19 -/
theorem SetTheory.Set.two_to_one {X Y: Set} {f: Function X Y} (h: ¬ f.one_to_one) :
    ∃ x x': X, x ≠ x' ∧ f x = f x' := by
  rw [Function.one_to_one] at h;
  push_neg at h
  exact h

/-- Definition 3.3.20 (Onto functions) -/
abbrev Function.onto {X Y: Set} (f: Function X Y) : Prop := ∀ y: Y, ∃ x: X, f x = y

/-- Compatibility with Mathlib's {name}`Function.Surjective` -/
theorem Function.onto_iff {X Y: Set} (f: Function X Y) : f.onto ↔ Function.Surjective f.to_fn := by rfl

/-- Example 3.3.21 (using Mathlib) -/
example : ¬ Function.Surjective (fun (n:ℤ) ↦ n^2) := by
  unfold Function.Surjective;
  push_neg
  use (-1); intro a
  linarith [sq_nonneg a]

abbrev A_3_3_21 := { m:ℤ // ∃ n:ℤ, m = n^2 }

example : Function.Surjective (fun (n:ℤ) ↦ ⟨ n^2, by use n ⟩ : ℤ → A_3_3_21) := by
  rintro ⟨b, ⟨a, ha⟩⟩;
  use a
  simp only [ha]

/-- Definition 3.3.23 (Bijective functions) -/
abbrev Function.bijective {X Y: Set} (f: Function X Y) : Prop := f.one_to_one ∧ f.onto

/-- Compatibility with Mathlib's {name}`Function.Bijective` -/
theorem Function.bijective_iff {X Y: Set} (f: Function X Y) :
    f.bijective ↔ Function.Bijective f.to_fn := by
  rw [Function.bijective]
  rw [Function.Bijective]
  rw [one_to_one_iff']
  rw [onto_iff]

/-- Example 3.3.24 (using Mathlib) -/
abbrev f_3_3_24 : Fin 3 → ({3,4}:_root_.Set ℕ) := fun x ↦ match x with
| 0 => ⟨ 3, by norm_num ⟩
| 1 => ⟨ 3, by norm_num ⟩
| 2 => ⟨ 4, by norm_num ⟩

example : Function.Surjective f_3_3_24 := by decide
example : ¬ Function.Injective f_3_3_24 := by decide
example : ¬ Function.Bijective f_3_3_24 := by decide

abbrev g_3_3_24 : Fin 2 → ({2,3,4}:_root_.Set ℕ) := fun x ↦ match x with
| 0 => ⟨ 2, by norm_num ⟩
| 1 => ⟨ 3, by norm_num ⟩

example : ¬ Function.Surjective g_3_3_24 := by decide
example : Function.Injective g_3_3_24 := by decide
example : ¬ Function.Bijective g_3_3_24 := by decide

abbrev h_3_3_24 : Fin 3 → ({3,4,5}:_root_.Set ℕ) := fun x ↦ match x with
| 0 => ⟨ 3, by norm_num ⟩
| 1 => ⟨ 4, by norm_num ⟩
| 2 => ⟨ 5, by norm_num ⟩

example : Function.Bijective h_3_3_24 := by decide

/--
  Example 3.3.25 is formulated using Mathlib rather than the set theory framework here to avoid
  some tedious technical issues (cf. Exercise 3.3.2)
-/
example : Function.Bijective (fun n ↦ ⟨ n+1, by omega⟩ : ℕ → { n:ℕ // n ≠ 0 }) := by
  constructor
  · intro _ _
    simp only [Subtype.mk.injEq];
    omega
  intro ⟨x, hx⟩;
  use x-1
  simp only [Subtype.mk.injEq];
  omega

example : ¬ Function.Bijective (fun n ↦ n+1) := by
  suffices h : ¬ Function.Surjective (fun n ↦ n+1) by
    unfold Function.Bijective
    tauto
  unfold Function.Surjective;
  push_neg
  use 0;
  intros
  symm;
  apply Nat.zero_ne_add_one

/-- Remark 3.3.27 -/
theorem Function.bijective_incorrect_def :
    ∃ X Y: Set, ∃ f: Function X Y, (∀ x: X, ∃! y: Y, y = f x) ∧ ¬ f.bijective := by
  use Nat, Nat
  set f := mk_fn fun x ↦ (0: Nat); use f
  constructor
  · intros x
    apply existsUnique_of_exists_of_unique
    · use 0; rw [Function.eval]
    intros y1 y2 h1 h2; rw [Function.eval] at *; --aesop
    unfold f at *
    simp at *
    rw [h1, h2]
  rw [Function.bijective]
  suffices h : ¬ f.one_to_one by tauto
  rw [Function.one_to_one_iff]
  push_neg;
  use 0, 1;
  simp [f]

/--
  We cannot use the notation {syntax term}`f⁻¹` for the inverse because in Mathlib's {name}`Inv` class, the inverse
  of {name}`f` must be exactly of the same type of {name}`f`, and {lean}`Function Y X` is a different type from
  {lean}`Function X Y`.
-/
abbrev Function.inverse {X Y: Set} (f: Function X Y) (h: f.bijective) :
    Function Y X :=
  Function.mk (fun y x ↦ f x = y) (by
    intros
    apply existsUnique_of_exists_of_unique
    . aesop
    intro _ _ hx hx'; simp at hx hx'
    rw [←hx'] at hx
    apply f.one_to_one_iff.mp h.1
    simp [hx]
  )

theorem Function.inverse_eval {X Y: Set} {f: Function X Y} (h: f.bijective) (y: Y) (x: X) :
    x = (f.inverse h) y ↔ f x = y := Function.eval (Function.inverse f h) y x

/-- Compatibility with Mathlib's notion of inverse -/
theorem Function.inverse_eq {X Y: Set} [Nonempty X] {f: Function X Y} (h: f.bijective) :
    (f.inverse h).to_fn = Function.invFun f.to_fn := by
  ext y;
  congr;
  symm
  rw [inverse_eval]
  apply Function.rightInverse_invFun (f.bijective_iff.mp h).2

/--
  Exercise 3.3.1.  Although a proof operating directly on functions would be shorter,
  the spirit of the exercise is to show these using the {name}`Function.eq_iff` definition.
-/
theorem Function.refl {X Y:Set} (f: Function X Y) : f = f := by rfl

theorem Function.symm {X Y:Set} (f g: Function X Y) : f = g ↔ g = f := by tauto

theorem Function.trans {X Y:Set} {f g h: Function X Y} (hfg: f = g) (hgh: g = h) : f = h := by
  rw [← hfg] at hgh
  exact hgh

theorem Function.comp_congr {X Y Z:Set} {f f': Function X Y} (hff': f = f') {g g': Function Y Z}
  (hgg': g = g') : g ○ f = g' ○ f' := by
    have h1 : g ○ f = g ○ f := by rfl
    nth_rewrite 2 [hff'] at h1
    nth_rewrite 2 [hgg'] at h1
    exact h1

/-- Exercise 3.3.2 -/
theorem Function.comp_of_inj {X Y Z:Set} {f: Function X Y} {g : Function Y Z} (hf: f.one_to_one)
  (hg: g.one_to_one) : (g ○ f).one_to_one := by
    rw [one_to_one] at *
    intro x y h
    replace hf := hf x y h
    replace hg := hg _ _ (hf)
    simp; push_neg
    exact hg

theorem Function.comp_of_surj {X Y Z:Set} {f: Function X Y} {g : Function Y Z} (hf: f.onto)
  (hg: g.onto) : (g ○ f).onto := by
    rw [onto] at *
    intro z
    replace ⟨y, hg⟩ := hg z
    replace ⟨x, hf⟩ := hf y
    simp only [comp]
    use x
    simp
    rw [hf]
    rw [hg]

/--
  Exercise 3.3.3 - fill in the sorrys in the statements in a reasonable fashion.
-/
theorem empty_function_one_to_one_iff (X: Set) (f: Function ∅ X) : f.one_to_one ↔ X = X := by
  constructor
  . intro h
    rw [Function.one_to_one] at h
  intro h
  simp

theorem empty_function_onto_iff (X: Set) (f: Function ∅ X) : f.onto ↔ X = ∅ := by
  constructor
  . intro h
    rw [Function.onto] at h
    simp at h
    exact (SetTheory.Set.eq_empty_iff_forall_notMem).mpr h
  intro h
  simp
  exact (SetTheory.Set.eq_empty_iff_forall_notMem).mp h

theorem empty_function_bijective_iff (X: Set) (f: Function ∅ X) : f.bijective ↔ X = ∅ := by
  have h1 := (empty_function_one_to_one_iff X f).mpr (by rfl)
  rw [Function.bijective] at *
  constructor
  . intro h
    obtain ⟨h2, h3⟩ := h
    exact (empty_function_onto_iff X f).mp h3
  intro h
  exact And.intro h1 ((empty_function_onto_iff X f).mpr h)

/--
  Exercise 3.3.4.
-/
theorem Function.comp_cancel_left {X Y Z:Set} {f f': Function X Y} {g : Function Y Z}
  (heq : g ○ f = g ○ f') (hg: g.one_to_one) : f = f' := by
    rw [Function.eq_iff] at heq ⊢
    intro x
    rw [Function.one_to_one_iff] at hg
    have h1 := hg (f.to_fn x) (f'.to_fn x)
    have h2 := heq x
    simp [] at h2
    exact h1 h2

theorem Function.comp_cancel_right {X Y Z:Set} {f: Function X Y} {g g': Function Y Z}
  (heq : g ○ f = g' ○ f) (hf: f.onto) : g = g' := by
    rw [Function.eq_iff] at heq ⊢
    intro x
    simp only [Function.onto_iff] at hf
    unfold Function.Surjective at hf
    have ⟨a, ha⟩ := hf x
    have h1 := heq a
    rw [← ha]
    simp at h1
    exact h1


def Function.comp_cancel_left_without_hg : Decidable (∀ (X Y Z:Set) (f f': Function X Y) (g : Function Y Z) (heq : g ○ f = g ○ f'), f = f') := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`.
  apply isFalse
  push_neg
  use ({0, 1}:Set)
  use ({0, 1}:Set)
  use ({0}:Set)
  use (Function.mk_fn (fun x ↦ ⟨0, by simp⟩))
  use (Function.mk_fn (fun x ↦ ⟨1, by simp⟩))
  use (Function.mk_fn (fun x ↦ ⟨0, by simp⟩))
  simp
  intro h
  have h1 := congrFun (congrFun h (⟨0, by simp⟩)) (⟨0, by simp⟩)
  simp at h1


def Function.comp_cancel_right_without_hg : Decidable (∀ (X Y Z:Set) (f: Function X Y) (g g': Function Y Z) (heq : g ○ f = g' ○ f), g = g') := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`.
  apply isFalse
  push_neg
  use ({0}:Set)
  use ({0, 1}:Set)
  use ({0, 1}:Set)
  use (Function.mk_fn (fun x ↦ ⟨0, by simp⟩))
  use (Function.mk_fn (fun x ↦ ⟨0, by simp⟩))
  use (Function.mk_fn (fun x ↦ x))
  simp
  intro h
  have h1 := congrFun (congrFun h (⟨1, by simp⟩)) (⟨1, by simp⟩)
  simp at h1


/--
  Exercise 3.3.5.
-/
theorem Function.comp_injective {X Y Z:Set} {f: Function X Y} {g : Function Y Z} (hinj :
    (g ○ f).one_to_one) : f.one_to_one := by
      intro x y h
      rw [one_to_one] at hinj
      have h1 := hinj x y h
      by_contra h2
      simp at h1
      rw [h2] at h1
      contradiction

theorem Function.comp_surjective {X Y Z:Set} {f: Function X Y} {g : Function Y Z} (hsurj :
    (g ○ f).onto) : g.onto := by
      intro z
      simp only [Function.onto_iff] at hsurj
      unfold Function.Surjective at hsurj
      have ⟨a, ha⟩ := hsurj z
      use (f.to_fn a)
      aesop

def Function.comp_injective' : Decidable (∀ (X Y Z:Set) (f: Function X Y) (g : Function Y Z) (hinj :
    (g ○ f).one_to_one), g.one_to_one) := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`.
    apply isFalse
    push_neg
    use ({0}:Set)
    use ({0, 1}:Set)
    use ({0, 1}:Set)
    use (Function.mk_fn (fun x ↦ ⟨0, by simp⟩))
    use (Function.mk_fn (fun x ↦ ⟨0, by simp⟩))
    simp



def Function.comp_surjective' : Decidable (∀ (X Y Z:Set) (f: Function X Y) (g : Function Y Z) (hsurj :
    (g ○ f).onto), f.onto) := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`.
    apply isFalse
    push_neg
    use ({0, 1}:Set)
    use ({0, 1}:Set)
    use ({0}:Set)
    use (Function.mk_fn (fun x ↦ ⟨0, by simp⟩))
    use (Function.mk_fn (fun x ↦ ⟨0, by simp⟩))
    simp

/-- Exercise 3.3.6 -/
theorem Function.inverse_comp_self {X Y: Set} {f: Function X Y} (h: f.bijective) (x: X) :
    (f.inverse h) (f x) = x := by
    symm
    rw [inverse_eval]

theorem Function.self_comp_inverse {X Y: Set} {f: Function X Y} (h: f.bijective) (y: Y) :
    f ((f.inverse h) y) = y := by
      rw [bijective] at h
      have ⟨h1, h2⟩ := h
      rw [Function.onto] at h2
      have h3 := h2 y
      obtain ⟨a, ha⟩ := h3
      rw [← ha, Function.inverse_comp_self]

theorem Function.inverse_bijective {X Y: Set} {f: Function X Y} (h: f.bijective) :
    (f.inverse h).bijective := by
      rw [bijective] at *
      have ⟨h1, h2⟩ := h
      rw [Function.one_to_one] at h1
      rw [Function.onto] at h2
      constructor
      . intro x y h3
        have ⟨a, ha⟩ := h2 x
        have ⟨b, hb⟩ := h2 y
        rw [← ha, ← hb, Function.inverse_comp_self, Function.inverse_comp_self]
        rw [← ha, ←hb] at h3
        aesop
      intro x
      use (f.to_fn x)
      rw [Function.inverse_comp_self]


theorem Function.inverse_inverse {X Y: Set} {f: Function X Y} (h: f.bijective) :
    (f.inverse h).inverse (f.inverse_bijective h) = f := by
      rw [Function.eq_iff]
      intro y
      have h3 := (Function.inverse_comp_self (f.inverse_bijective h)) (f.to_fn y)
      have h4 := (Function.inverse_comp_self h) y
      rw [h4] at h3
      exact h3

/-- Exercise 3.3.7 -/
theorem Function.comp_bijective {X Y Z:Set} {f: Function X Y} {g : Function Y Z} (hf: f.bijective)
  (hg: g.bijective) : (g ○ f).bijective := by
      rw [bijective] at *
      have ⟨hf1, hf2⟩ := hf
      have ⟨hg1, hg2⟩ := hg
      constructor
      . exact Function.comp_of_inj hf1 hg1
      exact Function.comp_of_surj hf2 hg2

set_option pp.proofs true
theorem Function.inv_of_comp {X Y Z:Set} {f: Function X Y} {g : Function Y Z}
  (hf: f.bijective) (hg: g.bijective) :
    (g ○ f).inverse (Function.comp_bijective hf hg) = (f.inverse hf) ○ (g.inverse hg) := by
      have h0 := Function.comp_bijective hf hg
      rw [bijective] at h0
      have ⟨hneg1,hneg2⟩ := h0
      rw [Function.onto] at hneg2
      have h1 (x:X): ((f.inverse hf) ○ (g.inverse hg)) ((g ○ f) x) = x := by
        simp
        rw [Function.inverse_comp_self]
        rw [Function.inverse_comp_self]
      rw [Function.eq_iff]
      intro y
      have ⟨a, ha⟩ := hneg2 y
      have h2 := Function.inverse_comp_self (h0) a
      rw [← ha]
      simp only [h1, h2]

/-- Exercise 3.3.8 -/
abbrev Function.inclusion {X Y:Set} (h: X ⊆ Y) :
    Function X Y := Function.mk_fn (fun x ↦ ⟨ x.val, h x.val x.property ⟩ )

abbrev Function.id (X:Set) : Function X X := Function.mk_fn (fun x ↦ x)

theorem Function.inclusion_id (X:Set) :
    Function.inclusion (SetTheory.Set.subset_self X) = Function.id X := by rw [inclusion]


theorem Function.inclusion_comp (X Y Z:Set) (hXY: X ⊆ Y) (hYZ: Y ⊆ Z) :
    Function.inclusion hYZ ○ Function.inclusion hXY = Function.inclusion (SetTheory.Set.subset_trans hXY hYZ) := by
      rw [inclusion, inclusion, inclusion]
      aesop


theorem Function.comp_id {A B:Set} (f: Function A B) : f ○ Function.id A = f := by
    rw [Function.eq_iff]
    intro y
    rw [id]
    simp

theorem Function.id_comp {A B:Set} (f: Function A B) : Function.id B ○ f = f := by
    rw [Function.eq_iff]
    intro y
    rw [id]
    simp

theorem Function.comp_inv {A B:Set} (f: Function A B) (hf: f.bijective) :
    f ○ f.inverse hf = Function.id B := by
    rw [Function.eq_iff]
    intro y
    rw [id]
    simp
    exact Function.self_comp_inverse hf y


theorem Function.inv_comp {A B:Set} (f: Function A B) (hf: f.bijective) :
    f.inverse hf ○ f = Function.id A := by
    rw [Function.eq_iff]
    intro y
    rw [id]
    simp
    exact Function.inverse_comp_self hf y

theorem Function.comp_fun_rewrite {X Y Z:Set} (f: Function X Y) (g: Function Y Z) (x : X):
    (g ○ f) x = g.to_fn (f.to_fn x) := by simp_all

theorem union_left {X} (Y : Set) (y : X.toSubtype): y.val ∈ SetTheory.union_pair X Y := by
    have h4 := SetTheory.Set.subset_union_left X Y
    rw [SetTheory.Set.subset_def] at h4
    exact h4 y.val y.property
theorem union_right {Y : Set} (X:Set) (y : Y.toSubtype): y.val ∈ SetTheory.union_pair X Y := by
    have h4 := SetTheory.Set.subset_union_right X Y
    rw [SetTheory.Set.subset_def] at h4
    exact h4 y.val y.property
theorem inclusion_left{X Y : Set} (y : X.toSubtype) (z : y.val ∈ SetTheory.union_pair X Y): ((Function.inclusion (SetTheory.Set.subset_union_left X Y)).to_fn y) = ⟨y.val, z⟩ := by
    simp_all
theorem inclusion_right{X Y : Set} (y : Y.toSubtype) (z : y.val ∈ SetTheory.union_pair X Y): ((Function.inclusion (SetTheory.Set.subset_union_right X Y)).to_fn y) = ⟨y.val, z⟩ := by
    simp_all

open Classical in
theorem Function.glue {X Y Z:Set} (hXY: Disjoint X Y) (f: Function X Z) (g: Function Y Z) :
    ∃! h: Function (X ∪ Y) Z, (h ○ Function.inclusion (SetTheory.Set.subset_union_left X Y) = f)
    ∧ (h ○ Function.inclusion (SetTheory.Set.subset_union_right X Y) = g) := by
      let P : (SetTheory.union_pair X Y) → Z → Prop := fun x y => ((x.val ∈ X) ∧ (∃ z : X, z = x.val ∧ y = f z) ∨ (x.val ∈ Y) ∧ (∃ z : Y, z = x.val ∧ y = g z))
      have h0 (x : (SetTheory.union_pair X Y)) : (x.val ∈ X ∧ x.val ∉ Y) ∨ (x.val ∉ X ∧ x.val ∈ Y) := by
        rw [SetTheory.Set.disjoint_iff] at hXY
        have hneg1 : x.val ∈ (X ∪ Y) := x.property
        rw [SetTheory.Set.mem_union] at hneg1
        rcases hneg1 with hneg1 | hneg1
        . have hneg2 : x.val ∉ Y := by
            intro hneg3
            have hneg4 := And.intro hneg1 hneg3
            rw [← SetTheory.Set.mem_inter] at hneg4
            simp [hXY] at hneg4
          tauto
        have hneg2 : x.val ∉ X := by
          intro hneg3
          have hneg4 := And.intro hneg3 hneg1
          rw [← SetTheory.Set.mem_inter] at hneg4
          simp [hXY] at hneg4
        tauto

      have h1 : ∀ x: (SetTheory.union_pair X Y), ∃! y: Z, P x y := by
        simp
        intro x hx
        have h1 := h0 ⟨x, hx⟩
        rcases h1 with h1 | h1
        . obtain ⟨h2,h3⟩ := h1
          use (f ↑⟨x, h2⟩)
          simp only [P, h2, h3]
          simp
          exact h2
        obtain ⟨h2,h3⟩ := h1
        use (g ↑⟨x, h3⟩)
        simp only [P, h2, h3]
        simp
        exact h3
      let fx := Function.mk P h1
      have fn_left (y: SetTheory.union_pair X Y) (z: y.val ∈ X) : fx.to_fn y = f.to_fn ⟨y, z⟩ := by
        have hfx : P y (f.to_fn ⟨y, z⟩) := by
            unfold P
            simp_all
        have hfx1 := fx.unique y
        rw [Function.to_fn]
        apply (fx.unique y).unique
        · exact (fx.unique y).choose_spec
        · unfold fx
          exact hfx
      have fn_right (y: SetTheory.union_pair X Y) (z: y.val ∈ Y) : fx.to_fn y = g.to_fn ⟨y, z⟩ := by
        have hfx : P y (g.to_fn ⟨y, z⟩) := by
          unfold P
          simp_all
        have hfx1 := fx.unique y
        rw [Function.to_fn]
        apply (fx.unique y).unique
        · exact (fx.unique y).choose_spec
        · unfold fx
          exact hfx
      apply ExistsUnique.intro fx
      . constructor
        . rw [Function.eq_iff]
          intro y
          have h5 : y.val ∈ X := by
            exact y.property
          have hu : y.val ∈ SetTheory.union_pair X Y := by
            have h4 := SetTheory.Set.subset_union_left X Y
            rw [SetTheory.Set.subset_def] at h4
            exact h4 y.val h5
          have h3 := inclusion_left y (union_left Y y)
          rw [Function.comp_fun_rewrite]
          rw [h3]
          exact fn_left ⟨y, hu⟩ y.property
        rw [Function.eq_iff]
        intro y
        have h5 : y.val ∈ Y := by
          exact y.property
        have hu : y.val ∈ SetTheory.union_pair X Y := by
          have h4 := SetTheory.Set.subset_union_right X Y
          rw [SetTheory.Set.subset_def] at h4
          exact h4 y.val h5
        have h3 := inclusion_right y (union_right X y)
        rw [Function.comp_fun_rewrite]
        rw [h3]
        exact fn_right ⟨y, hu⟩ y.property
      intro f1 ⟨h2, h3⟩
      rw [Function.eq_iff] at h2 h3 ⊢
      intro ⟨x, hx⟩
      have h4 := h0 ⟨x, hx⟩
      rcases h4 with h4 | h4
      . obtain ⟨h5, h6⟩ := h4
        replace h2 := h2 ⟨x, h5⟩
        have h7 := inclusion_left ⟨x, h5⟩ hx
        rw [Function.comp_fun_rewrite] at h2
        rw [h7] at h2
        simp at h2
        rw [h2]
        have h8 := fn_left ⟨x, hx⟩ h5
        simp at h8
        rw [h8]
      obtain ⟨h5, h6⟩ := h4
      replace h2 := h3 ⟨x, h6⟩
      have h7 := inclusion_right ⟨x, h6⟩ hx
      rw [Function.comp_fun_rewrite] at h2
      rw [h7] at h2
      simp at h2
      rw [h2]
      have h8 := fn_right ⟨x, hx⟩ h6
      simp at h8
      rw [h8]

theorem SetTheory.Set.disjoint_intersection_exclusion (X Y:Set) : (Disjoint Y (X \ Y)) ∧ (Y ∪ (X \ Y) = X ∪ Y) ∧ ((X \ Y) ⊆ X)  := by
  constructor
  . rw [disjoint_iff]
    exact inter_compl
  constructor
  . ext x
    simp
    tauto
  rw [subset_def]
  simp
  tauto

theorem Function.comp_fun_rewrite' {X Y Z:Set} (f: Function X Y) (g: Function Y Z) (x : X):
    (g ○ f) x = g (f x) := by simp_all

open Classical in
theorem Function.glue' {X Y Z:Set} (f: Function X Z) (g: Function Y Z)
    (hfg : ∀ x : ((X ∩ Y): Set), f ⟨x.val, by aesop⟩ = g ⟨x.val, by aesop⟩)  :
    ∃! h: Function (X ∪ Y) Z, (h ○ Function.inclusion (SetTheory.Set.subset_union_left X Y) = f)
    ∧ (h ○ Function.inclusion (SetTheory.Set.subset_union_right X Y) = g) := by
      have h1 := SetTheory.Set.disjoint_intersection_exclusion X Y
      have ⟨ h2, h3, h4 ⟩ := h1
      let inj := Function.inclusion (h4)
      let f' := (f ○ inj)
      have h5 := Function.glue h2 g f'
      obtain ⟨f1, ⟨hf1, hf2⟩, hf1_unique⟩ := h5
      have h6 : (X ∪ Y) ⊆ ( Y ∪ X \ Y ) := by
        simp_all

      have h10 {x}(h1: x ∈ X ∪ Y)(h2 : x ∉ Y): x ∈ X \ Y := by
        simp at *
        tauto
      let hw : (X ∪ Y).toSubtype → (Y ∪ X \ Y).toSubtype := fun w =>
        if hx : w.val ∈ Y then
          (inclusion (SetTheory.Set.subset_union_left Y (X \ Y))) ⟨w, hx⟩
        else  (inclusion (SetTheory.Set.subset_union_right Y (X \ Y))) ⟨w.val, h10 (w.property) hx⟩

      let f3 := Function.mk_fn (fun w => hw w)
      unfold Function.id at f3
      let f2 := Function.mk_fn (fun w => (f1○f3) w)
      apply ExistsUnique.intro f2
      symm
      have simplify_x {W:Set} {y : W.toSubtype}: (⟨↑y, Eq.mpr_prop (eq_true y.property) True.intro⟩ : W.toSubtype) = y := by
        apply Subtype.ext
        rfl
      constructor
      . rw [Function.eq_iff]
        intro y
        rw [Function.comp_fun_rewrite']
        have h2 := (union_right X y)
        have h1 := inclusion_right y h2
        rw [h1]
        unfold f2
        simp
        unfold f3
        simp
        unfold hw
        simp only [y.property]
        rw [dif_pos True.intro]
        rw [simplify_x]
        replace hf1 := congr($hf1 y)
        rw [Function.comp_fun_rewrite'] at hf1
        exact hf1
      . rw [Function.eq_iff]
        intro x
        rw [Function.comp_fun_rewrite']
        have h2 := (union_left Y x)
        have h1 := inclusion_left x h2
        rw [h1]
        unfold f2
        simp
        unfold f3
        simp
        unfold hw
        by_cases hv: x.val ∈ Y
        .  simp only [hv]
           rw [dif_pos True.intro]
           have h11 : (⟨↑x, Eq.mpr_prop (eq_true hv) True.intro⟩ : Y.toSubtype) = ⟨x.val, hv⟩ := by
              apply Subtype.ext
              rfl
           rw [h11]
           replace hf1 := congr($hf1 ⟨↑x, hv⟩)
           rw [Function.comp_fun_rewrite'] at hf1
           rw [hf1]
           have hw := (SetTheory.Set.mem_inter x.val X Y).mpr (And.intro x.property hv)
           have hfg1 := hfg ⟨↑x, hw⟩
           simp at hfg1
           exact hfg1.symm
        have hw := (SetTheory.Set.mem_sdiff x X Y).mpr (And.intro x.property hv)
        simp only [hv]
        rw [dif_neg (by simp)]
        have h13 : (⟨↑x, h10 (⟨↑x, h2⟩ : (X ∪ Y).toSubtype).property (Eq.mpr_not (eq_false hv) (of_eq_true not_false_eq_true))⟩ : (X \ Y).toSubtype) = ⟨↑x, hw⟩ := by
            apply Subtype.ext
            rfl
        rw [h13]
        replace hf2 := congr($hf2  ⟨↑x, hw⟩)
        rw [Function.comp_fun_rewrite'] at hf2
        rw [hf2]
        unfold f'
        unfold inj
        rw [Function.comp_fun_rewrite']
        simp
      intro g4 ⟨h21, h22⟩
      rw [Function.eq_iff]
      intro x
      unfold f2
      conv =>
        rhs
        simp
        unfold f3
        simp
        unfold hw
      by_cases h31 : x.val ∈ Y
      . simp only [h31]
        rw [dif_pos True.intro]
        have hhh :  (⟨↑x, Eq.mpr_prop (eq_true h31) True.intro⟩ : Y.toSubtype) = ⟨x.val, h31⟩ := by
            apply Subtype.ext
            rfl
        rw [hhh]
        replace hf1 := congr($hf1 ⟨x.val, h31⟩)
        rw [Function.comp_fun_rewrite'] at hf1
        rw [hf1]
        replace h22 := congr($h22 ⟨x.val, h31⟩)
        rw [Function.comp_fun_rewrite'] at h22
        rw [← h22]
        simp
      simp only [h31]
      rw [dif_neg (by simp)]
      have h32 := h10 x.property h31
      have hhh : (⟨↑x, h10 x.property (Eq.mpr_not (eq_false h31) (of_eq_true not_false_eq_true))⟩ : (X \ Y).toSubtype) = ⟨↑x, h32⟩ := by
          apply Subtype.ext
          rfl
      rw [hhh]
      replace hf2 := congr($hf2 ⟨x.val, h32⟩)
      rw [Function.comp_fun_rewrite'] at hf2
      rw [hf2]
      unfold f'
      rw [Function.comp_fun_rewrite']
      unfold inj
      simp
      have h33 : x.val ∈ X := by
        rw [SetTheory.Set.mem_sdiff] at h32
        exact h32.1
      have hhhh : (⟨↑x, inclusion._proof_1 h4 ⟨↑x, h32⟩⟩ : X.toSubtype) = ⟨x, h33⟩ := by
        apply Subtype.ext
        rfl
      rw [hhhh]
      replace h21 := congr($h21 ⟨x, h33⟩)
      rw [← h21]
      rw [Function.comp_fun_rewrite']
      simp



end Chapter3
