import Mathlib.Tactic
import Analysis.Section_3_1
set_option doc.verso.suggestions false
-- set_option pp.proofs true
/-!
# Analysis I, Section 3.4: Images and inverse images

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Images and inverse images of (Mathlib) functions, within the framework of Section 3.1 set
  theory. (The Section 3.3 functions are now deprecated and will not be used further.)
- Connection with Mathlib's image {syntax term}`f '' S` and preimage {syntax term}`f ⁻¹' S` notions.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Chapter3

export SetTheory (Set Object nat)

variable [SetTheory]

/-- Definition 3.4.1.  Interestingly, the definition does not require {lean}`S` to be a subset of {lean}`X`. -/
abbrev SetTheory.Set.image {X Y:Set} (f:X → Y) (S: Set) : Set :=
  X.replace (P := fun x y ↦ f x = y ∧ x.val ∈ S) (by simp_all)

/-- Definition 3.4.1 -/
theorem SetTheory.Set.mem_image {X Y:Set} (f:X → Y) (S: Set) (y:Object) :
    y ∈ image f S ↔ ∃ x:X, x.val ∈ S ∧ f x = y := by
  grind [replacement_axiom]

/-- Alternate definition of image using axiom of specification -/
theorem SetTheory.Set.image_eq_specify {X Y:Set} (f:X → Y) (S: Set) :
    image f S = Y.specify (fun y ↦ ∃ x:X, x.val ∈ S ∧ f x = y) := by
      ext x
      constructor
      . intro h
        rw [mem_image] at *
        grind [specification_axiom'']
      intro h
      rw [mem_image]
      aesop

/--
  Connection with Mathlib's notion of image.  Note the need to utilize the {name}`Subtype.val` coercion
  to make everything type consistent.
-/
theorem SetTheory.Set.image_eq_image {X Y:Set} (f:X → Y) (S: Set):
    (image f S: _root_.Set Object) = Subtype.val '' (f '' {x | x.val ∈ S}) := by
  ext;
  simp;
  grind

theorem SetTheory.Set.image_in_codomain {X Y:Set} (f:X → Y) (S: Set) :
    image f S ⊆ Y := by
      intro x h;
      rw [mem_image] at h;
      obtain ⟨⟨y, yh⟩, ⟨h1, h2⟩⟩ := h
      let rf := f ↑⟨y, yh⟩
      have h1 : ↑(f ↑⟨y, yh⟩) ∈ Y := rf.property
      rw [h2] at h1
      exact h1

/-- Example 3.4.2 -/
abbrev f_3_4_2 : nat → nat := fun n ↦ (2*n:ℕ)

theorem SetTheory.Set.image_f_3_4_2 : image f_3_4_2 {1,2,3} = {2,4,6} := by
  ext;
  simp only [mem_image]
  simp only [mem_triple]
  simp only [f_3_4_2]
  constructor
  · rintro ⟨_, (_ | _ | _), rfl⟩ <;>
    simp_all
  rintro (_ | _ | _);
  map_tacs [use 1; use 2; use 3]
  all_goals
  simp_all

/-- Example 3.4.3 is written using Mathlib's notion of image. -/
example : (fun n:ℤ ↦ n^2) '' {-1,0,1,2} = {0,1,4} := by aesop

theorem SetTheory.Set.mem_image_of_eval {X Y:Set} (f:X → Y) (S: Set) (x:X) :
    x.val ∈ S → (f x).val ∈ image f S := by
      intro h
      simp only [mem_image]
      use x

theorem SetTheory.Set.mem_image_of_eval_counter :
    ∃ (X Y:Set) (f:X → Y) (S: Set) (x:X), ¬((f x).val ∈ image f S → x.val ∈ S) := by
      let A := ({0, 1}:Set)
      let B := ({0}:Set)
      use A
      use B
      use (fun n:A ↦ ⟨0, by aesop⟩)
      use B
      use ⟨1, by aesop⟩
      simp_all
      use 0
      unfold A B
      simp_all


/--
  Definition 3.4.4 (inverse images).
  Again, it is not required that {lean}`U` be a subset of {lean}`Y`.
-/
abbrev SetTheory.Set.preimage {X Y:Set} (f:X → Y) (U: Set) : Set := X.specify (P := fun x ↦ (f x).val ∈ U)

@[simp]
theorem SetTheory.Set.mem_preimage {X Y:Set} (f:X → Y) (U: Set) (x:X) :
    x.val ∈ preimage f U ↔ (f x).val ∈ U := by
      rw [specification_axiom']

/--
  A version of {name}`mem_preimage` that does not require {lean}`x` to be of type {lean}`X`.
-/
theorem SetTheory.Set.mem_preimage' {X Y:Set} (f:X → Y) (U: Set) (x:Object) :
    x ∈ preimage f U ↔ ∃ x': X, x'.val = x ∧ (f x').val ∈ U := by
  constructor
  . intro h;
    by_cases hx: x ∈ X
    . use ⟨ x, hx ⟩;
      have := mem_preimage f U ⟨ _, hx ⟩;
      simp_all
    . simp only [preimage] at h
      have h1 := specification_axiom h
      contradiction
  . rintro ⟨ x', rfl, hfx' ⟩;
    rwa [mem_preimage]

/-- Connection with Mathlib's notion of preimage. -/
theorem SetTheory.Set.preimage_eq {X Y:Set} (f:X → Y) (U: Set) :
    ((preimage f U): _root_.Set Object) = Subtype.val '' (f⁻¹' {y | y.val ∈ U}) := by
  ext;
  simp

theorem SetTheory.Set.preimage_in_domain {X Y:Set} (f:X → Y) (U: Set) :
    (preimage f U) ⊆ X := by
      intro _ _;
      aesop

/-- Example 3.4.6 -/
theorem SetTheory.Set.preimage_f_3_4_2 : preimage f_3_4_2 {2,4,6} = {1,2,3} := by
  ext;
  simp only [mem_preimage'];
  simp only [mem_triple];
  simp only [f_3_4_2]
  constructor
  · rintro ⟨x, rfl, (_ | _ | _)⟩ <;>
    simp_all <;>
    omega
  rintro (rfl | rfl | rfl);
  map_tacs [use 1; use 2; use 3]
  all_goals simp

theorem SetTheory.Set.image_preimage_f_3_4_2 :
    image f_3_4_2 (preimage f_3_4_2 {1,2,3}) ≠ {1,2,3} := by
    intro h
    have h2 : 1 ∈ ({1,2,3}:Set) := by simp
    rw [← h] at h2
    simp only [mem_image] at h2
    have ⟨x, ⟨h4, h5⟩⟩ := h2
    unfold f_3_4_2 at *
    have h8 :  2 * nat_equiv.symm x ≠ 1 := by
      omega
    exfalso
    apply h8
    apply nat_equiv.injective
    apply Subtype.ext
    exact h5






/-- Example 3.4.7 (using the Mathlib notion of preimage) -/
example : (fun n:ℤ ↦ n^2) ⁻¹' {0,1,4} = {-2,-1,0,1,2} := by
  ext;
  refine ⟨ ?_, by aesop ⟩;
  rintro (h | h | h)
  on_goal 1 =>
    have : 0 ^ 2 = (0:ℤ) := (by norm_num);
    nth_rw 2 [←h] at this;
    conv at this =>
      rhs
      simp
    rw [sq_eq_sq_iff_eq_or_eq_neg] at this
    simp at this
  on_goal 3 => have : 2 ^ 2 = (4:ℤ) := (by norm_num); rw [←h, sq_eq_sq_iff_eq_or_eq_neg] at this
  all_goals aesop

example : (fun n:ℤ ↦ n^2) ⁻¹' ((fun n:ℤ ↦ n^2) '' {-1,0,1,2}) ≠ {-1,0,1,2} := by
  have h1 : (2:ℤ) ∈ ({-1,0,1,2}: Finset ℤ) := by simp
  have h3 : (-2:ℤ) ∉ ({-1,0,1,2}: Finset ℤ) := by simp
  have h2 : -2 ∈ (fun n:ℤ ↦ n^2) ⁻¹' ((fun n:ℤ ↦ n^2) '' {-1,0,1,2}) := by simp
  intro h
  rw [h] at h2
  contradiction


instance SetTheory.Set.inst_pow : Pow Set Set where
  pow := pow

@[coe]
def SetTheory.Set.coe_of_fun {X Y:Set} (f: X → Y) : Object := function_to_object X Y f

/-- This coercion has to be a {name}`CoeOut` rather than a
{name}`Coe` because the input type {lean}`X → Y` contains
parameters not present in the output type {name}`Object` -/
instance SetTheory.Set.inst_coe_of_fun {X Y:Set} : CoeOut (X → Y) Object where
  coe := coe_of_fun

@[simp]
theorem SetTheory.Set.coe_of_fun_inj {X Y:Set} (f g:X → Y) : (f:Object) = (g:Object) ↔ f = g := by
  simp [coe_of_fun]

/-- Axiom 3.11 (Power set axiom) --/
@[simp]
theorem SetTheory.Set.powerset_axiom {X Y:Set} (F:Object) :
    F ∈ (X ^ Y) ↔ ∃ f: Y → X, f = F := SetTheory.powerset_axiom X Y F

/-- Example 3.4.9 -/
abbrev f_3_4_9_a : ({4,7}:Set) → ({0,1}:Set) := fun x ↦ ⟨ 0, by simp ⟩

open Classical in
noncomputable abbrev f_3_4_9_b : ({4,7}:Set) → ({0,1}:Set) :=
  fun x ↦ if x.val = 4 then ⟨ 0, by simp ⟩ else ⟨ 1, by simp ⟩

open Classical in
noncomputable abbrev f_3_4_9_c : ({4,7}:Set) → ({0,1}:Set) :=
  fun x ↦ if x.val = 4 then ⟨ 1, by simp ⟩ else ⟨ 0, by simp ⟩

abbrev f_3_4_9_d : ({4,7}:Set) → ({0,1}:Set) := fun x ↦ ⟨ 1, by simp ⟩

theorem SetTheory.Set.example_3_4_9 (F:Object) :
    F ∈ ({0,1}:Set) ^ ({4,7}:Set) ↔ F = f_3_4_9_a
    ∨ F = f_3_4_9_b ∨ F = f_3_4_9_c ∨ F = f_3_4_9_d := by
  rw [powerset_axiom]
  refine ⟨?_, by aesop ⟩
  rintro ⟨f, rfl⟩
  have h1 := (f ⟨4, by simp⟩).property
  have h2 := (f ⟨7, by simp⟩).property
  simp [coe_of_fun_inj] at *
  obtain _ | _ := h1 <;>
  obtain _ | _ := h2
  map_tacs [left; (right;left); (right;right;left); (right;right;right)]
  all_goals ext ⟨_, hx⟩;
            simp at hx;
            grind

theorem SetTheory.Set.powerset_axiom_2 {X Y:Set} (F:(X ^ Y).toSubtype) :
    ∃ f: Y → X, f = F.val := (SetTheory.Set.powerset_axiom F.val).mp F.property

--  how can we denote this function f here?

noncomputable def SetTheory.Set.underlying_powerset {X Y:Set} (F:(X ^ Y).toSubtype) : Y → X :=
    (powerset_axiom_2 F).choose

/-- Exercise 3.4.6 (i). One needs to provide a suitable definition of the power set here. -/
def SetTheory.Set.powerset (X:Set) : Set :=
  (({0,1} ^ X): Set).replace     (P := fun F y ↦ y = X.specify
      (fun z ↦ ∃ f: X → ({0,1}:Set), (f:Object) = F.val ∧ f z = ⟨1, by simp⟩))
    (by intro x y y' ⟨h1, h2⟩; rw [h1, h2])

open Classical in
/-- Exercise 3.4.6 (i) -/
@[simp]
theorem SetTheory.Set.mem_powerset {X:Set} (x:Object) :
    x ∈ powerset X ↔ ∃ Y:Set, x = Y ∧ Y ⊆ X := by
      rw [powerset]
      simp only [replacement_axiom]
      constructor
      . intro h
        simp at h
        obtain ⟨f, hf⟩ := h
        use (X.specify fun z ↦ f z = ⟨1, by simp⟩)
        simp_all
        intro x hx
        exact specification_axiom hx
      simp_all
      intro y h1 h2
      let f : X.toSubtype → ({0, 1}:Set).toSubtype := fun (w:X.toSubtype) =>
        if hx : w.val ∈ y then ⟨1, by simp⟩
        else ⟨0, by simp⟩
      use f
      ext w
      simp
      unfold f
      simp
      intro h
      rw [subset_def] at h2
      exact h2 w h


/-- Lemma 3.4.10 -/
theorem SetTheory.Set.exists_powerset (X:Set) :
   ∃ (Z: Set), ∀ x, x ∈ Z ↔ ∃ Y:Set, x = Y ∧ Y ⊆ X := by
  use powerset X;
  apply mem_powerset

/- As noted in errata, Exercise 3.4.6 (ii) is replaced by Exercise 3.5.11. -/

/-- Remark 3.4.11 -/
theorem SetTheory.Set.powerset_of_triple (a b c x:Object) :
    x ∈ powerset {a,b,c}
    ↔ x = (∅:Set)
    ∨ x = ({a}:Set)
    ∨ x = ({b}:Set)
    ∨ x = ({c}:Set)
    ∨ x = ({a,b}:Set)
    ∨ x = ({a,c}:Set)
    ∨ x = ({b,c}:Set)
    ∨ x = ({a,b,c}:Set) := by
  simp only [mem_powerset]
  simp only [subset_def]
  simp only [mem_triple]
  refine ⟨ ?_, by aesop ⟩
  rintro ⟨Y, rfl, hY⟩;
  by_cases a ∈ Y <;>
  by_cases b ∈ Y <;>
  by_cases c ∈ Y
  on_goal 8 => left
  on_goal 4 => right; left
  on_goal 6 => right; right; left
  on_goal 7 => right; right; right; left
  on_goal 2 => right; right; right; right; left
  on_goal 3 => right; right; right; right; right; left
  on_goal 5 => right; right; right; right; right; right; left
  on_goal 1 => right; right; right; right; right; right; right
  all_goals
  congr;
  ext;
  simp;
  grind

/-- Axiom 3.12 (Union) -/
theorem SetTheory.Set.union_axiom (A: Set) (x:Object) :
    x ∈ union A ↔ ∃ (S:Set), x ∈ S ∧ (S:Object) ∈ A := SetTheory.union_axiom A x

/-- Example 3.4.12 -/
theorem SetTheory.Set.example_3_4_12 :
    union { (({2,3}:Set):Object), (({3,4}:Set):Object), (({4,5}:Set):Object) } = {2,3,4,5} := by
  ext x
  simp_all
  simp only [union_axiom]
  simp_all
  refine ⟨ ?_, by aesop ⟩
  rintro ⟨w, ⟨h1,h2⟩⟩
  rcases h2 with h2 | h2 | h2
  all_goals
  rw [h2] at h1
  rw [mem_pair] at *
  grind


/-- Connection with Mathlib union -/
theorem SetTheory.Set.union_eq (A: Set) :
    (union A : _root_.Set Object) =
    ⋃₀ { S : _root_.Set Object | ∃ S':Set, S = S' ∧ (S':Object) ∈ A } := by
  ext;
  simp only [union_axiom];
  simp only [Set.mem_sUnion];
  aesop

/-- Indexed union -/
abbrev SetTheory.Set.iUnion (I: Set) (A: I → Set) : Set :=
  union (I.replace (P := fun α S ↦ S = A α) (by intro _ _ _ ⟨h1, h2⟩; exact h1.trans h2.symm))

theorem SetTheory.Set.mem_iUnion {I:Set} (A: I → Set) (x:Object) :
    x ∈ iUnion I A ↔ ∃ α:I, x ∈ A α := by
  rw [union_axiom];
  constructor
  . intro h
    simp [replacement_axiom] at h
    obtain ⟨a, h1, h2⟩ := h
    use ⟨a, h1⟩
  intro ⟨α, ha⟩
  use (A α)
  constructor
  . exact ha
  rw [replacement_axiom]
  use α


open Classical in
noncomputable abbrev SetTheory.Set.index_example : ({1,2,3}:Set) → Set :=
  fun i ↦ if i.val = 1 then {2,3} else if i.val = 2 then {3,4} else {4,5}

theorem SetTheory.Set.iUnion_example : iUnion {1,2,3} index_example = {2,3,4,5} := by
  apply ext;
  intros;
  simp [mem_iUnion]
  simp [index_example]
  refine ⟨ by aesop, ?_ ⟩;
  rintro (_ | _ | _);
  map_tacs [use 1; use 2; use 3]
  all_goals aesop

/-- Connection with Mathlib indexed union -/
theorem SetTheory.Set.iUnion_eq (I: Set) (A: I → Set) :
    (iUnion I A : _root_.Set Object) = ⋃ α, (A α: _root_.Set Object) := by
  ext;
  simp [mem_iUnion]

theorem SetTheory.Set.iUnion_of_empty (A: (∅:Set) → Set) : iUnion (∅:Set) A = ∅ := by
  ext;
  simp [mem_iUnion]

/-- Indexed intersection -/
noncomputable abbrev SetTheory.Set.nonempty_choose {I:Set} (hI: I ≠ ∅) : I :=
  ⟨(nonempty_def hI).choose, (nonempty_def hI).choose_spec⟩

abbrev SetTheory.Set.iInter' (I:Set) (β:I) (A: I → Set) : Set :=
  (A β).specify (P := fun x ↦ ∀ α:I, x.val ∈ A α)

noncomputable abbrev SetTheory.Set.iInter (I: Set) (hI: I ≠ ∅) (A: I → Set) : Set :=
  iInter' I (nonempty_choose hI) A

theorem SetTheory.Set.mem_iInter {I:Set} (hI: I ≠ ∅) (A: I → Set) (x:Object) :
    x ∈ iInter I hI A ↔ ∀ α:I, x ∈ A α := by
  rw [iInter]
  rw [iInter']
  simp
  intro h
  simp_all


/-- Exercise 3.4.1 -/
theorem SetTheory.Set.preimage_eq_image_of_inv {X Y V:Set} (f:X → Y) (f_inv: Y → X)
  (hf: Function.LeftInverse f_inv f ∧ Function.RightInverse f_inv f) (hV: V ⊆ Y) :
    image f_inv V = preimage f V := by
      ext x;
      obtain ⟨hf1, hf2⟩ := hf
      rw [Function.LeftInverse] at hf1
      rw [Function.RightInverse, Function.LeftInverse] at hf2
      rw [mem_preimage', mem_image]
      simp_all
      refine ⟨ ?_, by aesop⟩;
      intro ⟨y, ⟨z, ⟨w, hw⟩⟩⟩
      have hv : (⟨y, (Iff.of_eq (Eq.refl (y ∈ Y))).mpr w⟩ : Y.toSubtype) = ⟨y, w⟩ := by
        apply Subtype.ext
        simp_all
      rw [hv] at hw
      let rf := ↑(f_inv ⟨y, w⟩)
      have h1 : ↑(f_inv ⟨y, w⟩) ∈ X := rf.property
      rw [hw] at h1
      use h1
      have hf3 := hf2 y w
      simp at hf3
      have h2 : f_inv ⟨y, w⟩ = ⟨x, by aesop⟩ := by
        aesop
      rw [h2] at hf3
      rw [hf3]
      have h3 :  (⟨y, w⟩ : Y.toSubtype) = y := by
        simp
      rw [← h3] at z
      exact z




/- Exercise 3.4.2.  State and prove an assertion connecting `preimage f (image f S)` and `S`. -/
theorem SetTheory.Set.preimage_of_image {X Y:Set} (f:X → Y) (S: Set) (hS: S ⊆ X) : S ⊆ preimage f (image f S)  := by
  intro x
  simp_all
  intro h
  have h1 := (hS x h)
  use h1
  use x
  constructor
  . use h1
  exact h

/- Exercise 3.4.2.  State and prove an assertion connecting `image f (preimage f U)` and `U`.
Interestingly, it is not needed for U to be a subset of Y. -/
theorem SetTheory.Set.image_of_preimage {X Y:Set} (f:X → Y) (U: Set) : image f (preimage f U) ⊆ U := by
  intro x
  simp_all

/- Exercise 3.4.2.  State and prove an assertion connecting `preimage f (image f (preimage f U))` and `preimage f U`.
Interestingly, it is not needed for U to be a subset of Y.-/
theorem SetTheory.Set.preimage_of_image_of_preimage {X Y:Set} (f:X → Y) (U: Set) : preimage f (image f (preimage f U)) = preimage f U  := by
  ext x;
  simp_all
  constructor
  . intro ⟨h1, ⟨a, ⟨h2, ⟨h3, h4⟩⟩⟩⟩
    use h1
    grind
  intro ⟨h1, h2⟩
  use h1
  use x
  use h1

/--
  Exercise 3.4.3.
-/
theorem SetTheory.Set.image_of_inter {X Y:Set} (f:X → Y) (A B: Set) :
    image f (A ∩ B) ⊆ (image f A) ∩ (image f B) := by
      intro x hx
      simp only [mem_image, mem_inter] at *
      obtain ⟨y, ⟨⟨h1, h2⟩, h3⟩⟩ := hx
      constructor
      all_goals
      use y

theorem SetTheory.Set.image_of_diff {X Y:Set} (f:X → Y) (A B: Set) :
    (image f A) \ (image f B) ⊆ image f (A \ B) := by
      intro x hx
      simp only [mem_image, mem_sdiff] at *
      obtain ⟨⟨y, ⟨hy1, hy2⟩⟩, h1⟩ := hx
      push_neg at h1
      replace h1 := h1 y
      rw [imp_iff_not_or] at h1
      use y
      rcases h1 with h1 | h1
      . exact And.intro (And.intro hy1 h1) hy2
      contradiction

theorem SetTheory.Set.image_of_union {X Y:Set} (f:X → Y) (A B: Set) :
    image f (A ∪ B) = (image f A) ∪ (image f B) := by
      ext x
      simp only [mem_image, mem_union] at *
      refine ⟨ ?_, by aesop⟩;
      intro ⟨y, ⟨h1, h2⟩⟩
      rcases h1 with h1 | h1
      . apply Or.inl
        use y
      apply Or.inr
      use y


def SetTheory.Set.image_of_inter' : Decidable (∀ X Y:Set, ∀ f:X → Y, ∀ A B: Set, image f (A ∩ B) = (image f A) ∩ (image f B)) := by
  -- The first line of this construction should be either `apply isTrue` or `apply isFalse`
  apply isFalse
  push_neg
  use {0, 1}
  use {0}
  let f : toSubtype {0, 1} → toSubtype {0}  := fun i ↦ ⟨0, by simp⟩
  use f
  use {0}
  use {1}
  have h1 : image f ({0} ∩ {1}) = ∅ := by
    ext x
    rw [mem_image]
    simp
  have h2 : image f {0} ∩ image f {1} = {0} := by
    ext x
    rw [mem_inter, mem_image]
    simp
    unfold f
    simp_all
    tauto
  rw [h1, h2]
  simp
  intro h
  have h3 : 0 ∈ ({0}:Set) := by
    simp
  rw [← h] at h3
  have h4 := not_mem_empty 0
  contradiction

def SetTheory.Set.image_of_diff' : Decidable (∀ X Y:Set, ∀ f:X → Y, ∀ A B: Set, image f (A \ B) = (image f A) \ (image f B)) := by
  -- The first line of this construction should be either `apply isTrue` or `apply isFalse`
  apply isFalse
  push_neg
  use {0, 1}
  use {0}
  let f : toSubtype {0, 1} → toSubtype {0}  := fun i ↦ ⟨0, by simp⟩
  use f
  use {0}
  use {1}
  have h1 : image f ({0} \ {1}) = {0} := by
    ext x
    rw [mem_image]
    simp
    unfold f
    simp_all
    tauto
  have h2 : image f {0} = {0} := by
    ext x
    rw [mem_image]
    simp
    unfold f
    simp_all
    tauto
  have h3 : image f {1} = {0} := by
    ext x
    rw [mem_image]
    simp
    unfold f
    simp_all
    tauto
  rw [h1, h2, h3]
  have h4: ({0}:Set) \ {0} = ∅ := by
    ext x
    simp_all
  rw [h4]
  simp
  intro h5
  have h6: 0 ∈ ({0}:Set) := by simp
  rw [h5] at h6
  have h7 := not_mem_empty 0
  contradiction


/-- Exercise 3.4.4 -/
theorem SetTheory.Set.preimage_of_inter {X Y:Set} (f:X → Y) (A B: Set) :
    preimage f (A ∩ B) = (preimage f A) ∩ (preimage f B) := by
      ext x;
      rw [mem_preimage']
      refine ⟨ ?_, by aesop⟩;
      intro ⟨y, ⟨h1, h2⟩⟩
      rw [mem_inter] at *
      rw [mem_preimage', mem_preimage']
      obtain ⟨h3, h4⟩ := h2
      constructor
      . use y
      use y

theorem SetTheory.Set.preimage_of_union {X Y:Set} (f:X → Y) (A B: Set) :
    preimage f (A ∪ B) = (preimage f A) ∪ (preimage f B) := by
      ext x;
      rw [mem_preimage', mem_union, mem_preimage', mem_preimage']
      refine ⟨ ?_, by aesop⟩;
      intro ⟨y, ⟨h1, h2⟩⟩
      rw [mem_union] at h2
      rcases h2 with h2 | h2
      . apply Or.inl
        use y
      apply Or.inr
      use y


theorem SetTheory.Set.preimage_of_diff {X Y:Set} (f:X → Y) (A B: Set) :
    preimage f (A \ B) = (preimage f A) \ (preimage f B)  := by
      ext x;
      rw [mem_preimage', mem_sdiff, mem_preimage', mem_preimage']
      refine ⟨ ?_, by aesop⟩;
      intro ⟨y, ⟨h1, h2⟩⟩
      rw [mem_sdiff] at h2
      obtain ⟨h3, h4⟩ := h2
      constructor
      . use y
      push_neg
      intro z hz
      have h5 : y = z := by
        rw [← h1] at hz
        exact Subtype.ext hz.symm
      rw [← h5]
      exact h4

/-- Exercise 3.4.5 -/
theorem SetTheory.Set.image_preimage_of_surj {X Y:Set} (f:X → Y) :
    (∀ S, S ⊆ Y → image f (preimage f S) = S) ↔ Function.Surjective f := by
      constructor
      . intro h
        unfold Function.Surjective
        intro x
        let a := (SetTheory.singleton x)
        have h0 : x.val ∈ a := (mem_singleton x x).mpr (rfl)
        have h1 : a ⊆ Y := by
          intro y hy
          have h2 := (mem_singleton y x).mp hy
          have h3 : x.val ∈ Y := x.property
          rw [← h2] at h3
          exact h3
        have h2 := h a h1
        rw [← h2] at h0
        rw [mem_image] at h0
        obtain ⟨z, ⟨hz0, hz1⟩⟩ := h0
        use z
        exact Subtype.ext hz1
      intro h S h0
      ext x;
      unfold Function.Surjective at h
      constructor
      . intro h1
        rw [mem_image] at h1
        obtain ⟨z, ⟨hz0, hz1⟩⟩ := h1
        rw [mem_preimage'] at hz0
        obtain ⟨c, ⟨hc0, hc1⟩⟩ := hz0
        have hd : c = z := Subtype.ext hc0
        rw [hd, hz1] at hc1
        exact hc1
      intro h1
      have h2 := h0 x h1
      have ⟨y, hy⟩ := h ⟨x,h2⟩
      rw [mem_image]
      use y
      simp_all
      exact y.property



/-- Exercise 3.4.5 -/
theorem SetTheory.Set.preimage_image_of_inj {X Y:Set} (f:X → Y) :
    (∀ S, S ⊆ X → preimage f (image f S) = S) ↔ Function.Injective f := by
      unfold Function.Injective
      constructor
      . intro h a1 a2 ha
        let a := SetTheory.singleton a1
        have h0 := a1.property
        have h1 {x:Object} := (mem_singleton x a1)
        have h2 : a1.val ∈ a := h1.mpr (rfl)
        have h3 : a ⊆ X := by
          intro x h2
          unfold a at h2
          have h3 := h1.mp h2
          rw [← h3] at h0
          exact h0
        have h4 := h a h3
        rw [← h4] at h2
        have h5 : ↑(f a2) ∈ image f a := by
          rw [← ha]
          simp
          use a1
          constructor
          . use h0
          exact h1.mpr (rfl)
        have h6 : a2.val ∈ preimage f (image f a) := by
          rw [preimage, specification_axiom']
          exact h5
        rw [h4] at h6
        exact Subtype.ext (h1.mp h6).symm
      intro h S hS
      ext x
      constructor
      . intro h1
        rw [mem_preimage'] at h1
        obtain ⟨y, ⟨h2, h3⟩⟩ := h1
        rw [mem_image] at h3
        obtain ⟨z, ⟨h4, h5⟩⟩ := h3
        have h6 := Subtype.ext h5
        have h7 := h h6
        rw [h7] at h4
        rw [h2] at h4
        exact h4
      intro h1
      have h2 := hS x h1
      rw [mem_preimage']
      use ⟨x,h2⟩
      constructor
      . simp
      rw [mem_image]
      use ⟨x,h2⟩





/-- Helper lemma for Exercise 3.4.7. -/
@[simp]
lemma SetTheory.Set.mem_powerset' {S S' : Set} : (S': Object) ∈ S.powerset ↔ S' ⊆ S := by
  simp [mem_powerset]

/-- Another helper lemma for Exercise 3.4.7. -/
lemma SetTheory.Set.mem_union_powerset_replace_iff {S : Set} {P : S.powerset → Object → Prop} {hP : _} {x : Object} :
    x ∈ union (S.powerset.replace (P := P) hP) ↔
    ∃ (S' : S.powerset) (U : Set), P S' U ∧ x ∈ U := by
  grind [union_axiom, replacement_axiom]

noncomputable abbrev SetTheory.Set.PSet {X: Set} (x : powerset X): Set := ((mem_powerset x).mp (x.property)).choose


lemma SetTheory.Set.PSet_prop {X: Set} (x : powerset X): x = set_to_object (PSet x) ∧ PSet x ⊆ X :=
  ((mem_powerset _).mp (x.property)).choose_spec


lemma SetTheory.Set.PSet_prop' (A X : Set) (h :  (A:Object) ∈ powerset X ) :
  A = PSet ⟨A, h⟩ := by
  have := (PSet_prop ⟨A, h⟩).1  -- PSet is the set specifically constructed to correspond to (A : Object)
  simpa using this

abbrev SetTheory.Set.set_partial_functions (X Y:Set) : Set := by
  let PX := powerset X
  let PY := powerset Y

  let fX : PX → Set := fun X' ↦
  union (
    PY.replace (P := fun Y' Y'X' ↦ Y'X' = set_to_object ((PSet Y')^(PSet X')) ) (by aesop)
  )

  exact union (
    PX.replace (P := fun X' YX' ↦ YX' = fX (X')  ) (by aesop)
  )


-- https://github.com/Shaunticlair/analysis/blob/b0bf9f3fb006f08e0a450a8685251709f7223f86/analysis/Analysis/Section_3_4.lean#L511
/-- Exercise 3.4.7 -/
theorem SetTheory.Set.partial_functions {X Y:Set} :
    ∃ Z:Set, ∀ F:Object, F ∈ Z ↔ ∃ X' Y':Set, X' ⊆ X ∧ Y' ⊆ Y ∧ ∃ f: X' → Y', F = f := by
      use set_partial_functions X Y
      intro F
      rw [mem_union_powerset_replace_iff];
      constructor
      · rintro ⟨X', YX', h, hF⟩;
        simp at h
        subst h
        rw [mem_union_powerset_replace_iff] at hF
        obtain ⟨Y', Y'X', hF1, hF⟩ := hF
        simp at hF1
        rw [hF1] at hF
        refine ⟨ PSet X', PSet Y', (PSet_prop X').2, (PSet_prop Y').2, ?_⟩
        simp_all
        obtain ⟨f, hf⟩ := hF
        use f
        exact hf.symm
      rintro ⟨X', Y', hX, hY, ⟨f, hf⟩ ⟩
      use ⟨X', by simp [hX]⟩;
      simp;
      rw [mem_union_powerset_replace_iff]
      use ⟨Y', by simp [hY]⟩;
      simp;
      rw [← mem_powerset'] at hX hY
      rw [← PSet_prop', ← PSet_prop']
      use f
      exact hf.symm

/--
  Exercise 3.4.8.  The point of this exercise is to prove it without using the
  pairwise union operation {kw (of := «term_∪_»)}`∪`.
-/
theorem SetTheory.Set.union_pair_exists (X Y:Set) : ∃ Z:Set, ∀ x, x ∈ Z ↔ (x ∈ X ∨ x ∈ Y) := by
   use union {set_to_object X, set_to_object Y}
   intro x
   rw [union_axiom]
   simp_all
   aesop

/-- Exercise 3.4.9 -/
theorem SetTheory.Set.iInter'_insensitive {I:Set} (β β':I) (A: I → Set) :
    iInter' I β A = iInter' I β' A := by
    ext x;
    unfold iInter'
    simp_all


/-- Exercise 3.4.10 -/
theorem SetTheory.Set.union_iUnion {I J:Set} (A: (I ∪ J:Set) → Set) :
    iUnion I (fun α ↦ A ⟨ α.val, by simp [α.property]⟩)
    ∪ iUnion J (fun α ↦ A ⟨ α.val, by simp [α.property]⟩)
    = iUnion (I ∪ J) A := by
      ext x;
      unfold iUnion
      constructor
      . intro h
        rw [mem_union, union_axiom] at *
        rcases h with h | h
        . obtain ⟨S, ⟨hS1, hS2⟩⟩ := h
          use S
          constructor
          . exact hS1
          rw [replacement_axiom] at *
          obtain ⟨y, hY⟩ := hS2
          have h1 : y.val ∈ I ∪ J := (subset_union_left I J) y.val y.property
          use ⟨y, h1⟩
        rw [union_axiom] at *
        obtain ⟨S, ⟨hS1, hS2⟩⟩ := h
        use S
        constructor
        . exact hS1
        rw [replacement_axiom] at *
        obtain ⟨y, hY⟩ := hS2
        have h1 : y.val ∈ I ∪ J := (subset_union_right I J) y.val y.property
        use ⟨y, h1⟩
      intro h
      simp_all
      rw [union_axiom, union_axiom] at *
      have ⟨S, ⟨hS1, hS2⟩⟩ := h
      rw [replacement_axiom] at *
      obtain ⟨y, hY⟩ := hS2
      have hYY := y.property
      rw [mem_union] at hYY
      rcases hYY with hYY | hYY
      . apply Or.inl
        use S
        constructor
        . exact hS1
        rw [replacement_axiom] at *
        use ⟨y, hYY⟩
      apply Or.inr
      use S
      constructor
      . exact hS1
      rw [replacement_axiom] at *
      use ⟨y, hYY⟩

/-- Exercise 3.4.10 -/
theorem SetTheory.Set.union_of_nonempty {I J:Set} (hI: I ≠ ∅) (hJ: J ≠ ∅) : I ∪ J ≠ ∅ := by
    have ⟨x, hx⟩ := nonempty_def hI
    have h1 := (subset_union_left I J) x hx
    exact nonempty_of_inhabited h1

/-- Exercise 3.4.10 -/
theorem SetTheory.Set.inter_iInter {I J:Set} (hI: I ≠ ∅) (hJ: J ≠ ∅) (A: (I ∪ J:Set) → Set) :
    iInter I hI (fun α ↦ A ⟨ α.val, by simp [α.property]⟩)
    ∩ iInter J hJ (fun α ↦ A ⟨ α.val, by simp [α.property]⟩)
    = iInter (I ∪ J) (union_of_nonempty hI hJ) A := by
      ext x;
      rw [mem_inter]
      constructor
      . intro ⟨h1, h2⟩
        rw [iInter, iInter', specification_axiom''] at *
        obtain ⟨U, hU⟩ := h1
        obtain ⟨V, hV⟩ := h2
        let u := nonempty_choose (hI)
        let v := nonempty_choose (hJ)
        let w := nonempty_choose (union_of_nonempty hI hJ)
        have h3 : w.val ∈ I ∨ w.val ∈ J := by
          have h4 := w.property
          rw [mem_union] at h4
          exact h4
        simp_all
        constructor
        . grind
        intro a h
        have h1 := hU a
        have h2 := hV a
        rcases h with h | h
        . exact h1 h
        exact h2 h
      intro h
      constructor
      . rw [iInter, iInter', specification_axiom''] at *
        simp_all
        obtain ⟨h1, h2⟩ := h
        grind
      simp_all
      obtain ⟨h1, h2⟩ := h
      grind

/-- Exercise 3.4.11 -/
theorem SetTheory.Set.compl_iUnion {X I: Set} (hI: I ≠ ∅) (A: I → Set) :
    X \ iUnion I A = iInter I hI (fun α ↦ X \ A α) := by
      ext x;
      simp_all
      constructor
      . intro ⟨h1, h2⟩
        constructor
        . constructor
          . tauto
          unfold iUnion at h2
          simp [mem_iUnion] at h2
          let k := (nonempty_choose hI)
          have h3 := h2 k k.property
          grind
        intro a b
        constructor
        . tauto
        unfold iUnion at h2
        simp [mem_iUnion] at h2
        exact h2 a b
      intro ⟨⟨h1, h2⟩, h3⟩
      constructor
      . tauto
      unfold iUnion
      simp [mem_iUnion]
      intro y h
      exact (h3 y h).2



/-- Exercise 3.4.11 -/
theorem SetTheory.Set.compl_iInter {X I: Set} (hI: I ≠ ∅) (A: I → Set) :
    X \ iInter I hI A = iUnion I (fun α ↦ X \ A α) := by
      ext x;
      simp_all
      constructor
      . intro ⟨h1, h2⟩
        unfold iUnion
        simp [mem_iUnion]
        constructor
        . exact h1
        let k := A (nonempty_choose hI)
        by_cases h3 : x ∈ k
        . have h4 := h2 h3
          exact h4
        tauto
      unfold iUnion
      simp [mem_iUnion]
      intro h1 y h2 h3
      constructor
      . exact h1
      intro h4
      use y
      use h2


end Chapter3
