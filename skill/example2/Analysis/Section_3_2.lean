import Mathlib.Tactic
import Analysis.Section_3_1

/-!
# Analysis I, Section 3.2: Russell's paradox

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

This section is mostly optional, though it does make explicit the axiom of foundation which is
used in a minor role in an exercise in Section 3.5.

Main constructions and results of this section:

- Russell's paradox (ruling out the axiom of universal specification).
- The axiom of regularity (foundation) - an axiom designed to avoid Russell's paradox.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

--/

namespace Chapter3

export SetTheory (Set Object)

variable [SetTheory]

/-- Axiom 3.8 (Universal specification) -/
abbrev axiom_of_universal_specification : Prop :=
  ∀ P : Object → Prop, ∃ A : Set, ∀ x : Object, x ∈ A ↔ P x

theorem Russells_paradox : ¬ axiom_of_universal_specification := by
  -- This proof is written to follow the structure of the original text.
  intro h
  set P : Object → Prop := fun x ↦ ∃ X:Set, x = X ∧ x ∉ X
  choose Ω hΩ using h P
  by_cases h: (Ω:Object) ∈ Ω
  . have : P (Ω:Object) := (hΩ _).mp h
    obtain ⟨ Ω', ⟨ hΩ1, hΩ2⟩ ⟩ := this
    simp at hΩ1
    rw [←hΩ1] at hΩ2
    contradiction
  have : P (Ω:Object) := by use Ω
  rw [←hΩ] at this
  contradiction

/-- Axiom 3.9 (Regularity) -/
theorem SetTheory.Set.axiom_of_regularity {A:Set} (h: A ≠ ∅) :
    ∃ x:A, ∀ S:Set, x.val = S → Disjoint S A := by
  choose x h h' using regularity_axiom A (nonempty_def h)
  use ⟨x, h⟩
  intro S hS;
  specialize h' S hS
  rw [disjoint_iff, eq_empty_iff_forall_notMem]
  contrapose! h'; simp at h'
  aesop

/--
  Exercise 3.2.1.  The spirit of the exercise is to establish these results without using either
  Russell's paradox, or the empty set.
-/
theorem SetTheory.Set.emptyset_exists (h: axiom_of_universal_specification):
    ∃ (X:Set), ∀ x, x ∉ X := by
  rw [axiom_of_universal_specification] at h
  set P : Object → Prop := fun y ↦ (∃ z:Set, y = set_to_object z ∧ ((∀ x, x ∉ z) ∨ (y ∉ z)))
  choose a ha using h P
  by_cases h1 : (set_to_object a) ∈ a
  . have hb := (ha a).mp h1
    obtain ⟨z, hz_eq, hz_not_mem⟩ := hb
    simp at hz_eq
    rw [←hz_eq] at hz_not_mem
    use a
    rcases hz_not_mem with hy | hy
    . exact hy
    contradiction
  replace ha := (not_congr (ha a)).mp h1
  dsimp [P] at ha
  push_neg at ha
  replace ha := ha a
  simp at ha
  use a
  obtain ⟨ h3, h4 ⟩ := ha
  contradiction

/--
  Exercise 3.2.1.  The spirit of the exercise is to establish these results without using either
  Russell's paradox, or the singleton set.
-/
theorem SetTheory.Set.singleton_exists (h: axiom_of_universal_specification) (x:Object):
    ∃ (X:Set), ∀ y, y ∈ X ↔ y = x := by
  rw [axiom_of_universal_specification] at h
  set P : Object → Prop := fun y ↦ (∃ z:Set, y = set_to_object z ∧ ((∀ y, y ∈ z ↔ y = x) ∨ (y ∉ z)))
  choose a ha using h P
  by_cases h1 : (set_to_object a) ∈ a
  . have hb := (ha a).mp h1
    obtain ⟨z, hz_eq, hz_not_mem⟩ := hb
    simp at hz_eq
    rw [←hz_eq] at hz_not_mem
    use a
    rcases hz_not_mem with hy | hy
    . exact hy
    contradiction
  use a
  replace ha := (not_congr (ha a)).mp h1
  dsimp [P] at ha
  push_neg at ha
  replace ha := ha a
  simp at ha
  obtain ⟨ h3, h4 ⟩ := ha
  contradiction

/--
  Exercise 3.2.1.  The spirit of the exercise is to establish these results without using either
  Russell's paradox, or the pair set.
-/
theorem SetTheory.Set.pair_exists (h: axiom_of_universal_specification) (x₁ x₂:Object):
    ∃ (X:Set), ∀ y, y ∈ X ↔ y = x₁ ∨ y = x₂ := by
  rw [axiom_of_universal_specification] at h
  set P : Object → Prop := fun y ↦ (∃ z:Set, y = set_to_object z ∧ ((∀ y, y ∈ z ↔ y = x₁ ∨ y = x₂) ∨ (y ∉ z)))
  choose a ha using h P
  by_cases h1 : (set_to_object a) ∈ a
  . have hb := (ha a).mp h1
    obtain ⟨z, hz_eq, hz_not_mem⟩ := hb
    simp at hz_eq
    rw [←hz_eq] at hz_not_mem
    use a
    rcases hz_not_mem with hy | hy
    . exact hy
    contradiction
  use a
  replace ha := (not_congr (ha a)).mp h1
  dsimp [P] at ha
  push_neg at ha
  replace ha := ha a
  simp at ha
  obtain ⟨ h3, h4 ⟩ := ha
  contradiction

/--
  Exercise 3.2.1. The spirit of the exercise is to establish these results without using either
  Russell's paradox, or the union operation.
-/
theorem SetTheory.Set.union_exists (h: axiom_of_universal_specification) (A B:Set):
    ∃ (Z:Set), ∀ z, z ∈ Z ↔ z ∈ A ∨ z ∈ B := by
  rw [axiom_of_universal_specification] at h
  set P : Object → Prop := fun y ↦ (∃ z:Set, y = set_to_object z ∧ ((∀ w, w ∈ z ↔ w ∈ A ∨ w ∈ B) ∨ (y ∉ z)))
  choose a ha using h P
  by_cases h1 : (set_to_object a) ∈ a
  . have hb := (ha a).mp h1
    obtain ⟨z, hz_eq, hz_not_mem⟩ := hb
    simp at hz_eq
    rw [←hz_eq] at hz_not_mem
    use a
    rcases hz_not_mem with hy | hy
    . exact hy
    contradiction
  use a
  replace ha := (not_congr (ha a)).mp h1
  dsimp [P] at ha
  push_neg at ha
  replace ha := ha a
  simp at ha
  obtain ⟨ h3, h4 ⟩ := ha
  contradiction
/--
  Exercise 3.2.1. The spirit of the exercise is to establish these results without using either
  Russell's paradox, or the specify operation.
-/
theorem SetTheory.Set.specify_exists (h: axiom_of_universal_specification) (A:Set) (P: A → Prop):
    ∃ (Z:Set), ∀ z, z ∈ Z ↔ ∃ h : z ∈ A, P ⟨ z, h ⟩ := by
  rw [axiom_of_universal_specification] at h
  set P : Object → Prop := fun y ↦ (∃ z:Set, y = set_to_object z ∧ ((∀ w, w ∈ z ↔ ∃ h : w ∈ A, P ⟨ w, h ⟩) ∨ (y ∉ z)))
  choose a ha using h P
  by_cases h1 : (set_to_object a) ∈ a
  . have hb := (ha a).mp h1
    obtain ⟨z, hz_eq, hz_not_mem⟩ := hb
    simp at hz_eq
    rw [←hz_eq] at hz_not_mem
    use a
    rcases hz_not_mem with hy | hy
    . exact hy
    contradiction
  use a
  replace ha := (not_congr (ha a)).mp h1
  dsimp [P] at ha
  push_neg at ha
  replace ha := ha a
  simp at ha
  obtain ⟨ h3, h4 ⟩ := ha
  contradiction

/--
  Exercise 3.2.1. The spirit of the exercise is to establish these results without using either
  Russell's paradox, or the replace operation.
-/
theorem SetTheory.Set.replace_exists (h: axiom_of_universal_specification) (A:Set)
  (P: A → Object → Prop) (hP: ∀ x y y', P x y ∧ P x y' → y = y') :
    ∃ (Z:Set), ∀ y, y ∈ Z ↔ ∃ a : A, P a y := by
  rw [axiom_of_universal_specification] at h
  set P : Object → Prop := fun y ↦ (∃ z:Set, y = set_to_object z ∧ ((∀ y, y ∈ z ↔ ∃ a : A, P a y) ∨ (y ∉ z)))
  choose a ha using h P
  by_cases h1 : (set_to_object a) ∈ a
  . have hb := (ha a).mp h1
    obtain ⟨z, hz_eq, hz_not_mem⟩ := hb
    simp at hz_eq
    rw [←hz_eq] at hz_not_mem
    use a
    rcases hz_not_mem with hy | hy
    . exact hy
    contradiction
  use a
  replace ha := (not_congr (ha a)).mp h1
  dsimp [P] at ha
  push_neg at ha
  replace ha := ha a
  simp at ha
  obtain ⟨ h3, h4 ⟩ := ha
  contradiction

/-- Exercise 3.2.2 -/
theorem SetTheory.Set.not_mem_self (A:Set) : (A:Object) ∉ A := by
  have h1 :  (set_to_object A) ∈ ({set_to_object A}:Set) := by simp
  have h2 : ({set_to_object A}) ≠ (∅:Set) := by
    by_contra h2
    rw [h2] at h1
    have h3 := not_mem_empty (set_to_object A)
    contradiction
  have h4 := axiom_of_regularity h2
  obtain ⟨x, h5⟩ := h4
  by_contra h6
  have h7 : (↑x : Object) = set_to_object A := by
    simpa using x.property
  have h8 := h5 A h7
  rw [disjoint_iff] at h8
  have h9 : A ∩ {set_to_object A} = {set_to_object A} := by
    ext x
    simp
    intro h10
    rw [← h10] at h6
    exact h6
  rw [h8] at h9
  replace h9 := h9.symm
  contradiction


/-- Exercise 3.2.2 -/
theorem SetTheory.Set.not_mem_mem (A B:Set) : (A:Object) ∉ B ∨ (B:Object) ∉ A := by
  have h1 :  (set_to_object A) ∈ ({set_to_object A, set_to_object B}:Set) := by simp
  have h2 :  (set_to_object B) ∈ ({set_to_object A, set_to_object B}:Set) := by simp
  have h3 : ({set_to_object A, set_to_object B}) ≠ (∅:Set) := by
    by_contra h2
    rw [h2] at h1
    have h3 := not_mem_empty (set_to_object A)
    contradiction
  have h4 := axiom_of_regularity h3
  obtain ⟨x, h5⟩ := h4
  by_contra h6
  push_neg at h6
  obtain ⟨h7, h8⟩ := h6
  have h9 : ((↑x : Object) = set_to_object A) ∨ ((↑x : Object) = set_to_object B) := by
    simpa using x.property
  have h10 := h5 A
  have h14 := h5 B
  rcases h9 with h9 | h9
  . have h11 := h10 h9
    rw [disjoint_iff] at h11
    have h12 := And.intro h8 h2
    rw [← mem_inter] at h12
    have h13 := not_mem_empty (set_to_object B)
    rw [← h11] at h13
    contradiction
  have h15 := h14 h9
  rw [disjoint_iff] at h15
  have h16 := And.intro h7 h1
  rw [← mem_inter] at h16
  have h17 := not_mem_empty (set_to_object A)
  rw [← h15] at h17
  contradiction




/-- Exercise 3.2.3 -/
theorem SetTheory.Set.univ_iff : axiom_of_universal_specification ↔
  ∃ (U:Set), ∀ x, x ∈ U := by
    constructor
    . intro h
      rw [axiom_of_universal_specification] at h
      set P : Object → Prop := fun y ↦ (∃ z:Set, y = set_to_object z ∧ ((∀ x, x ∈ z) ∨ (y ∉ z)))
      choose a ha using h P
      by_cases h1 : (set_to_object a) ∈ a
      . have hb := (ha a).mp h1
        obtain ⟨z, hz_eq, hz_not_mem⟩ := hb
        simp at hz_eq
        rw [←hz_eq] at hz_not_mem
        use a
        rcases hz_not_mem with hy | hy
        . exact hy
        contradiction
      use a
      replace ha := (not_congr (ha a)).mp h1
      dsimp [P] at ha
      push_neg at ha
      replace ha := ha a
      simp at ha
      obtain ⟨ h3, h4 ⟩ := ha
      contradiction
    rw [axiom_of_universal_specification]
    intro h P
    obtain ⟨U, h1⟩ := h
    let P_on_U : U → Prop := fun x => P x.val
    use (U.specify P_on_U)
    intro x
    constructor
    . intro h2
      have hspecification := (specification_axiom'' P_on_U x).mp h2
      obtain ⟨b, h4⟩ := hspecification
      dsimp [P_on_U] at h4
      exact h4
    intro h2
    have h3 := h1 x
    simp_all
    dsimp [P_on_U]
    exact h2



/-- Exercise 3.2.3 -/
theorem SetTheory.Set.no_univ : ¬ ∃ (U:Set), ∀ (x:Object), x ∈ U := by
  exact (not_congr univ_iff).mp Russells_paradox

end Chapter3
