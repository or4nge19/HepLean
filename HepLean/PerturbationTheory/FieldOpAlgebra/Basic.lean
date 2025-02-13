/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.FieldOpFreeAlgebra.SuperCommute
import Mathlib.Algebra.RingQuot
import Mathlib.RingTheory.TwoSidedIdeal.Operations
/-!

# Field operator algebra

-/

namespace FieldSpecification
open FieldOpFreeAlgebra
open HepLean.List
open FieldStatistic

variable (𝓕 : FieldSpecification)

/-- The set contains the super-commutators equal to zero in the operator algebra.
  This contains e.g. the super-commutator of two creation operators. -/
def fieldOpIdealSet : Set (FieldOpFreeAlgebra 𝓕) :=
  { x |
    (∃ (φ1 φ2 φ3 : 𝓕.CrAnFieldOp),
        x = [ofCrAnOpF φ1, [ofCrAnOpF φ2, ofCrAnOpF φ3]ₛca]ₛca)
    ∨ (∃ (φc φc' : 𝓕.CrAnFieldOp) (_ : 𝓕 |>ᶜ φc = .create) (_ : 𝓕 |>ᶜ φc' = .create),
      x = [ofCrAnOpF φc, ofCrAnOpF φc']ₛca)
    ∨ (∃ (φa φa' : 𝓕.CrAnFieldOp) (_ : 𝓕 |>ᶜ φa = .annihilate) (_ : 𝓕 |>ᶜ φa' = .annihilate),
      x = [ofCrAnOpF φa, ofCrAnOpF φa']ₛca)
    ∨ (∃ (φ φ' : 𝓕.CrAnFieldOp) (_ : ¬ (𝓕 |>ₛ φ) = (𝓕 |>ₛ φ')),
      x = [ofCrAnOpF φ, ofCrAnOpF φ']ₛca)}

/-- For a field specification `𝓕`, the algebra `𝓕.FieldOpAlgebra` is defined as the quotient
  of the free algebra `𝓕.FieldOpFreeAlgebra` by the ideal generated by
- `[ofCrAnOpF φc, ofCrAnOpF φc']ₛca` for `φc` and `φc'` field creation operators.
  This corresponds to the condition that two creation operators always super-commute.
- `[ofCrAnOpF φa, ofCrAnOpF φa']ₛca` for `φa` and `φa'` field annihilation operators.
  This corresponds to the condition that two annihilation operators always super-commute.
- `[ofCrAnOpF φ, ofCrAnOpF φ']ₛca` for `φ` and `φ'` operators with different statistics.
  This corresponds to the condition that two operators with different statistics always
  super-commute. In other words, fermions and bosons always super-commute.
- `[ofCrAnOpF φ1, [ofCrAnOpF φ2, ofCrAnOpF φ3]ₛca]ₛca`. This corresponds to the condition,
  when combined with the conditions above, that the super-commutator is in the center
  of the algebra.
-/
abbrev FieldOpAlgebra : Type := (TwoSidedIdeal.span 𝓕.fieldOpIdealSet).ringCon.Quotient

namespace FieldOpAlgebra
variable {𝓕 : FieldSpecification}

/-- The instance of a setoid on `FieldOpFreeAlgebra` from the ideal `TwoSidedIdeal`. -/
instance : Setoid (FieldOpFreeAlgebra 𝓕) := (TwoSidedIdeal.span 𝓕.fieldOpIdealSet).ringCon.toSetoid

lemma equiv_iff_sub_mem_ideal (x y : FieldOpFreeAlgebra 𝓕) :
    x ≈ y ↔ x - y ∈ TwoSidedIdeal.span 𝓕.fieldOpIdealSet := by
  rw [← TwoSidedIdeal.rel_iff]
  rfl

lemma equiv_iff_exists_add (x y : FieldOpFreeAlgebra 𝓕) :
    x ≈ y ↔ ∃ a, x = y + a ∧ a ∈ TwoSidedIdeal.span 𝓕.fieldOpIdealSet := by
  apply Iff.intro
  · intro h
    rw [equiv_iff_sub_mem_ideal] at h
    use x - y
    simp [h]
  · intro h
    obtain ⟨a, rfl, ha⟩ := h
    rw [equiv_iff_sub_mem_ideal]
    simp [ha]

/-- For a field specification `𝓕`, the projection

`𝓕.FieldOpFreeAlgebra →ₐ[ℂ] FieldOpAlgebra 𝓕`

taking each element of `𝓕.FieldOpFreeAlgebra` to its equivalence class in `FieldOpAlgebra 𝓕`. -/
def ι : FieldOpFreeAlgebra 𝓕 →ₐ[ℂ] FieldOpAlgebra 𝓕 where
  toFun := (TwoSidedIdeal.span 𝓕.fieldOpIdealSet).ringCon.mk'
  map_one' := by rfl
  map_mul' x y := by rfl
  map_zero' := by rfl
  map_add' x y := by rfl
  commutes' x := by rfl

lemma ι_surjective : Function.Surjective (@ι 𝓕) := by
  intro x
  obtain ⟨x⟩ := x
  use x
  rfl

lemma ι_apply (x : FieldOpFreeAlgebra 𝓕) : ι x = Quotient.mk _ x := rfl

lemma ι_of_mem_fieldOpIdealSet (x : FieldOpFreeAlgebra 𝓕) (hx : x ∈ 𝓕.fieldOpIdealSet) :
    ι x = 0 := by
  rw [ι_apply]
  change ⟦x⟧ = ⟦0⟧
  simp only [ringConGen, Quotient.eq]
  refine RingConGen.Rel.of x 0 ?_
  simpa using hx

lemma ι_superCommuteF_of_create_create (φc φc' : 𝓕.CrAnFieldOp) (hφc : 𝓕 |>ᶜ φc = .create)
    (hφc' : 𝓕 |>ᶜ φc' = .create) : ι [ofCrAnOpF φc, ofCrAnOpF φc']ₛca = 0 := by
  apply ι_of_mem_fieldOpIdealSet
  simp only [fieldOpIdealSet, exists_and_left, Set.mem_setOf_eq]
  simp only [exists_prop]
  right
  left
  use φc, φc', hφc, hφc'

lemma ι_superCommuteF_of_annihilate_annihilate (φa φa' : 𝓕.CrAnFieldOp)
    (hφa : 𝓕 |>ᶜ φa = .annihilate) (hφa' : 𝓕 |>ᶜ φa' = .annihilate) :
    ι [ofCrAnOpF φa, ofCrAnOpF φa']ₛca = 0 := by
  apply ι_of_mem_fieldOpIdealSet
  simp only [fieldOpIdealSet, exists_and_left, Set.mem_setOf_eq]
  simp only [exists_prop]
  right
  right
  left
  use φa, φa', hφa, hφa'

lemma ι_superCommuteF_of_diff_statistic {φ ψ : 𝓕.CrAnFieldOp}
    (h : (𝓕 |>ₛ φ) ≠ (𝓕 |>ₛ ψ)) : ι [ofCrAnOpF φ, ofCrAnOpF ψ]ₛca = 0 := by
  apply ι_of_mem_fieldOpIdealSet
  simp only [fieldOpIdealSet, exists_prop, exists_and_left, Set.mem_setOf_eq]
  right
  right
  right
  use φ, ψ

lemma ι_superCommuteF_zero_of_fermionic (φ ψ : 𝓕.CrAnFieldOp)
    (h : [ofCrAnOpF φ, ofCrAnOpF ψ]ₛca ∈ statisticSubmodule fermionic) :
    ι [ofCrAnOpF φ, ofCrAnOpF ψ]ₛca = 0 := by
  rw [← ofCrAnListF_singleton, ← ofCrAnListF_singleton] at h ⊢
  rcases statistic_neq_of_superCommuteF_fermionic h with h | h
  · simp only [ofCrAnListF_singleton]
    apply ι_superCommuteF_of_diff_statistic
    simpa using h
  · simp [h]

lemma ι_superCommuteF_ofCrAnOpF_ofCrAnOpF_bosonic_or_zero (φ ψ : 𝓕.CrAnFieldOp) :
    [ofCrAnOpF φ, ofCrAnOpF ψ]ₛca ∈ statisticSubmodule bosonic ∨
    ι [ofCrAnOpF φ, ofCrAnOpF ψ]ₛca = 0 := by
  rcases superCommuteF_ofCrAnListF_ofCrAnListF_bosonic_or_fermionic [φ] [ψ] with h | h
  · simp_all [ofCrAnListF_singleton]
  · simp_all only [ofCrAnListF_singleton]
    right
    exact ι_superCommuteF_zero_of_fermionic _ _ h

/-!

## Super-commutes are in the center

-/

@[simp]
lemma ι_superCommuteF_ofCrAnOpF_superCommuteF_ofCrAnOpF_ofCrAnOpF (φ1 φ2 φ3 : 𝓕.CrAnFieldOp) :
    ι [ofCrAnOpF φ1, [ofCrAnOpF φ2, ofCrAnOpF φ3]ₛca]ₛca = 0 := by
  apply ι_of_mem_fieldOpIdealSet
  simp only [fieldOpIdealSet, exists_prop, exists_and_left, Set.mem_setOf_eq]
  left
  use φ1, φ2, φ3

lemma ι_superCommuteF_superCommuteF_ofCrAnOpF_ofCrAnOpF_ofCrAnOpF (φ1 φ2 φ3 : 𝓕.CrAnFieldOp) :
    ι [[ofCrAnOpF φ1, ofCrAnOpF φ2]ₛca, ofCrAnOpF φ3]ₛca = 0 := by
  rw [← ofCrAnListF_singleton, ← ofCrAnListF_singleton, ← ofCrAnListF_singleton]
  rcases superCommuteF_ofCrAnListF_ofCrAnListF_bosonic_or_fermionic [φ1] [φ2] with h | h
  · rw [bonsonic_superCommuteF_symm h]
    simp [ofCrAnListF_singleton]
  · rcases ofCrAnListF_bosonic_or_fermionic [φ3] with h' | h'
    · rw [superCommuteF_bonsonic_symm h']
      simp [ofCrAnListF_singleton]
    · rw [superCommuteF_fermionic_fermionic_symm h h']
      simp [ofCrAnListF_singleton]

lemma ι_superCommuteF_superCommuteF_ofCrAnOpF_ofCrAnOpF_ofCrAnListF (φ1 φ2 : 𝓕.CrAnFieldOp)
    (φs : List 𝓕.CrAnFieldOp) :
    ι [[ofCrAnOpF φ1, ofCrAnOpF φ2]ₛca, ofCrAnListF φs]ₛca = 0 := by
  rw [← ofCrAnListF_singleton, ← ofCrAnListF_singleton]
  rcases superCommuteF_ofCrAnListF_ofCrAnListF_bosonic_or_fermionic [φ1] [φ2] with h | h
  · rw [superCommuteF_bosonic_ofCrAnListF_eq_sum _ _ h]
    simp [ofCrAnListF_singleton, ι_superCommuteF_superCommuteF_ofCrAnOpF_ofCrAnOpF_ofCrAnOpF]
  · rw [superCommuteF_fermionic_ofCrAnListF_eq_sum _ _ h]
    simp [ofCrAnListF_singleton, ι_superCommuteF_superCommuteF_ofCrAnOpF_ofCrAnOpF_ofCrAnOpF]

@[simp]
lemma ι_superCommuteF_superCommuteF_ofCrAnOpF_ofCrAnOpF_fieldOpFreeAlgebra (φ1 φ2 : 𝓕.CrAnFieldOp)
    (a : 𝓕.FieldOpFreeAlgebra) : ι [[ofCrAnOpF φ1, ofCrAnOpF φ2]ₛca, a]ₛca = 0 := by
  change (ι.toLinearMap ∘ₗ superCommuteF [ofCrAnOpF φ1, ofCrAnOpF φ2]ₛca) a = _
  have h1 : (ι.toLinearMap ∘ₗ superCommuteF [ofCrAnOpF φ1, ofCrAnOpF φ2]ₛca) = 0 := by
    apply (ofCrAnListFBasis.ext fun l ↦ ?_)
    simp [ι_superCommuteF_superCommuteF_ofCrAnOpF_ofCrAnOpF_ofCrAnListF]
  rw [h1]
  simp

lemma ι_commute_fieldOpFreeAlgebra_superCommuteF_ofCrAnOpF_ofCrAnOpF (φ1 φ2 : 𝓕.CrAnFieldOp)
    (a : 𝓕.FieldOpFreeAlgebra) : ι a * ι [ofCrAnOpF φ1, ofCrAnOpF φ2]ₛca -
    ι [ofCrAnOpF φ1, ofCrAnOpF φ2]ₛca * ι a = 0 := by
  rcases ι_superCommuteF_ofCrAnOpF_ofCrAnOpF_bosonic_or_zero φ1 φ2 with h | h
  swap
  · simp [h]
  trans - ι [[ofCrAnOpF φ1, ofCrAnOpF φ2]ₛca, a]ₛca
  · rw [bosonic_superCommuteF h]
    simp
  · simp

lemma ι_superCommuteF_ofCrAnOpF_ofCrAnOpF_mem_center (φ ψ : 𝓕.CrAnFieldOp) :
    ι [ofCrAnOpF φ, ofCrAnOpF ψ]ₛca ∈ Subalgebra.center ℂ 𝓕.FieldOpAlgebra := by
  rw [Subalgebra.mem_center_iff]
  intro a
  obtain ⟨a, rfl⟩ := ι_surjective a
  have h0 := ι_commute_fieldOpFreeAlgebra_superCommuteF_ofCrAnOpF_ofCrAnOpF φ ψ a
  trans ι ((superCommuteF (ofCrAnOpF φ)) (ofCrAnOpF ψ)) * ι a + 0
  swap
  simp only [add_zero]
  rw [← h0]
  abel

/-!

## The kernel of ι
-/

lemma ι_eq_zero_iff_mem_ideal (x : FieldOpFreeAlgebra 𝓕) :
    ι x = 0 ↔ x ∈ TwoSidedIdeal.span 𝓕.fieldOpIdealSet := by
  rw [ι_apply]
  change ⟦x⟧ = ⟦0⟧ ↔ _
  simp only [ringConGen, Quotient.eq]
  rw [TwoSidedIdeal.mem_iff]
  simp only
  rfl

lemma bosonicProjF_mem_fieldOpIdealSet_or_zero (x : FieldOpFreeAlgebra 𝓕)
    (hx : x ∈ 𝓕.fieldOpIdealSet) :
    x.bosonicProjF.1 ∈ 𝓕.fieldOpIdealSet ∨ x.bosonicProjF = 0 := by
  have hx' := hx
  simp only [fieldOpIdealSet, exists_prop, Set.mem_setOf_eq] at hx
  rcases hx with ⟨φ1, φ2, φ3, rfl⟩ | ⟨φc, φc', hφc, hφc', rfl⟩ | ⟨φa, φa', hφa, hφa', rfl⟩ |
    ⟨φ, φ', hdiff, rfl⟩
  · rcases superCommuteF_superCommuteF_ofCrAnOpF_bosonic_or_fermionic φ1 φ2 φ3 with h | h
    · left
      rw [bosonicProjF_of_mem_bosonic _ h]
      simpa using hx'
    · right
      rw [bosonicProjF_of_mem_fermionic _ h]
  · rcases superCommuteF_ofCrAnOpF_ofCrAnOpF_bosonic_or_fermionic φc φc' with h | h
    · left
      rw [bosonicProjF_of_mem_bosonic _ h]
      simpa using hx'
    · right
      rw [bosonicProjF_of_mem_fermionic _ h]
  · rcases superCommuteF_ofCrAnOpF_ofCrAnOpF_bosonic_or_fermionic φa φa' with h | h
    · left
      rw [bosonicProjF_of_mem_bosonic _ h]
      simpa using hx'
    · right
      rw [bosonicProjF_of_mem_fermionic _ h]
  · rcases superCommuteF_ofCrAnOpF_ofCrAnOpF_bosonic_or_fermionic φ φ' with h | h
    · left
      rw [bosonicProjF_of_mem_bosonic _ h]
      simpa using hx'
    · right
      rw [bosonicProjF_of_mem_fermionic _ h]

lemma fermionicProjF_mem_fieldOpIdealSet_or_zero (x : FieldOpFreeAlgebra 𝓕)
    (hx : x ∈ 𝓕.fieldOpIdealSet) :
    x.fermionicProjF.1 ∈ 𝓕.fieldOpIdealSet ∨ x.fermionicProjF = 0 := by
  have hx' := hx
  simp only [fieldOpIdealSet, exists_prop, Set.mem_setOf_eq] at hx
  rcases hx with ⟨φ1, φ2, φ3, rfl⟩ | ⟨φc, φc', hφc, hφc', rfl⟩ | ⟨φa, φa', hφa, hφa', rfl⟩ |
    ⟨φ, φ', hdiff, rfl⟩
  · rcases superCommuteF_superCommuteF_ofCrAnOpF_bosonic_or_fermionic φ1 φ2 φ3 with h | h
    · right
      rw [fermionicProjF_of_mem_bosonic _ h]
    · left
      rw [fermionicProjF_of_mem_fermionic _ h]
      simpa using hx'
  · rcases superCommuteF_ofCrAnOpF_ofCrAnOpF_bosonic_or_fermionic φc φc' with h | h
    · right
      rw [fermionicProjF_of_mem_bosonic _ h]
    · left
      rw [fermionicProjF_of_mem_fermionic _ h]
      simpa using hx'
  · rcases superCommuteF_ofCrAnOpF_ofCrAnOpF_bosonic_or_fermionic φa φa' with h | h
    · right
      rw [fermionicProjF_of_mem_bosonic _ h]
    · left
      rw [fermionicProjF_of_mem_fermionic _ h]
      simpa using hx'
  · rcases superCommuteF_ofCrAnOpF_ofCrAnOpF_bosonic_or_fermionic φ φ' with h | h
    · right
      rw [fermionicProjF_of_mem_bosonic _ h]
    · left
      rw [fermionicProjF_of_mem_fermionic _ h]
      simpa using hx'

lemma bosonicProjF_mem_ideal (x : FieldOpFreeAlgebra 𝓕)
    (hx : x ∈ TwoSidedIdeal.span 𝓕.fieldOpIdealSet) :
    x.bosonicProjF.1 ∈ TwoSidedIdeal.span 𝓕.fieldOpIdealSet := by
  rw [TwoSidedIdeal.mem_span_iff_mem_addSubgroup_closure] at hx
  let p {k : Set 𝓕.FieldOpFreeAlgebra} (a : FieldOpFreeAlgebra 𝓕)
    (h : a ∈ AddSubgroup.closure k) : Prop :=
    a.bosonicProjF.1 ∈ TwoSidedIdeal.span 𝓕.fieldOpIdealSet
  change p x hx
  apply AddSubgroup.closure_induction
  · intro x hx
    simp only [p]
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hx
    obtain ⟨d, hd, y, hy, rfl⟩ := Set.mem_mul.mp ha
    rw [bosonicProjF_mul, bosonicProjF_mul, fermionicProjF_mul]
    simp only [add_mul]
    rcases fermionicProjF_mem_fieldOpIdealSet_or_zero y hy with hfy | hfy
      <;> rcases bosonicProjF_mem_fieldOpIdealSet_or_zero y hy with hby | hby
    · apply TwoSidedIdeal.add_mem
      apply TwoSidedIdeal.add_mem
      · /- boson, boson, boson mem-/
        rw [TwoSidedIdeal.mem_span_iff_mem_addSubgroup_closure]
        refine Set.mem_of_mem_of_subset ?_ AddSubgroup.subset_closure
        apply Set.mem_mul.mpr
        use ↑(bosonicProjF d) * ↑(bosonicProjF y)
        apply And.intro
        · apply Set.mem_mul.mpr
          use bosonicProjF d
          simp only [Set.mem_univ, mul_eq_mul_left_iff, ZeroMemClass.coe_eq_zero, true_and]
          use (bosonicProjF y).1
          simp [hby]
        · use ↑(bosonicProjF b)
          simp
      · /- fermion, fermion, boson mem-/
        rw [TwoSidedIdeal.mem_span_iff_mem_addSubgroup_closure]
        refine Set.mem_of_mem_of_subset ?_ AddSubgroup.subset_closure
        apply Set.mem_mul.mpr
        use ↑(fermionicProjF d) * ↑(fermionicProjF y)
        apply And.intro
        · apply Set.mem_mul.mpr
          use fermionicProjF d
          simp only [Set.mem_univ, mul_eq_mul_left_iff, ZeroMemClass.coe_eq_zero, true_and]
          use (fermionicProjF y).1
          simp [hby, hfy]
        · use ↑(bosonicProjF b)
          simp
      apply TwoSidedIdeal.add_mem
      · /- boson, fermion, fermion mem-/
        rw [TwoSidedIdeal.mem_span_iff_mem_addSubgroup_closure]
        refine Set.mem_of_mem_of_subset ?_ AddSubgroup.subset_closure
        apply Set.mem_mul.mpr
        use ↑(bosonicProjF d) * ↑(fermionicProjF y)
        apply And.intro
        · apply Set.mem_mul.mpr
          use bosonicProjF d
          simp only [Set.mem_univ, mul_eq_mul_left_iff, ZeroMemClass.coe_eq_zero, true_and]
          use (fermionicProjF y).1
          simp [hby, hfy]
        · use ↑(fermionicProjF b)
          simp
      · /- fermion, boson, fermion mem-/
        rw [TwoSidedIdeal.mem_span_iff_mem_addSubgroup_closure]
        refine Set.mem_of_mem_of_subset ?_ AddSubgroup.subset_closure
        apply Set.mem_mul.mpr
        use ↑(fermionicProjF d) * ↑(bosonicProjF y)
        apply And.intro
        · apply Set.mem_mul.mpr
          use fermionicProjF d
          simp only [Set.mem_univ, mul_eq_mul_left_iff, ZeroMemClass.coe_eq_zero, true_and]
          use (bosonicProjF y).1
          simp [hby, hfy]
        · use ↑(fermionicProjF b)
          simp
    · simp only [hby, ZeroMemClass.coe_zero, mul_zero, zero_mul, zero_add, add_zero]
      apply TwoSidedIdeal.add_mem
      · /- fermion, fermion, boson mem-/
        rw [TwoSidedIdeal.mem_span_iff_mem_addSubgroup_closure]
        refine Set.mem_of_mem_of_subset ?_ AddSubgroup.subset_closure
        apply Set.mem_mul.mpr
        use ↑(fermionicProjF d) * ↑(fermionicProjF y)
        apply And.intro
        · apply Set.mem_mul.mpr
          use fermionicProjF d
          simp only [Set.mem_univ, mul_eq_mul_left_iff, ZeroMemClass.coe_eq_zero, true_and]
          use (fermionicProjF y).1
          simp [hby, hfy]
        · use ↑(bosonicProjF b)
          simp
      · /- boson, fermion, fermion mem-/
        rw [TwoSidedIdeal.mem_span_iff_mem_addSubgroup_closure]
        refine Set.mem_of_mem_of_subset ?_ AddSubgroup.subset_closure
        apply Set.mem_mul.mpr
        use ↑(bosonicProjF d) * ↑(fermionicProjF y)
        apply And.intro
        · apply Set.mem_mul.mpr
          use bosonicProjF d
          simp only [Set.mem_univ, mul_eq_mul_left_iff, ZeroMemClass.coe_eq_zero, true_and]
          use (fermionicProjF y).1
          simp [hby, hfy]
        · use ↑(fermionicProjF b)
          simp
    · simp only [hfy, ZeroMemClass.coe_zero, mul_zero, zero_mul, add_zero, zero_add]
      apply TwoSidedIdeal.add_mem
      · /- boson, boson, boson mem-/
        rw [TwoSidedIdeal.mem_span_iff_mem_addSubgroup_closure]
        refine Set.mem_of_mem_of_subset ?_ AddSubgroup.subset_closure
        apply Set.mem_mul.mpr
        use ↑(bosonicProjF d) * ↑(bosonicProjF y)
        apply And.intro
        · apply Set.mem_mul.mpr
          use bosonicProjF d
          simp only [Set.mem_univ, mul_eq_mul_left_iff, ZeroMemClass.coe_eq_zero, true_and]
          use (bosonicProjF y).1
          simp [hby]
        · use ↑(bosonicProjF b)
          simp
      · /- fermion, boson, fermion mem-/
        rw [TwoSidedIdeal.mem_span_iff_mem_addSubgroup_closure]
        refine Set.mem_of_mem_of_subset ?_ AddSubgroup.subset_closure
        apply Set.mem_mul.mpr
        use ↑(fermionicProjF d) * ↑(bosonicProjF y)
        apply And.intro
        · apply Set.mem_mul.mpr
          use fermionicProjF d
          simp only [Set.mem_univ, mul_eq_mul_left_iff, ZeroMemClass.coe_eq_zero, true_and]
          use (bosonicProjF y).1
          simp [hby, hfy]
        · use ↑(fermionicProjF b)
          simp
    · simp [hfy, hby]
  · simp [p]
  · intro x y hx hy hpx hpy
    simp_all only [map_add, Submodule.coe_add, p]
    apply TwoSidedIdeal.add_mem
    · exact hpx
    · exact hpy
  · intro x hx
    simp [p]

lemma fermionicProjF_mem_ideal (x : FieldOpFreeAlgebra 𝓕)
    (hx : x ∈ TwoSidedIdeal.span 𝓕.fieldOpIdealSet) :
    x.fermionicProjF.1 ∈ TwoSidedIdeal.span 𝓕.fieldOpIdealSet := by
  have hb := bosonicProjF_mem_ideal x hx
  rw [← ι_eq_zero_iff_mem_ideal] at hx hb ⊢
  rw [← bosonicProjF_add_fermionicProjF x] at hx
  simp only [map_add] at hx
  simp_all

lemma ι_eq_zero_iff_ι_bosonicProjF_fermonicProj_zero (x : FieldOpFreeAlgebra 𝓕) :
    ι x = 0 ↔ ι x.bosonicProjF.1 = 0 ∧ ι x.fermionicProjF.1 = 0 := by
  apply Iff.intro
  · intro h
    rw [ι_eq_zero_iff_mem_ideal] at h ⊢
    rw [ι_eq_zero_iff_mem_ideal]
    apply And.intro
    · exact bosonicProjF_mem_ideal x h
    · exact fermionicProjF_mem_ideal x h
  · intro h
    rw [← bosonicProjF_add_fermionicProjF x]
    simp_all

/-!

## Constructors

-/

/-- For a field specification `𝓕` and an element `φ` of `𝓕.FieldOp`,
  `ofFieldOp φ` is defined as the element of
  `𝓕.FieldOpAlgebra` given by `ι (ofFieldOpF φ)`. -/
def ofFieldOp (φ : 𝓕.FieldOp) : 𝓕.FieldOpAlgebra := ι (ofFieldOpF φ)

lemma ofFieldOp_eq_ι_ofFieldOpF (φ : 𝓕.FieldOp) : ofFieldOp φ = ι (ofFieldOpF φ) := rfl

/-- For a field specification `𝓕` and a list `φs` of `𝓕.FieldOp`,
  `ofFieldOpList φs` is defined as the element of
  `𝓕.FieldOpAlgebra` given by `ι (ofFieldOpListF φ)`. -/
def ofFieldOpList (φs : List 𝓕.FieldOp) : 𝓕.FieldOpAlgebra := ι (ofFieldOpListF φs)

lemma ofFieldOpList_eq_ι_ofFieldOpListF (φs : List 𝓕.FieldOp) :
    ofFieldOpList φs = ι (ofFieldOpListF φs) := rfl

lemma ofFieldOpList_append (φs ψs : List 𝓕.FieldOp) :
    ofFieldOpList (φs ++ ψs) = ofFieldOpList φs * ofFieldOpList ψs := by
  simp only [ofFieldOpList]
  rw [ofFieldOpListF_append]
  simp

lemma ofFieldOpList_cons (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp) :
    ofFieldOpList (φ :: φs) = ofFieldOp φ * ofFieldOpList φs := by
  simp only [ofFieldOpList]
  rw [ofFieldOpListF_cons]
  simp only [map_mul]
  rfl

lemma ofFieldOpList_singleton (φ : 𝓕.FieldOp) :
    ofFieldOpList [φ] = ofFieldOp φ := by
  simp only [ofFieldOpList, ofFieldOp, ofFieldOpListF_singleton]

/-- For a field specification `𝓕` and an element `φ` of `𝓕.CrAnFieldOp`,
  `ofCrAnOp φ` is defined as the element of
  `𝓕.FieldOpAlgebra` given by `ι (ofCrAnOpF φ)`. -/
def ofCrAnOp (φ : 𝓕.CrAnFieldOp) : 𝓕.FieldOpAlgebra := ι (ofCrAnOpF φ)

lemma ofCrAnOp_eq_ι_ofCrAnOpF (φ : 𝓕.CrAnFieldOp) :
    ofCrAnOp φ = ι (ofCrAnOpF φ) := rfl

lemma ofFieldOp_eq_sum (φ : 𝓕.FieldOp) :
    ofFieldOp φ = (∑ i : 𝓕.fieldOpToCrAnType φ, ofCrAnOp ⟨φ, i⟩) := by
  rw [ofFieldOp, ofFieldOpF]
  simp only [map_sum]
  rfl

/-- For a field specification `𝓕` and a list `φs` of `𝓕.CrAnFieldOp`,
  `ofCrAnList φs` is defined as the element of
  `𝓕.FieldOpAlgebra` given by `ι (ofCrAnListF φ)`. -/
def ofCrAnList (φs : List 𝓕.CrAnFieldOp) : 𝓕.FieldOpAlgebra := ι (ofCrAnListF φs)

lemma ofCrAnList_eq_ι_ofCrAnListF (φs : List 𝓕.CrAnFieldOp) :
    ofCrAnList φs = ι (ofCrAnListF φs) := rfl

lemma ofCrAnList_append (φs ψs : List 𝓕.CrAnFieldOp) :
    ofCrAnList (φs ++ ψs) = ofCrAnList φs * ofCrAnList ψs := by
  simp only [ofCrAnList]
  rw [ofCrAnListF_append]
  simp

lemma ofCrAnList_singleton (φ : 𝓕.CrAnFieldOp) :
    ofCrAnList [φ] = ofCrAnOp φ := by
  simp only [ofCrAnList, ofCrAnOp, ofCrAnListF_singleton]

lemma ofFieldOpList_eq_sum (φs : List 𝓕.FieldOp) :
    ofFieldOpList φs = ∑ s : CrAnSection φs, ofCrAnList s.1 := by
  rw [ofFieldOpList, ofFieldOpListF_sum]
  simp only [map_sum]
  rfl

remark notation_drop := "In doc-strings we will often drop explicit applications of `ofCrAnOp`,
`ofCrAnList`, `ofFieldOp`, and `ofFieldOpList`"

/-- For a field specification `𝓕`, and an element `φ` of `𝓕.FieldOp`, the
  annihilation part of `𝓕.FieldOp` as an element of `𝓕.FieldOpAlgebra`.
  Thus for `φ`
- an incoming asymptotic state this is `0`.
- a position based state this is `ofCrAnOp ⟨φ, .create⟩`.
- an outgoing asymptotic state this is `ofCrAnOp ⟨φ, ()⟩`. -/
def anPart (φ : 𝓕.FieldOp) : 𝓕.FieldOpAlgebra := ι (anPartF φ)

lemma anPart_eq_ι_anPartF (φ : 𝓕.FieldOp) : anPart φ = ι (anPartF φ) := rfl

@[simp]
lemma anPart_negAsymp (φ : (Σ f, 𝓕.AsymptoticLabel f) × (Fin 3 → ℝ)) :
    anPart (FieldOp.inAsymp φ) = 0 := by
  simp [anPart, anPartF]

@[simp]
lemma anPart_position (φ : (Σ f, 𝓕.PositionLabel f) × SpaceTime) :
    anPart (FieldOp.position φ) =
    ofCrAnOp ⟨FieldOp.position φ, CreateAnnihilate.annihilate⟩ := by
  simp [anPart, ofCrAnOp]

@[simp]
lemma anPart_posAsymp (φ : (Σ f, 𝓕.AsymptoticLabel f) × (Fin 3 → ℝ)) :
    anPart (FieldOp.outAsymp φ) = ofCrAnOp ⟨FieldOp.outAsymp φ, ()⟩ := by
  simp [anPart, ofCrAnOp]

/-- For a field specification `𝓕`, and an element `φ` of `𝓕.FieldOp`, the
  creation part of `𝓕.FieldOp` as an element of `𝓕.FieldOpAlgebra`.
  Thus for `φ`
- an incoming asymptotic state this is `ofCrAnOp ⟨φ, ()⟩`.
- a position based state this is `ofCrAnOp ⟨φ, .create⟩`.
- an outgoing asymptotic state this is `0`. -/
def crPart (φ : 𝓕.FieldOp) : 𝓕.FieldOpAlgebra := ι (crPartF φ)

lemma crPart_eq_ι_crPartF (φ : 𝓕.FieldOp) : crPart φ = ι (crPartF φ) := rfl

@[simp]
lemma crPart_negAsymp (φ : (Σ f, 𝓕.AsymptoticLabel f) × (Fin 3 → ℝ)) :
    crPart (FieldOp.inAsymp φ) = ofCrAnOp ⟨FieldOp.inAsymp φ, ()⟩ := by
  simp [crPart, ofCrAnOp]

@[simp]
lemma crPart_position (φ : (Σ f, 𝓕.PositionLabel f) × SpaceTime) :
    crPart (FieldOp.position φ) =
    ofCrAnOp ⟨FieldOp.position φ, CreateAnnihilate.create⟩ := by
  simp [crPart, ofCrAnOp]

@[simp]
lemma crPart_posAsymp (φ : (Σ f, 𝓕.AsymptoticLabel f) × (Fin 3 → ℝ)) :
    crPart (FieldOp.outAsymp φ) = 0 := by
  simp [crPart]

/-- For field specification `𝓕`, and an element `φ` of `𝓕.FieldOp` the following relation holds:

`ofFieldOp φ = crPart φ + anPart φ`

That is, every field operator splits into its creation part plus its annihilation part.
-/
lemma ofFieldOp_eq_crPart_add_anPart (φ : 𝓕.FieldOp) :
    ofFieldOp φ = crPart φ + anPart φ := by
  rw [ofFieldOp, crPart, anPart, ofFieldOpF_eq_crPartF_add_anPartF]
  simp only [map_add]

end FieldOpAlgebra
end FieldSpecification
