/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.Algebras.FieldOpAlgebra.NormalOrder
import HepLean.PerturbationTheory.Algebras.FieldOpAlgebra.TimeOrder
/-!

# Time contractions

We define the state algebra of a field structure to be the free algebra
generated by the states.

-/

namespace FieldSpecification
variable {𝓕 : FieldSpecification}
open CrAnAlgebra
noncomputable section

namespace FieldOpAlgebra

open FieldStatistic

/-- The time contraction of two States as an element of `𝓞.A` defined
  as their time ordering in the state algebra minus their normal ordering in the
  creation and annihlation algebra, both mapped to `𝓞.A`.. -/
def timeContract (φ ψ : 𝓕.States) : 𝓕.FieldOpAlgebra :=
    𝓣(ofFieldOp φ * ofFieldOp ψ) - 𝓝(ofFieldOp φ * ofFieldOp ψ)

lemma timeContract_eq_smul (φ ψ : 𝓕.States) : timeContract φ ψ =
    𝓣(ofFieldOp φ * ofFieldOp ψ) + (-1 : ℂ) • 𝓝(ofFieldOp φ * ofFieldOp ψ) := by rfl

lemma timeContract_of_timeOrderRel (φ ψ : 𝓕.States) (h : timeOrderRel φ ψ) :
    timeContract φ ψ = [anPart φ, ofFieldOp ψ]ₛ := by
  conv_rhs =>
    rw [ofFieldOp_eq_crPart_add_anPart]
    rw [map_add, superCommute_anPart_anPart, superCommute_anPart_crPart]
  simp only [timeContract, instCommGroup.eq_1, Algebra.smul_mul_assoc, add_zero]
  rw [timeOrder_ofFieldOp_ofFieldOp_ordered h]
  rw [normalOrder_ofFieldOp_mul_ofFieldOp]
  simp only [instCommGroup.eq_1]
  rw [ofFieldOp_eq_crPart_add_anPart, ofFieldOp_eq_crPart_add_anPart]
  simp only [mul_add, add_mul]
  abel_nf

lemma timeContract_of_not_timeOrderRel (φ ψ : 𝓕.States) (h : ¬ timeOrderRel φ ψ) :
    timeContract φ ψ = 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ ψ) • timeContract ψ φ := by
  rw [timeContract_eq_smul]
  simp only [Int.reduceNeg, one_smul, map_add]
  rw [normalOrder_ofFieldOp_ofFieldOp_swap]
  rw [timeOrder_ofFieldOp_ofFieldOp_not_ordered_eq_timeOrder h]
  rw [timeContract_eq_smul]
  simp only [instCommGroup.eq_1, map_smul, map_add, smul_add]
  rw [smul_smul, smul_smul, mul_comm]

lemma timeContract_mem_center (φ ψ : 𝓕.States) :
    timeContract φ ψ ∈ Subalgebra.center ℂ 𝓕.FieldOpAlgebra := by
  by_cases h : timeOrderRel φ ψ
  · rw [timeContract_of_timeOrderRel _ _ h]
    exact superCommute_anPart_ofFieldOp_mem_center φ ψ
  · rw [timeContract_of_not_timeOrderRel _ _ h]
    refine Subalgebra.smul_mem (Subalgebra.center ℂ _) ?_ 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ ψ)
    rw [timeContract_of_timeOrderRel]
    exact superCommute_anPart_ofFieldOp_mem_center _ _
    have h1 := IsTotal.total (r := 𝓕.timeOrderRel) φ ψ
    simp_all

lemma timeContract_zero_of_diff_grade (φ ψ : 𝓕.States) (h : (𝓕 |>ₛ φ) ≠ (𝓕 |>ₛ ψ)) :
    timeContract φ ψ = 0 := by
  by_cases h1 : timeOrderRel φ ψ
  · rw [timeContract_of_timeOrderRel _ _ h1]
    rw [superCommute_anPart_ofState_diff_grade_zero]
    exact h
  · rw [timeContract_of_not_timeOrderRel _ _ h1]
    rw [timeContract_of_timeOrderRel _ _ _]
    rw [superCommute_anPart_ofState_diff_grade_zero]
    simp only [instCommGroup.eq_1, smul_zero]
    exact h.symm
    have ht := IsTotal.total (r := 𝓕.timeOrderRel) φ ψ
    simp_all

lemma normalOrder_timeContract (φ ψ : 𝓕.States) :
    𝓝(timeContract φ ψ) = 0 := by
  by_cases h : timeOrderRel φ ψ
  · rw [timeContract_of_timeOrderRel _ _ h]
    simp
  · rw [timeContract_of_not_timeOrderRel _ _ h]
    simp
    have h1 : timeOrderRel ψ φ := by
      have ht : timeOrderRel φ ψ ∨ timeOrderRel ψ φ := IsTotal.total (r := 𝓕.timeOrderRel) φ ψ
      simp_all
    rw [timeContract_of_timeOrderRel _ _ h1]
    simp

end FieldOpAlgebra

end
end FieldSpecification
