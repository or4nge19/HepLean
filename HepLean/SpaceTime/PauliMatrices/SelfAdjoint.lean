/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Mathematics.PiTensorProduct
import Mathlib.RepresentationTheory.Rep
import HepLean.Tensors.Basic
import Mathlib.Logic.Equiv.TransferInstance
import HepLean.SpaceTime.LorentzGroup.Basic
import HepLean.SpaceTime.PauliMatrices.Basic
import LLMLean
/-!

## Interaction of Pauli matrices with self-adjoint matrices

-/
namespace PauliMatrix
open Matrix

lemma selfAdjoint_trace_σ0_real (A : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)) :
    (Matrix.trace (σ0 * A.1)).re = Matrix.trace (σ0 * A.1) := by
  rw [eta_fin_two A.1]
  simp only [σ0, Fin.isValue, cons_mul, Nat.succ_eq_add_one, Nat.reduceAdd, vecMul_cons, head_cons,
    one_smul, tail_cons, zero_smul, empty_vecMul, add_zero, zero_add, empty_mul,
    Equiv.symm_apply_apply, trace_fin_two_of, Complex.add_re, Complex.ofReal_add]
  have hA : IsSelfAdjoint A.1 := A.2
  rw [isSelfAdjoint_iff, star_eq_conjTranspose] at hA
  rw [eta_fin_two (A.1)ᴴ] at hA
  simp only [Fin.isValue, conjTranspose_apply, RCLike.star_def, of_apply, cons_val', cons_val_zero,
    empty_val', cons_val_fin_one, cons_val_one, head_cons, head_fin_const] at hA
  have h00 := congrArg (fun f => f 0 0) hA
  simp only [Fin.isValue, of_apply, cons_val', cons_val_zero, empty_val', cons_val_fin_one] at h00
  have hA00 : A.1 0 0 = (A.1 0 0).re := by
    exact Eq.symm ((fun {z} => Complex.conj_eq_iff_re.mp) h00)
  rw [hA00]
  simp
  have h11 := congrArg (fun f => f 1 1) hA
  simp only [Fin.isValue, of_apply, cons_val', cons_val_one, head_cons, empty_val',
    cons_val_fin_one, head_fin_const] at h11
  exact Complex.conj_eq_iff_re.mp h11

lemma selfAdjoint_trace_σ1_real (A : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)) :
    (Matrix.trace (σ1 * A.1)).re = Matrix.trace (σ1 * A.1) := by
  rw [eta_fin_two A.1]
  simp only [σ1, Fin.isValue, cons_mul, Nat.succ_eq_add_one, Nat.reduceAdd, vecMul_cons, head_cons,
    one_smul, tail_cons, zero_smul, empty_vecMul, add_zero, zero_add, empty_mul,
    Equiv.symm_apply_apply, trace_fin_two_of, Complex.add_re, Complex.ofReal_add]
  have hA : IsSelfAdjoint A.1 := A.2
  rw [isSelfAdjoint_iff, star_eq_conjTranspose] at hA
  rw [eta_fin_two (A.1)ᴴ] at hA
  simp at hA
  have h01 := congrArg (fun f => f 0 1) hA
  have h10 := congrArg (fun f => f 1 0) hA
  simp at h01 h10
  rw [← h01]
  simp
  rw [Complex.add_conj]
  simp
  ring

lemma selfAdjoint_trace_σ2_real (A : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)) :
    (Matrix.trace (σ2 * A.1)).re = Matrix.trace (σ2 * A.1) := by
  rw [eta_fin_two A.1]
  simp only [σ2, Fin.isValue, cons_mul, Nat.succ_eq_add_one, Nat.reduceAdd, vecMul_cons, head_cons,
    one_smul, tail_cons, zero_smul, empty_vecMul, add_zero, zero_add, empty_mul,
    Equiv.symm_apply_apply, trace_fin_two_of, Complex.add_re, Complex.ofReal_add]
  have hA : IsSelfAdjoint A.1 := A.2
  rw [isSelfAdjoint_iff, star_eq_conjTranspose, eta_fin_two (A.1)ᴴ] at hA
  simp at hA
  have h01 := congrArg (fun f => f 0 1) hA
  have h10 := congrArg (fun f => f 1 0) hA
  simp at h01 h10
  rw [← h10]
  simp
  trans Complex.I * (A.1 0 1 - (starRingEnd ℂ) (A.1 0 1))
  · rw [Complex.sub_conj ]
    ring_nf
    simp
  · ring

lemma selfAdjoint_trace_σ3_real (A : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)) :
    (Matrix.trace (σ3 * A.1)).re = Matrix.trace (σ3 * A.1) := by
  rw [eta_fin_two A.1]
  simp only [σ3, Fin.isValue, cons_mul, Nat.succ_eq_add_one, Nat.reduceAdd, vecMul_cons, head_cons,
    one_smul, tail_cons, zero_smul, empty_vecMul, add_zero, zero_add, empty_mul,
    Equiv.symm_apply_apply, trace_fin_two_of, Complex.add_re, Complex.ofReal_add]
  have hA : IsSelfAdjoint A.1 := A.2
  rw [isSelfAdjoint_iff, star_eq_conjTranspose, eta_fin_two (A.1)ᴴ] at hA
  simp at hA
  have h00 := congrArg (fun f => f 0 0) hA
  have h11 := congrArg (fun f => f 1 1) hA
  have hA00 : A.1 0 0 = (A.1 0 0).re := Eq.symm ((fun {z} => Complex.conj_eq_iff_re.mp) h00)
  have hA11 : A.1 1 1 = (A.1 1 1).re := Eq.symm ((fun {z} => Complex.conj_eq_iff_re.mp) h11)
  simp
  rw [hA00, hA11]
  simp


open Complex

lemma selfAdjoint_ext_complex {A B : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)}
    (h0 : ((Matrix.trace (PauliMatrix.σ0 * A.1)) = (Matrix.trace (PauliMatrix.σ0 * B.1))))
    (h1 : Matrix.trace (PauliMatrix.σ1 * A.1) = Matrix.trace (PauliMatrix.σ1 * B.1))
    (h2 : Matrix.trace (PauliMatrix.σ2 * A.1) = Matrix.trace (PauliMatrix.σ2 * B.1))
    (h3 : Matrix.trace (PauliMatrix.σ3 * A.1) = Matrix.trace (PauliMatrix.σ3 * B.1)) : A = B := by
  ext i j
  rw [eta_fin_two A.1, eta_fin_two B.1] at h0 h1 h2 h3
  simp only [PauliMatrix.σ0, Fin.isValue, cons_mul, Nat.succ_eq_add_one, Nat.reduceAdd, vecMul_cons,
    head_cons, one_smul, tail_cons, zero_smul, empty_vecMul, add_zero, zero_add, empty_mul,
    Equiv.symm_apply_apply, trace_fin_two_of] at h0
  simp [PauliMatrix.σ1] at h1
  simp [PauliMatrix.σ2] at h2
  simp [PauliMatrix.σ3] at h3
  match i, j with
  | 0, 0 =>
    linear_combination (norm := ring_nf)  (h0 + h3) / 2
  | 0, 1 =>
    linear_combination (norm := ring_nf)  (h1 - I * h2) / 2
    simp
  | 1, 0 =>
    linear_combination (norm := ring_nf)  (h1 + I * h2) / 2
    simp
  | 1, 1 =>
    linear_combination (norm := ring_nf)  (h0 - h3) / 2

lemma selfAdjoint_ext {A B : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)}
    (h0 : ((Matrix.trace (PauliMatrix.σ0 * A.1))).re = ((Matrix.trace (PauliMatrix.σ0 * B.1))).re)
    (h1 : ((Matrix.trace (PauliMatrix.σ1 * A.1))).re = ((Matrix.trace (PauliMatrix.σ1 * B.1))).re)
    (h2 : ((Matrix.trace (PauliMatrix.σ2 * A.1))).re = ((Matrix.trace (PauliMatrix.σ2 * B.1))).re)
    (h3 : ((Matrix.trace (PauliMatrix.σ3 * A.1))).re = ((Matrix.trace (PauliMatrix.σ3 * B.1))).re) :
    A = B := by
  have h0' := congrArg ofReal h0
  have h1' := congrArg ofReal h1
  have h2' := congrArg ofReal h2
  have h3' := congrArg ofReal h3
  rw [ofReal_eq_coe, ofReal_eq_coe] at h0' h1' h2' h3'
  rw [selfAdjoint_trace_σ0_real A, selfAdjoint_trace_σ0_real B] at h0'
  rw [selfAdjoint_trace_σ1_real A, selfAdjoint_trace_σ1_real B] at h1'
  rw [selfAdjoint_trace_σ2_real A, selfAdjoint_trace_σ2_real B] at h2'
  rw [selfAdjoint_trace_σ3_real A, selfAdjoint_trace_σ3_real B] at h3'
  exact selfAdjoint_ext_complex h0' h1' h2' h3'

noncomputable section

def σSA' (i : Fin 1 ⊕ Fin 3) : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ) :=
  match i with
  | Sum.inl 0 => ⟨σ0, σ0_selfAdjoint⟩
  | Sum.inr 0 => ⟨σ1, σ1_selfAdjoint⟩
  | Sum.inr 1 => ⟨σ2, σ2_selfAdjoint⟩
  | Sum.inr 2 => ⟨σ3, σ3_selfAdjoint⟩


lemma σSA_linearly_independent : LinearIndependent ℝ σSA' := by
  apply Fintype.linearIndependent_iff.mpr
  intro g hg
  simp at hg
  rw [Fin.sum_univ_three] at hg
  simp [σSA'] at hg
  intro i
  match i with
  | Sum.inl 0 =>
    simpa [mul_sub, mul_add] using congrArg (fun A => (Matrix.trace (PauliMatrix.σ0 * A.1))) hg
  | Sum.inr 0 =>
    simpa [mul_sub, mul_add] using congrArg (fun A => (Matrix.trace (PauliMatrix.σ1 * A.1))) hg
  | Sum.inr 1 =>
    simpa [mul_sub, mul_add] using congrArg (fun A => (Matrix.trace (PauliMatrix.σ2 * A.1))) hg
  | Sum.inr 2 =>
    simpa [mul_sub, mul_add] using congrArg (fun A => (Matrix.trace (PauliMatrix.σ3 * A.1))) hg

lemma σSA_span : ⊤ ≤ Submodule.span ℝ (Set.range σSA') := by
  refine (top_le_span_range_iff_forall_exists_fun ℝ).mpr ?_
  intro A
  let c : Fin 1 ⊕ Fin 3 → ℝ := fun i =>
    match i with
    | Sum.inl 0 => 1/2 * (Matrix.trace (σ0 * A.1)).re
    | Sum.inr 0 => 1/2 * (Matrix.trace (σ1 * A.1)).re
    | Sum.inr 1 => 1/2 * (Matrix.trace (σ2 * A.1)).re
    | Sum.inr 2 => 1/2 * (Matrix.trace (σ3 * A.1)).re
  use c
  simp [Fin.sum_univ_three, c]
  apply selfAdjoint_ext
  · simp [mul_add, σSA']
    ring
  · simp [mul_add, σSA']
    ring
  · simp [mul_add, σSA']
    ring
  · simp [mul_add, σSA']
    ring

def σSA : Basis (Fin 1 ⊕ Fin 3) ℝ (selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)) :=
  Basis.mk σSA_linearly_independent σSA_span

def σSAL' (i : Fin 1 ⊕ Fin 3) : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ) :=
  match i with
  | Sum.inl 0 => ⟨σ0, σ0_selfAdjoint⟩
  | Sum.inr 0 => ⟨-σ1, by rw [neg_mem_iff]; exact σ1_selfAdjoint⟩
  | Sum.inr 1 => ⟨-σ2,  by rw [neg_mem_iff]; exact σ2_selfAdjoint⟩
  | Sum.inr 2 => ⟨-σ3, by rw [neg_mem_iff]; exact σ3_selfAdjoint⟩


lemma σSAL_linearly_independent : LinearIndependent ℝ σSAL' := by
  apply Fintype.linearIndependent_iff.mpr
  intro g hg
  simp at hg
  rw [Fin.sum_univ_three] at hg
  simp [σSAL'] at hg
  intro i
  match i with
  | Sum.inl 0 =>
    simpa [mul_sub, mul_add] using congrArg (fun A => (Matrix.trace (PauliMatrix.σ0 * A.1))) hg
  | Sum.inr 0 =>
    simpa [mul_sub, mul_add] using congrArg (fun A => (Matrix.trace (PauliMatrix.σ1 * A.1))) hg
  | Sum.inr 1 =>
    simpa [mul_sub, mul_add] using congrArg (fun A => (Matrix.trace (PauliMatrix.σ2 * A.1))) hg
  | Sum.inr 2 =>
    simpa [mul_sub, mul_add] using congrArg (fun A => (Matrix.trace (PauliMatrix.σ3 * A.1))) hg

lemma σSAL_span : ⊤ ≤ Submodule.span ℝ (Set.range σSAL') := by
  refine (top_le_span_range_iff_forall_exists_fun ℝ).mpr ?_
  intro A
  let c : Fin 1 ⊕ Fin 3 → ℝ := fun i =>
    match i with
    | Sum.inl 0 => 1/2 * (Matrix.trace (σ0 * A.1)).re
    | Sum.inr 0 => - 1/2 * (Matrix.trace (σ1 * A.1)).re
    | Sum.inr 1 => - 1/2 * (Matrix.trace (σ2 * A.1)).re
    | Sum.inr 2 => - 1/2 * (Matrix.trace (σ3 * A.1)).re
  use c
  simp [Fin.sum_univ_three, c]
  apply selfAdjoint_ext
  · simp [mul_add, σSAL']
    ring
  · simp [mul_add, σSAL']
    ring
  · simp [mul_add, σSAL']
    ring
  · simp [mul_add, σSAL']
    ring

def σSAL : Basis (Fin 1 ⊕ Fin 3) ℝ (selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)) :=
  Basis.mk σSAL_linearly_independent σSAL_span

lemma σSAL_decomp (M : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)) :
    M = (1/2 * (Matrix.trace (σ0 * M.1)).re) • σSAL (Sum.inl 0)
    + (-1/2 * (Matrix.trace (σ1 * M.1)).re) • σSAL (Sum.inr 0)
    + (-1/2 * (Matrix.trace (σ2 * M.1)).re) • σSAL (Sum.inr 1)
    + (-1/2 * (Matrix.trace (σ3 * M.1)).re) • σSAL (Sum.inr 2) := by
  apply selfAdjoint_ext
  · simp [σSAL, mul_add, σSAL']
    ring
  · simp [σSAL, mul_add, σSAL']
    ring
  · simp [σSAL, mul_add, σSAL']
    ring
  · simp [σSAL, mul_add, σSAL']
    ring

@[simp]
lemma σSAL_repr_inl_0 (M : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)) :
    σSAL.repr M (Sum.inl 0) = 1 / 2 * Matrix.trace (σ0 * M.1) := by
  have hM : M = ∑ i, σSAL.repr M i • σSAL i := (Basis.sum_repr σSAL M).symm
  simp [Fin.sum_univ_three] at hM
  have h0 := congrArg (fun A => Matrix.trace (σ0 * A.1)/ 2) hM
  simp [σSAL, σSAL', mul_add] at h0
  linear_combination (norm := ring_nf) -h0
  simp [σSAL]

@[simp]
lemma σSAL_repr_inr_0 (M : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)) :
    σSAL.repr M (Sum.inr 0) = - 1 / 2 * Matrix.trace (σ1 * M.1) := by
  have hM : M = ∑ i, σSAL.repr M i • σSAL i := (Basis.sum_repr σSAL M).symm
  simp [Fin.sum_univ_three] at hM
  have h0 := congrArg (fun A => - Matrix.trace (σ1 * A.1)/ 2) hM
  simp [σSAL, σSAL', mul_add] at h0
  linear_combination (norm := ring_nf) -h0
  simp [σSAL]

@[simp]
lemma σSAL_repr_inr_1 (M : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)) :
    σSAL.repr M (Sum.inr 1) = - 1 / 2 * Matrix.trace (σ2 * M.1) := by
  have hM : M = ∑ i, σSAL.repr M i • σSAL i := (Basis.sum_repr σSAL M).symm
  simp [Fin.sum_univ_three] at hM
  have h0 := congrArg (fun A => - Matrix.trace (σ2 * A.1)/ 2) hM
  simp [σSAL, σSAL', mul_add] at h0
  linear_combination (norm := ring_nf) -h0
  simp [σSAL]

@[simp]
lemma σSAL_repr_inr_2 (M : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)) :
    σSAL.repr M (Sum.inr 2) = - 1 / 2 * Matrix.trace (σ3 * M.1) := by
  have hM : M = ∑ i, σSAL.repr M i • σSAL i := (Basis.sum_repr σSAL M).symm
  simp [Fin.sum_univ_three] at hM
  have h0 := congrArg (fun A => - Matrix.trace (σ3 * A.1)/ 2) hM
  simp [σSAL, σSAL', mul_add] at h0
  linear_combination (norm := ring_nf) -h0
  simp [σSAL]

lemma σSA_minkowskiMetric_σSAL (i : Fin 1 ⊕ Fin 3) :
    (σSA i) = minkowskiMatrix i i • (σSAL i) := by
  match i with
  | Sum.inl 0 =>
    simp [σSA, σSAL, σSA', σSAL', minkowskiMatrix.inl_0_inl_0]
  | Sum.inr 0 =>
    simp [σSA, σSAL, σSA', σSAL', minkowskiMatrix.inr_i_inr_i]
    cases i with
    | inl val =>
      ext i j : 2
      simp_all only [NegMemClass.coe_neg, neg_apply, neg_neg]
    | inr val_1 =>
      ext i j : 2
      simp_all only [NegMemClass.coe_neg, neg_apply, neg_neg]
  | Sum.inr 1 =>
    simp [σSA, σSAL, σSA', σSAL', minkowskiMatrix.inr_i_inr_i]
    cases i with
    | inl val =>
      ext i j : 2
      simp_all only [NegMemClass.coe_neg, neg_apply, neg_neg]
    | inr val_1 =>
      ext i j : 2
      simp_all only [NegMemClass.coe_neg, neg_apply, neg_neg]
  | Sum.inr 2 =>
    simp [σSA, σSAL, σSA', σSAL', minkowskiMatrix.inr_i_inr_i]
    cases i with
    | inl val =>
      ext i j : 2
      simp_all only [NegMemClass.coe_neg, neg_apply, neg_neg]
    | inr val_1 =>
      ext i j : 2
      simp_all only [NegMemClass.coe_neg, neg_apply, neg_neg]


end
end PauliMatrix
