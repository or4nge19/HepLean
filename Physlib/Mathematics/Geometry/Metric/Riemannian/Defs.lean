/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

import all Physlib.Mathematics.Geometry.Metric.PseudoRiemannian.Defs
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.LinearAlgebra.QuadraticForm.Signature

/-!
# Riemannian metrics (tangent bundle)

This file defines `RiemannianMetric` as the specialization of Mathlib's bundle-level
`Bundle.ContMDiffRiemannianMetric` to the tangent bundle, and provides a coercion to
`PseudoRiemannianMetric` by forgetting positivity.

## Main definitions

* `PseudoRiemannianMetric.RiemannianMetric`: a `C^n` Riemannian metric on `M`.
* `PseudoRiemannianMetric.RiemannianMetric.toPseudoRiemannianMetric`: forget positivity to obtain a
  pseudo-Riemannian metric (index `0`).

## Tags

Riemannian, pseudo-Riemannian
-/

namespace PseudoRiemannianMetric

open Bundle ContinuousLinearMap
open scoped Manifold Bundle

noncomputable section

variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type w} [TopologicalSpace H]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners ℝ E H} {n : WithTop ℕ∞}
variable [IsManifold I (n + 1) M] [IsManifold I 1 M]

private lemma sigNeg_eq_zero_of_posDef
    {F : Type*} [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ F]
    {Q : QuadraticForm ℝ F} (hQ : Q.PosDef) : sigNeg Q = 0 := by
  obtain ⟨W, hW, hWneg⟩ := exists_finrank_eq_sigNeg_and_negDef (Q := Q)
  have hWbot : W = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    by_contra hx0
    have hxW : (⟨x, hx⟩ : W) ≠ 0 := fun h => hx0 (congrArg Subtype.val h)
    have hneg : Q x < 0 := by
      have := hWneg _ hxW
      simpa using neg_pos.mp (by simpa using this)
    exact (not_lt_of_gt (hQ x hx0)) hneg
  have hfin0 : Module.finrank ℝ W = 0 := by simp [hWbot]
  exact hW.symm.trans hfin0

/-- A `C^n` Riemannian metric on `M`. -/
abbrev RiemannianMetric
    (I : ModelWithCorners ℝ E H) (n : WithTop ℕ∞) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] :=
  Bundle.ContMDiffRiemannianMetric (IB := I) (n := n) (F := E) (E := fun x : M ↦ TangentSpace I x)

namespace RiemannianMetric

variable [∀ x : M, FiniteDimensional ℝ (TangentSpace I x)]

/-- Forget the positivity to get a pseudo-Riemannian metric. The index is (locally constantly) `0`.
It makes pseudo-Riemannian API (musical isomorphisms, etc.) usable for a Riemannian metric. -/
def toPseudoRiemannianMetric (g : RiemannianMetric I n M) :
    _root_.PseudoRiemannianMetric E H M n I where
  val := g.inner
  symm := g.symm
  nondegenerate x v hv := by
    by_contra h
    exact (g.pos x v h).ne' (hv v)
  contMDiff := g.contMDiff
  sigNeg_isLocallyConstant :=
    IsLocallyConstant.of_constant _ fun x y => by
      have hx :
          sigNeg (_root_.PseudoRiemannianMetric.valToQuadraticForm g.inner g.symm x) = 0 :=
        sigNeg_eq_zero_of_posDef fun v hv => by
          simpa [_root_.PseudoRiemannianMetric.valToQuadraticForm] using g.pos x v hv
      have hy :
          sigNeg (_root_.PseudoRiemannianMetric.valToQuadraticForm g.inner g.symm y) = 0 :=
        sigNeg_eq_zero_of_posDef fun v hv => by
          simpa [_root_.PseudoRiemannianMetric.valToQuadraticForm] using g.pos y v hv
      rw [hx, hy]

@[simp]
lemma index_toPseudoRiemannianMetric (g : RiemannianMetric I n M) (x : M) :
    g.toPseudoRiemannianMetric.index x = 0 := by
  have hx : sigNeg (_root_.PseudoRiemannianMetric.valToQuadraticForm g.inner g.symm x) = 0 :=
    sigNeg_eq_zero_of_posDef fun v hv => by
      simpa [_root_.PseudoRiemannianMetric.valToQuadraticForm] using g.pos x v hv
  simpa [_root_.PseudoRiemannianMetric.index, _root_.PseudoRiemannianMetric.toQuadraticForm,
    toPseudoRiemannianMetric] using hx

instance : Coe (RiemannianMetric I n M) (_root_.PseudoRiemannianMetric E H M n I) :=
  ⟨toPseudoRiemannianMetric⟩

end RiemannianMetric

/-! ## Existence helper -/

/-- Existence of a Riemannian metric implies existence of a pseudo-Riemannian metric (of index `0`),
by forgetting positivity. -/
theorem nonempty_pseudoRiemannianMetric_of_nonempty_riemannianMetric
    [∀ x : M, FiniteDimensional ℝ (TangentSpace I x)]
    (h : Nonempty (RiemannianMetric I n M)) :
    Nonempty (_root_.PseudoRiemannianMetric E H M n I) :=
  h.map RiemannianMetric.toPseudoRiemannianMetric

end

end PseudoRiemannianMetric
