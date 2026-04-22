/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Physlib.Mathematics.Geometry.Metric.PseudoRiemannian.Defs
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.LinearAlgebra.QuadraticForm.Signature

/-!
# Lorentzian metrics

This file records the Lorentzian condition (index `1`) for a pseudo-Riemannian metric.

We adopt the mathematical, or "mostly plus", convention: a Lorentzian metric has exactly one
negative direction, corresponding to signature `(-, +, ..., +)`. Users working with the physics
"mostly minus" convention should keep in mind that such a metric has negative index `dim - 1`
instead.

## Main definitions

* `PseudoRiemannianMetric.IsLorentzianMetric`: the Prop-valued predicate asserting that a
  pseudo-Riemannian metric has index `1` at every point.

## Tags

Lorentzian, pseudo-Riemannian, index
-/

@[expose] public section

namespace PseudoRiemannianMetric

noncomputable section

variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type w} [TopologicalSpace H]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners ℝ E H} {n : WithTop ℕ∞}
variable [IsManifold I (n + 1) M]
variable [∀ x : M, FiniteDimensional ℝ (TangentSpace I x)]

/-- Predicate asserting that a pseudo-Riemannian metric has index `1` at every point. -/
class IsLorentzianMetric (g : _root_.PseudoRiemannianMetric E H M n I) : Prop where
  /-- A Lorentzian metric has index `1` at every point. -/
  index_eq_one : ∀ x : M, g.index x = 1

@[simp]
lemma sigNeg_toQuadraticForm_eq_one (g : _root_.PseudoRiemannianMetric E H M n I)
    [IsLorentzianMetric (g := g)] (x : M) :
    sigNeg (g.toQuadraticForm x) = 1 := by
  simpa [_root_.PseudoRiemannianMetric.index] using IsLorentzianMetric.index_eq_one (g := g) x

end

end PseudoRiemannianMetric
