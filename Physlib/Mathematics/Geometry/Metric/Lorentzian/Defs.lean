/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

import all Physlib.Mathematics.Geometry.Metric.PseudoRiemannian.Defs
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.LinearAlgebra.QuadraticForm.Signature

/-!
# Lorentzian metrics

This file records the Lorentzian condition (index `1`) for a pseudo-Riemannian metric.

## Main definitions

p0* `PseudoRiemannianMetric.IsLorentzianMetric`: the Prop-valued predicate asserting that a
  pseudo-Riemannian metric has index `1` at every point.

## Tags

Lorentzian, pseudo-Riemannian, index
-/

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
  index_eq_one : ∀ x : M, sigNeg (g.toQuadraticForm x) = 1

attribute [simp] IsLorentzianMetric.index_eq_one

end

end PseudoRiemannianMetric
