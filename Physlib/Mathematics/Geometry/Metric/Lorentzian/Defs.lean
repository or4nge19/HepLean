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

* `PseudoRiemannianMetric.IsLorentzianMetric`: the Prop-valued predicate asserting
  `QuadraticForm.sigNeg (g.toQuadraticForm x) = 1` for all `x`.

## Tags

Lorentzian, pseudo-Riemannian, index
-/

namespace PseudoRiemannianMetric

noncomputable section

section

variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type w} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners ℝ E H} {n : WithTop ℕ∞}
variable [IsManifold I (n + 1) M]
variable [∀ x : M, FiniteDimensional ℝ (TangentSpace I x)]

/-- Predicate asserting that a pseudo-Riemannian metric has index `1` at every point. -/
class IsLorentzianMetric (g : _root_.PseudoRiemannianMetric E H M n I) : Prop where
  sigNeg_eq_one : ∀ x : M, sigNeg (g.toQuadraticForm x) = 1

namespace IsLorentzianMetric

variable (g : _root_.PseudoRiemannianMetric E H M n I)

/-- For a Lorentzian metric, the index is `1` at every point. -/
lemma index_eq_one (x : M) [IsLorentzianMetric (g := g)] :
    g.index x = 1 := by
  simpa [_root_.PseudoRiemannianMetric.index] using
    (IsLorentzianMetric.sigNeg_eq_one (g := g) x)

end IsLorentzianMetric

end

end

end PseudoRiemannianMetric
