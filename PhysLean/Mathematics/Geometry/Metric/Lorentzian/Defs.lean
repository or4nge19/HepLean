/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import PhysLean.Mathematics.Geometry.Metric.PseudoRiemannian.Defs

/-!
# Lorentzian metrics

This file defines Lorentzian metrics as pseudo-Riemannian metrics of index `1` (negative dimension
`1`), in the sense of Sylvester's law of inertia (`QuadraticForm.negDim`).

It provides a reusable definition that composes with the
existing pseudo-Riemannian API (musical isomorphisms, induced bilinear forms, etc.).
-/

namespace PseudoRiemannianMetric

noncomputable section

open scoped Manifold

section

variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type w} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners ℝ E H} {n : WithTop ℕ∞}
variable [IsManifold I (n + 1) M]
variable [∀ x : M, FiniteDimensional ℝ (TangentSpace I x)]

/-- A Lorentzian metric is a pseudo-Riemannian metric whose associated quadratic form has
`negDim = 1` at every point. -/
abbrev LorentzianMetric (E : Type v) (H : Type w) (M : Type w) (n : WithTop ℕ∞)
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners ℝ E H) [IsManifold I (n + 1) M]
    [∀ x : M, FiniteDimensional ℝ (TangentSpace I x)] :=
  PseudoRiemannianMetric E H M n I

/-- Typeclass asserting that a pseudo-Riemannian metric is Lorentzian (index `1`). -/
class IsLorentzianMetric (g : LorentzianMetric (E := E) (H := H) (M := M) (I := I) (n := n)) :
    Prop where
  negDim_eq_one : ∀ x : M, (g.toQuadraticForm x).negDim = 1

namespace LorentzianMetric

variable (g : LorentzianMetric (E := E) (H := H) (M := M) (I := I) (n := n))

@[simp] lemma negDim_eq_one (x : M) [IsLorentzianMetric (g := g)] :
    (g.toQuadraticForm x).negDim = 1 :=
  IsLorentzianMetric.negDim_eq_one (g := g) x

@[simp] lemma index_eq_one (x : M) [IsLorentzianMetric (g := g)] :
    g.index x = 1 := by
  simpa [PseudoRiemannianMetric.index] using
    (IsLorentzianMetric.negDim_eq_one (g := g) x)

end LorentzianMetric

end

end

end PseudoRiemannianMetric
