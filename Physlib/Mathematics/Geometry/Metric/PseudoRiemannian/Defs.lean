/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Physlib.Mathematics.Geometry.Metric.PseudoRiemannian.Basic
public import Physlib.Mathematics.Geometry.Metric.PseudoRiemannian.MetricTensorCotangent

/-!
# Pseudo-Riemannian metrics (manifold structure)

This file defines the `PseudoRiemannianMetric` structure and its API, building on
`Physlib/Mathematics/Geometry/Metric/PseudoRiemannian/Basic.lean` (bundle-level setup and
`MetricTensor` through the musical isomorphisms) and
`Physlib/Mathematics/Geometry/Metric/PseudoRiemannian/MetricTensorCotangent.lean` (induced cotangent
metric and `MetricTensor.index`).

A pseudo-Riemannian metric is a smoothly varying symmetric nondegenerate bilinear form on each
tangent space, whose index (negative inertia) is locally constant. The index is formalized using
`QuadraticForm.sigNeg`. In finite dimension, a metric induces the usual musical isomorphisms
(`flat`/`sharp`) and an induced metric on the cotangent spaces.

## Main definitions (this file)

* `PseudoRiemannianMetric E H M n I`: a `MetricTensor` whose pointwise index is locally constant.

Earlier files in the same folder provide `Bundle` pseudo-Riemannian infrastructure, the
`MetricTensor` core, and cotangent/index material for `MetricTensor`.

## Implementation notes

Smoothness is stated as a `ContMDiff` assumption for a bundled map `x ↦ TotalSpace.mk' … x (gₓ)` as
in Mathlib. Index-type constructions use `QuadraticForm.sigNeg` and therefore require
finite-dimensional tangent spaces. For now, local constancy of the index is packaged as part of the
definition of `PseudoRiemannianMetric`; deriving it from smooth nondegenerate variation would
require additional topological linear algebra about continuous families of symmetric bilinear forms.

If the fibers already carry a topology (e.g. the tangent bundle), we register the fiberwise metric
through `Bundle.PseudoRiemannianBundle` to avoid introducing diamonds in typeclass inference, in the
same spirit as Mathlib's `Bundle.RiemannianBundle`.

## Tags

pseudo-Riemannian, metric tensor, musical isomorphisms, index

## References

* Barrett O'Neill, *Semi-Riemannian Geometry with Applications to Relativity*, Academic
Press (1983).
-/

@[expose] public section

section PseudoRiemannianMetric

open Bundle Set Finset Function Filter Module Topology ContinuousLinearMap
open scoped Manifold Bundle LinearMap Dual

/-- A `C^n` pseudo-Riemannian metric on a manifold.

This is a smooth symmetric nondegenerate bilinear form on each tangent space whose index
(`QuadraticForm.sigNeg`) is locally constant (O'Neill, *Semi-Riemannian Geometry* (1983),
Definition 3.1). -/
@[ext]
structure PseudoRiemannianMetric
    (E : Type v) (H : Type w) (M : Type*) (n : WithTop ℕ∞)
    [inst_norm_grp_E : NormedAddCommGroup E]
    [inst_norm_sp_E : NormedSpace ℝ E]
    [inst_top_H : TopologicalSpace H]
    [inst_top_M : TopologicalSpace M]
    [inst_chart_M : ChartedSpace H M]
    (I : ModelWithCorners ℝ E H)
    [inst_mani : IsManifold I (n + 1) M]
    [inst_tangent_findim : ∀ (x : M), FiniteDimensional ℝ (TangentSpace I x)] :
      Type _ extends toMetricTensor : MetricTensor E H M n I where
  /-- The negative index (`QuadraticForm.sigNeg`) of the metric's quadratic form is
      locally constant. On a connected manifold, this implies it is constant globally.

      TODO: mathematically, this should be derivable from smooth nondegenerate variation of the
      metric tensor. We currently keep it as data until the requisite topological linear algebra
      lemmas are available. -/
  sigNeg_isLocallyConstant :
    IsLocallyConstant (fun x : M =>
      have : FiniteDimensional ℝ (TangentSpace I x) := inferInstance
      sigNeg (PseudoRiemannianMetric.valToQuadraticForm val symm x))

namespace PseudoRiemannianMetric

variable {E : Type v} {H : Type w} {M : Type*} {n : WithTop ℕ∞}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners ℝ E H}
variable [IsManifold I (n + 1) M]
variable [inst_tangent_findim : ∀ (x : M), FiniteDimensional ℝ (TangentSpace I x)]

/-- Given a pseudo-Riemannian metric `g` on manifold `M` and a point `x : M`,
this function constructs a bilinear form on the tangent space at `x`.
For tangent vectors `u v : T_x M`, the bilinear form is given by:
`g_x(u, v) = g(x)(u, v)` -/
noncomputable abbrev toBilinForm (g : PseudoRiemannianMetric E H M n I) (x : M) :
    LinearMap.BilinForm ℝ (TangentSpace I x) :=
  MetricTensor.toBilinForm (g := g.toMetricTensor) x

/-- Convert a pseudo-Riemannian metric at a point `x` to a quadratic form `v ↦ gₓ(v, v)`. -/
noncomputable abbrev toQuadraticForm (g : PseudoRiemannianMetric E H M n I) (x : M) :
    QuadraticForm ℝ (TangentSpace I x) :=
  MetricTensor.toQuadraticForm (g := g.toMetricTensor) x

/-- Coercion from PseudoRiemannianMetric to its function representation. -/
instance coeFunInst : CoeFun (PseudoRiemannianMetric E H M n I)
    (fun _ => ∀ x : M, TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ)) where
  coe g := g.val

@[simp]
lemma toBilinForm_apply (g : PseudoRiemannianMetric E H M n I) (x : M)
    (v w : TangentSpace I x) : toBilinForm g x v w = g.val x v w :=
  rfl

@[simp]
lemma toQuadraticForm_apply (g : PseudoRiemannianMetric E H M n I) (x : M)
    (v : TangentSpace I x) : toQuadraticForm g x v = g.val x v v :=
  rfl

/-! ## Index (negative inertia) -/

/-- The (negative) index of a pseudo-Riemannian metric at a point, defined as the negative index of
the associated quadratic form `v ↦ gₓ(v,v)`. -/
noncomputable def index (g : PseudoRiemannianMetric E H M n I) (x : M) : ℕ :=
  sigNeg (g.toQuadraticForm x)

@[simp]
lemma index_def (g : PseudoRiemannianMetric E H M n I) (x : M) :
    g.index x = sigNeg (g.toQuadraticForm x) :=
  rfl

lemma index_isLocallyConstant (g : PseudoRiemannianMetric E H M n I) :
    IsLocallyConstant (fun x : M => g.index x) :=
  g.sigNeg_isLocallyConstant

lemma index_eq_of_isPreconnected (g : PseudoRiemannianMetric E H M n I) {s : Set M}
    (hs : IsPreconnected s) {x y : M} (hx : x ∈ s) (hy : y ∈ s) : g.index x = g.index y :=
  (index_isLocallyConstant (g := g)).apply_eq_of_isPreconnected hs hx hy

lemma index_eq_of_preconnectedSpace [PreconnectedSpace M] (g : PseudoRiemannianMetric E H M n I)
    (x y : M) : g.index x = g.index y :=
  (index_isLocallyConstant (g := g)).apply_eq_of_preconnectedSpace x y

lemma index_eq_of_mem_connectedComponent (g : PseudoRiemannianMetric E H M n I) (x y : M)
    (hy : y ∈ connectedComponent x) : g.index y = g.index x :=
  (index_isLocallyConstant (g := g)).apply_eq_of_isPreconnected
    (isConnected_connectedComponent.isPreconnected)
    hy (mem_connectedComponent : x ∈ connectedComponent x)

lemma toBilinForm_isSymm (g : PseudoRiemannianMetric E H M n I) (x : M) :
    (toBilinForm g x).IsSymm := by
  simp [toBilinForm]

lemma toBilinForm_nondegenerate (g : PseudoRiemannianMetric E H M n I) (x : M) :
    (toBilinForm g x).Nondegenerate := by
  simp [toBilinForm]

/-- The fiberwise pairing \(g_x(v,w)\) of a pseudo-Riemannian metric. -/
noncomputable abbrev inner (g : PseudoRiemannianMetric E H M n I) (x : M) (v w : TangentSpace I x) :
    ℝ :=
  MetricTensor.inner (g := g.toMetricTensor) x v w

@[simp] lemma inner_apply (g : PseudoRiemannianMetric E H M n I) (x : M) (v w : TangentSpace I x) :
    inner g x v w = g.val x v w := rfl

/-! ### Smoothness of the pairing `g(v,w)` -/

section PairingSmoothness

variable [IsManifold I 1 M]

variable
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace HM M']
  {b : M' → M} {v w : ∀ x, TangentSpace I (b x)} {s : Set M'} {x : M'}

lemma ContMDiffWithinAt.inner
    (g : PseudoRiemannianMetric E H M n I)
    (hv : ContMDiffWithinAt IM (I.prod 𝓘(ℝ, E)) n
      (fun m ↦ (v m : TotalSpace E fun y : M ↦ TangentSpace I y)) s x)
    (hw : ContMDiffWithinAt IM (I.prod 𝓘(ℝ, E)) n
      (fun m ↦ (w m : TotalSpace E fun y : M ↦ TangentSpace I y)) s x) :
    ContMDiffWithinAt IM 𝓘(ℝ) n (fun m ↦ g.inner (b m) (v m) (w m)) s x := by
  simpa [PseudoRiemannianMetric.inner] using
    (MetricTensor.ContMDiffWithinAt.inner (g := g.toMetricTensor) (b := b) (v := v) (w := w)
      (s := s) (x := x) hv hw)

lemma ContMDiffAt.inner
    (g : PseudoRiemannianMetric E H M n I)
    (hv : ContMDiffAt IM (I.prod 𝓘(ℝ, E)) n
      (fun m ↦ (v m : TotalSpace E fun y : M ↦ TangentSpace I y)) x)
    (hw : ContMDiffAt IM (I.prod 𝓘(ℝ, E)) n
      (fun m ↦ (w m : TotalSpace E fun y : M ↦ TangentSpace I y)) x) :
    ContMDiffAt IM 𝓘(ℝ) n (fun m ↦ g.inner (b m) (v m) (w m)) x :=
  ContMDiffWithinAt.inner (g := g) hv hw

lemma ContMDiffOn.inner
    (g : PseudoRiemannianMetric E H M n I)
    (hv : ContMDiffOn IM (I.prod 𝓘(ℝ, E)) n
      (fun m ↦ (v m : TotalSpace E fun y : M ↦ TangentSpace I y)) s)
    (hw : ContMDiffOn IM (I.prod 𝓘(ℝ, E)) n
      (fun m ↦ (w m : TotalSpace E fun y : M ↦ TangentSpace I y)) s) :
    ContMDiffOn IM 𝓘(ℝ) n (fun m ↦ g.inner (b m) (v m) (w m)) s :=
  fun x hx ↦ ContMDiffWithinAt.inner (g := g) (x := x) (hv x hx) (hw x hx)

lemma ContMDiff.inner
    (g : PseudoRiemannianMetric E H M n I)
    (hv : ContMDiff IM (I.prod 𝓘(ℝ, E)) n
      (fun m ↦ (v m : TotalSpace E fun y : M ↦ TangentSpace I y)))
    (hw : ContMDiff IM (I.prod 𝓘(ℝ, E)) n
      (fun m ↦ (w m : TotalSpace E fun y : M ↦ TangentSpace I y))) :
    ContMDiff IM 𝓘(ℝ) n (fun m ↦ g.inner (b m) (v m) (w m)) :=
  fun x ↦ ContMDiffAt.inner (g := g) (x := x) (hv x) (hw x)

end PairingSmoothness

section MDifferentiablePairing

variable
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace HM M']
  {b : M' → M} {v w : ∀ x, TangentSpace I (b x)} {s : Set M'} {x : M'}

lemma MDifferentiableWithinAt.inner
    [IsManifold I 1 M]
    (g : PseudoRiemannianMetric E H M n I)
    (hn : (1 : WithTop ℕ∞) ≤ n)
    (hv : MDifferentiableWithinAt IM (I.prod 𝓘(ℝ, E))
      (fun m ↦ (v m : TotalSpace E fun y : M ↦ TangentSpace I y)) s x)
    (hw : MDifferentiableWithinAt IM (I.prod 𝓘(ℝ, E))
      (fun m ↦ (w m : TotalSpace E fun y : M ↦ TangentSpace I y)) s x) :
    MDifferentiableWithinAt IM 𝓘(ℝ) (fun m ↦ g.inner (b m) (v m) (w m)) s x := by
  simpa [PseudoRiemannianMetric.inner] using
    (MetricTensor.MDifferentiableWithinAt.inner (g.toMetricTensor) (b := b) (v := v) (w := w)
      (s := s) (x := x) hn hv hw)

lemma MDifferentiableAt.inner
    [IsManifold I 1 M]
    (g : PseudoRiemannianMetric E H M n I)
    (hn : (1 : WithTop ℕ∞) ≤ n)
    (hv : MDifferentiableAt IM (I.prod 𝓘(ℝ, E))
      (fun m ↦ (v m : TotalSpace E fun y : M ↦ TangentSpace I y)) x)
    (hw : MDifferentiableAt IM (I.prod 𝓘(ℝ, E))
      (fun m ↦ (w m : TotalSpace E fun y : M ↦ TangentSpace I y)) x) :
    MDifferentiableAt IM 𝓘(ℝ) (fun m ↦ g.inner (b m) (v m) (w m)) x :=
  MDifferentiableWithinAt.inner (g := g) hn hv hw

lemma MDifferentiableOn.inner
    [IsManifold I 1 M]
    (g : PseudoRiemannianMetric E H M n I)
    (hn : (1 : WithTop ℕ∞) ≤ n)
    (hv : MDifferentiableOn IM (I.prod 𝓘(ℝ, E))
      (fun m ↦ (v m : TotalSpace E fun y : M ↦ TangentSpace I y)) s)
    (hw : MDifferentiableOn IM (I.prod 𝓘(ℝ, E))
      (fun m ↦ (w m : TotalSpace E fun y : M ↦ TangentSpace I y)) s) :
    MDifferentiableOn IM 𝓘(ℝ) (fun m ↦ g.inner (b m) (v m) (w m)) s :=
  fun x hx ↦ MDifferentiableWithinAt.inner (g := g) (x := x) hn (hv x hx) (hw x hx)

lemma MDifferentiable.inner
    [IsManifold I 1 M]
    (g : PseudoRiemannianMetric E H M n I)
    (hn : (1 : WithTop ℕ∞) ≤ n)
    (hv : MDifferentiable IM (I.prod 𝓘(ℝ, E))
      (fun m ↦ (v m : TotalSpace E fun y : M ↦ TangentSpace I y)))
    (hw : MDifferentiable IM (I.prod 𝓘(ℝ, E))
      (fun m ↦ (w m : TotalSpace E fun y : M ↦ TangentSpace I y))) :
    MDifferentiable IM 𝓘(ℝ) (fun m ↦ g.inner (b m) (v m) (w m)) :=
  fun x ↦ MDifferentiableAt.inner (g := g) (x := x) hn (hv x) (hw x)

end MDifferentiablePairing

/-! ## Flat / sharp / cotangent API (delegated to `MetricTensor`)

TODO: upgrade the fiberwise bundle equivalence below to a smooth equivalence by proving that
`sharpBundleMap` is smooth. The `flatL` family and the total-space `flatBundleMap` are already
smooth, but the inverse direction still needs a smooth-inverse argument. -/

/-- Index lowering map `v ↦ gₓ(v, -)` as a linear map. -/
abbrev flat (g : PseudoRiemannianMetric E H M n I) (x : M) :
    TangentSpace I x →ₗ[ℝ] (TangentSpace I x →L[ℝ] ℝ) :=
  MetricTensor.flat (g := (g.toMetricTensor : MetricTensor E H M n I)) x

/-- Index lowering map `v ↦ gₓ(v, -)` as a continuous linear map. -/
abbrev flatL (g : PseudoRiemannianMetric E H M n I) (x : M) :
    TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ) :=
  MetricTensor.flatL (g := (g.toMetricTensor : MetricTensor E H M n I)) x

lemma flat_inj (g : PseudoRiemannianMetric E H M n I) (x : M) :
    Function.Injective (flat g x) := by
  simpa [flat] using (MetricTensor.flat_inj (g := (g.toMetricTensor : MetricTensor E H M n I)) x)

lemma flatL_inj (g : PseudoRiemannianMetric E H M n I) (x : M) :
    Function.Injective (flatL g x) := by
  simpa [flatL] using (MetricTensor.flatL_inj (g := (g.toMetricTensor : MetricTensor E H M n I)) x)

/-- Index lowering on the total space of the tangent bundle. -/
noncomputable abbrev flatBundleMap (g : PseudoRiemannianMetric E H M n I) :
    Bundle.TotalSpace E (fun y : M ↦ TangentSpace I y) →
      Bundle.TotalSpace (E →L[ℝ] ℝ) (fun y : M ↦ TangentSpace I y →L[ℝ] ℝ) :=
  MetricTensor.flatBundleMap (g := (g.toMetricTensor : MetricTensor E H M n I))

lemma flatBundleMap_apply (g : PseudoRiemannianMetric E H M n I) (x : M) (v : TangentSpace I x) :
    g.flatBundleMap ⟨x, v⟩ = ⟨x, g.flatL x v⟩ := rfl

/-- The family `x ↦ g.flatL x` is a smooth section of the bundle of continuous linear maps from the
tangent bundle to the cotangent bundle. -/
lemma contMDiff_flatL [IsManifold I 1 M] (g : PseudoRiemannianMetric E H M n I) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) n
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y : M ↦ TangentSpace I y →L[ℝ] (TangentSpace I y →L[ℝ] ℝ))
        x (g.flatL x)) := by
  simpa [flatL] using
    (MetricTensor.contMDiff_flatL (g := (g.toMetricTensor : MetricTensor E H M n I)))

section FlatSmoothness

variable
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace HM M']
  {b : M' → M} {v : ∀ x, TangentSpace I (b x)} {s : Set M'} {x : M'}

lemma ContMDiffWithinAt.flatL
    [IsManifold I 1 M]
    (g : PseudoRiemannianMetric E H M n I)
    (hv : ContMDiffWithinAt IM (I.prod 𝓘(ℝ, E)) n
      (fun m ↦ (v m : TotalSpace E fun y : M ↦ TangentSpace I y)) s x) :
    ContMDiffWithinAt IM (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) n
      (fun m ↦ TotalSpace.mk' (E →L[ℝ] ℝ)
        (E := fun y : M ↦ TangentSpace I y →L[ℝ] ℝ)
        (b m) (g.flatL (b m) (v m))) s x := by
  simpa [PseudoRiemannianMetric.flatL] using
    (MetricTensor.ContMDiffWithinAt.flatL (g := g.toMetricTensor) (b := b) (v := v)
      (s := s) (x := x) hv)

lemma ContMDiffAt.flatL
    [IsManifold I 1 M]
    (g : PseudoRiemannianMetric E H M n I)
    (hv : ContMDiffAt IM (I.prod 𝓘(ℝ, E)) n
      (fun m ↦ (v m : TotalSpace E fun y : M ↦ TangentSpace I y)) x) :
    ContMDiffAt IM (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) n
      (fun m ↦ TotalSpace.mk' (E →L[ℝ] ℝ)
        (E := fun y : M ↦ TangentSpace I y →L[ℝ] ℝ)
        (b m) (g.flatL (b m) (v m))) x :=
  ContMDiffWithinAt.flatL (g := g) hv

lemma ContMDiffOn.flatL
    [IsManifold I 1 M]
    (g : PseudoRiemannianMetric E H M n I)
    (hv : ContMDiffOn IM (I.prod 𝓘(ℝ, E)) n
      (fun m ↦ (v m : TotalSpace E fun y : M ↦ TangentSpace I y)) s) :
    ContMDiffOn IM (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) n
      (fun m ↦ TotalSpace.mk' (E →L[ℝ] ℝ)
        (E := fun y : M ↦ TangentSpace I y →L[ℝ] ℝ)
        (b m) (g.flatL (b m) (v m))) s :=
  fun x hx ↦ ContMDiffWithinAt.flatL (g := g) (hv x hx)

lemma ContMDiff.flatL
    [IsManifold I 1 M]
    (g : PseudoRiemannianMetric E H M n I)
    (hv : ContMDiff IM (I.prod 𝓘(ℝ, E)) n
      (fun m ↦ (v m : TotalSpace E fun y : M ↦ TangentSpace I y))) :
    ContMDiff IM (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) n
      (fun m ↦ TotalSpace.mk' (E →L[ℝ] ℝ)
        (E := fun y : M ↦ TangentSpace I y →L[ℝ] ℝ)
        (b m) (g.flatL (b m) (v m))) :=
  fun x ↦ ContMDiffAt.flatL (g := g) (hv x)

section MDifferentiableFlat

lemma MDifferentiableWithinAt.flatL
    [IsManifold I 1 M]
    (g : PseudoRiemannianMetric E H M n I)
    (hn : (1 : WithTop ℕ∞) ≤ n)
    (hv : MDifferentiableWithinAt IM (I.prod 𝓘(ℝ, E))
      (fun m ↦ (v m : TotalSpace E fun y : M ↦ TangentSpace I y)) s x) :
    MDifferentiableWithinAt IM (I.prod 𝓘(ℝ, E →L[ℝ] ℝ))
      (fun m ↦ TotalSpace.mk' (E →L[ℝ] ℝ)
        (E := fun y : M ↦ TangentSpace I y →L[ℝ] ℝ)
        (b m) (g.flatL (b m) (v m))) s x := by
  simpa [PseudoRiemannianMetric.flatL] using
    (MetricTensor.MDifferentiableWithinAt.flatL (g := g.toMetricTensor) (b := b) (v := v)
      (s := s) (x := x) hn hv)

lemma MDifferentiableAt.flatL
    [IsManifold I 1 M]
    (g : PseudoRiemannianMetric E H M n I)
    (hn : (1 : WithTop ℕ∞) ≤ n)
    (hv : MDifferentiableAt IM (I.prod 𝓘(ℝ, E))
      (fun m ↦ (v m : TotalSpace E fun y : M ↦ TangentSpace I y)) x) :
    MDifferentiableAt IM (I.prod 𝓘(ℝ, E →L[ℝ] ℝ))
      (fun m ↦ TotalSpace.mk' (E →L[ℝ] ℝ)
        (E := fun y : M ↦ TangentSpace I y →L[ℝ] ℝ)
        (b m) (g.flatL (b m) (v m))) x :=
  MDifferentiableWithinAt.flatL (g := g) hn hv

lemma MDifferentiableOn.flatL
    [IsManifold I 1 M]
    (g : PseudoRiemannianMetric E H M n I)
    (hn : (1 : WithTop ℕ∞) ≤ n)
    (hv : MDifferentiableOn IM (I.prod 𝓘(ℝ, E))
      (fun m ↦ (v m : TotalSpace E fun y : M ↦ TangentSpace I y)) s) :
    MDifferentiableOn IM (I.prod 𝓘(ℝ, E →L[ℝ] ℝ))
      (fun m ↦ TotalSpace.mk' (E →L[ℝ] ℝ)
        (E := fun y : M ↦ TangentSpace I y →L[ℝ] ℝ)
        (b m) (g.flatL (b m) (v m))) s :=
  fun x hx ↦ MDifferentiableWithinAt.flatL (g := g) hn (hv x hx)

lemma MDifferentiable.flatL
    [IsManifold I 1 M]
    (g : PseudoRiemannianMetric E H M n I)
    (hn : (1 : WithTop ℕ∞) ≤ n)
    (hv : MDifferentiable IM (I.prod 𝓘(ℝ, E))
      (fun m ↦ (v m : TotalSpace E fun y : M ↦ TangentSpace I y))) :
    MDifferentiable IM (I.prod 𝓘(ℝ, E →L[ℝ] ℝ))
      (fun m ↦ TotalSpace.mk' (E →L[ℝ] ℝ)
        (E := fun y : M ↦ TangentSpace I y →L[ℝ] ℝ)
        (b m) (g.flatL (b m) (v m))) :=
  fun x ↦ MDifferentiableAt.flatL (g := g) hn (hv x)

end MDifferentiableFlat
end FlatSmoothness

/-- Index lowering is smooth on the total space of the tangent bundle. -/
lemma contMDiff_flatBundleMap [IsManifold I 1 M] (g : PseudoRiemannianMetric E H M n I) :
    ContMDiff (I.prod 𝓘(ℝ, E)) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) n g.flatBundleMap := by
  simpa [PseudoRiemannianMetric.flatBundleMap] using
    (MetricTensor.contMDiff_flatBundleMap
      (g := (g.toMetricTensor : MetricTensor E H M n I)))

/-- Index lowering is differentiable on the total space of the tangent bundle. -/
lemma mdifferentiable_flatBundleMap [IsManifold I 1 M]
    (g : PseudoRiemannianMetric E H M n I) (hn : (1 : WithTop ℕ∞) ≤ n) :
    MDifferentiable (I.prod 𝓘(ℝ, E)) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) g.flatBundleMap := by
  simpa [PseudoRiemannianMetric.flatBundleMap] using
    (MetricTensor.mdifferentiable_flatBundleMap
      (g := (g.toMetricTensor : MetricTensor E H M n I)) hn)

lemma flatL_surj (g : PseudoRiemannianMetric E H M n I) (x : M) :
    Function.Surjective (flatL g x) := by
  simpa [flatL] using (MetricTensor.flatL_surj (g := (g.toMetricTensor : MetricTensor E H M n I)) x)

 /-- The `flat` musical equivalence `TₓM ≃ (TₓM)⋆`. -/
noncomputable abbrev flatEquiv (g : PseudoRiemannianMetric E H M n I) (x : M) :
    TangentSpace I x ≃L[ℝ] (TangentSpace I x →L[ℝ] ℝ) :=
  MetricTensor.flatEquiv (g := (g.toMetricTensor : MetricTensor E H M n I)) x

 /-- The `sharp` musical equivalence `(TₓM)⋆ ≃ TₓM`. -/
noncomputable abbrev sharpEquiv (g : PseudoRiemannianMetric E H M n I) (x : M) :
    (TangentSpace I x →L[ℝ] ℝ) ≃L[ℝ] TangentSpace I x :=
  MetricTensor.sharpEquiv (g := (g.toMetricTensor : MetricTensor E H M n I)) x

 /-- Index raising map `ω ↦ sharp ω` as a continuous linear map. -/
noncomputable abbrev sharpL (g : PseudoRiemannianMetric E H M n I) (x : M) :
    (TangentSpace I x →L[ℝ] ℝ) →L[ℝ] TangentSpace I x :=
  MetricTensor.sharpL (g := (g.toMetricTensor : MetricTensor E H M n I)) x

 /-- Index raising map `ω ↦ sharp ω` as a linear map. -/
noncomputable abbrev sharp (g : PseudoRiemannianMetric E H M n I) (x : M) :
    (TangentSpace I x →L[ℝ] ℝ) →ₗ[ℝ] TangentSpace I x :=
  MetricTensor.sharp (g := (g.toMetricTensor : MetricTensor E H M n I)) x

/-- Index raising on the total space of the cotangent bundle. -/
noncomputable abbrev sharpBundleMap (g : PseudoRiemannianMetric E H M n I) :
    Bundle.TotalSpace (E →L[ℝ] ℝ) (fun y : M ↦ TangentSpace I y →L[ℝ] ℝ) →
      Bundle.TotalSpace E (fun y : M ↦ TangentSpace I y) :=
  MetricTensor.sharpBundleMap (g := (g.toMetricTensor : MetricTensor E H M n I))

lemma sharpBundleMap_apply (g : PseudoRiemannianMetric E H M n I) (x : M)
    (ω : TangentSpace I x →L[ℝ] ℝ) :
    g.sharpBundleMap ⟨x, ω⟩ = ⟨x, g.sharpL x ω⟩ := rfl

/-- Fiberwise musical isomorphism between the total spaces of the tangent and cotangent bundles. -/
noncomputable def flatBundleEquiv (g : PseudoRiemannianMetric E H M n I) :
    Bundle.TotalSpace E (fun y : M ↦ TangentSpace I y) ≃
      Bundle.TotalSpace (E →L[ℝ] ℝ) (fun y : M ↦ TangentSpace I y →L[ℝ] ℝ) :=
  MetricTensor.flatBundleEquiv (g := (g.toMetricTensor : MetricTensor E H M n I))

lemma sharpL_apply_flatL (g : PseudoRiemannianMetric E H M n I) (x : M) (v : TangentSpace I x) :
    g.sharpL x (g.flatL x v) = v := by
  simp [sharpL, flatL]

lemma flatL_apply_sharpL (g : PseudoRiemannianMetric E H M n I) (x : M)
    (ω : TangentSpace I x →L[ℝ] ℝ) :
    g.flatL x (g.sharpL x ω) = ω := by
  simp [sharpL, flatL]

lemma flat_sharp_apply (g : PseudoRiemannianMetric E H M n I) (x : M)
    (ω : TangentSpace I x →L[ℝ] ℝ) :
    g.flat x (g.sharp x ω) = ω := by
  simp [flat, sharp]

lemma sharp_flat_apply (g : PseudoRiemannianMetric E H M n I) (x : M) (v : TangentSpace I x) :
    g.sharp x (g.flat x v) = v := by
  simpa [flat, sharp] using
    (MetricTensor.sharp_flat_apply (g := (g.toMetricTensor : MetricTensor E H M n I)) x v)

lemma apply_sharp_sharp (g : PseudoRiemannianMetric E H M n I) (x : M)
    (ω₁ ω₂ : TangentSpace I x →L[ℝ] ℝ) :
    g.val x (g.sharpL x ω₁) (g.sharpL x ω₂) = ω₁ (g.sharpL x ω₂) := by
  simp [sharpL]

lemma apply_vec_sharp (g : PseudoRiemannianMetric E H M n I) (x : M) (v : TangentSpace I x)
    (ω : TangentSpace I x →L[ℝ] ℝ) :
    g.val x v (g.sharpL x ω) = ω v := by
  simpa [sharpL] using
    (MetricTensor.apply_vec_sharp (g := (g.toMetricTensor : MetricTensor E H M n I)) x v ω)

 /-- The induced cotangent metric value `g⁻¹(ω₁, ω₂)`. -/
noncomputable abbrev cotangentMetricVal (g : PseudoRiemannianMetric E H M n I) (x : M)
    (ω₁ ω₂ : TangentSpace I x →L[ℝ] ℝ) : ℝ :=
  MetricTensor.cotangentMetricVal (g := (g.toMetricTensor : MetricTensor E H M n I)) x ω₁ ω₂

 /-- The induced cotangent metric as a bilinear form. -/
noncomputable abbrev cotangentToBilinForm (g : PseudoRiemannianMetric E H M n I) (x : M) :
    LinearMap.BilinForm ℝ (TangentSpace I x →L[ℝ] ℝ) :=
  MetricTensor.cotangentToBilinForm (g := (g.toMetricTensor : MetricTensor E H M n I)) x

 /-- The induced cotangent metric as a quadratic form. -/
noncomputable abbrev cotangentToQuadraticForm (g : PseudoRiemannianMetric E H M n I) (x : M) :
    QuadraticForm ℝ (TangentSpace I x →L[ℝ] ℝ) :=
  MetricTensor.cotangentToQuadraticForm (g := (g.toMetricTensor : MetricTensor E H M n I)) x

theorem cotangentToQuadraticForm_equivalent_toQuadraticForm (g : PseudoRiemannianMetric E H M n I)
    (x : M) :
    (g.cotangentToQuadraticForm x).Equivalent (g.toQuadraticForm x) := by
  simpa [cotangentToQuadraticForm, toQuadraticForm] using
    (MetricTensor.cotangentToQuadraticForm_equivalent_toQuadraticForm
      (g := (g.toMetricTensor : MetricTensor E H M n I)) x)

theorem cotangent_sigNeg_eq (g : PseudoRiemannianMetric E H M n I) (x : M) :
    sigNeg (g.cotangentToQuadraticForm x) =
      sigNeg (g.toQuadraticForm x) := by
  simpa using (cotangentToQuadraticForm_equivalent_toQuadraticForm (g := g) x).sigNeg_eq

end PseudoRiemannianMetric
end PseudoRiemannianMetric
