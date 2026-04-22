/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.QuadraticForm.Signature
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# Pseudo-Riemannian metrics (basic)

`Bundle` API, the `MetricTensor` structure, and musical isomorphisms through `apply_vec_sharp`.
Cotangent metric and `MetricTensor.index` are in `MetricTensorCotangent.lean`; the
`PseudoRiemannianMetric` structure is in `Defs.lean`.
-/

@[expose] public section

section PseudoRiemannianMetric

open Bundle Set Finset Function Filter Module Topology ContinuousLinearMap
open scoped Manifold Bundle LinearMap Dual

/-! ## Bundle-level infrastructure -/

namespace Bundle

/-! ### Fiberwise pseudo-Riemannian structures -/

section PseudoRiemannianBundle

variable
  {B : Type*} [TopologicalSpace B]
  {E : B → Type*} [∀ x, SeminormedAddCommGroup (E x)] [∀ x, NormedSpace ℝ (E x)]

/-- A pseudo-Riemannian structure on a family of fibers `E x`: a symmetric, nondegenerate bilinear
form on each fiber, expressed as a continuous bilinear map. -/
class PseudoRiemannianBundle : Type _ where
  /-- The fiberwise pseudo-inner product as a continuous bilinear map. -/
  metric : ∀ x : B, E x →L[ℝ] E x →L[ℝ] ℝ
  /-- Symmetry: `gₓ(v,w) = gₓ(w,v)`. -/
  symm : ∀ (x : B) (v w : E x), metric x v w = metric x w v
  /-- Nondegeneracy: if `gₓ(v,w)=0` for all `w`, then `v=0`. -/
  nondegenerate : ∀ (x : B) (v : E x), (∀ w : E x, metric x v w = 0) → v = 0

variable [PseudoRiemannianBundle (B := B) (E := E)]

/-- The metric as a family of continuous bilinear maps. -/
abbrev metric (x : B) : E x →L[ℝ] E x →L[ℝ] ℝ :=
  PseudoRiemannianBundle.metric (B := B) (E := E) x

/-- The fiberwise pseudo-inner-product \(g_x(v,w)\). -/
noncomputable abbrev pseudoInner (x : B) (v w : E x) : ℝ :=
  (PseudoRiemannianBundle.metric (B := B) (E := E) x) v w

omit [TopologicalSpace B] in
@[simp]
lemma pseudoInner_def (x : B) (v w : E x) :
    pseudoInner (B := B) (E := E) x v w = metric (B := B) (E := E) x v w :=
  rfl

omit [TopologicalSpace B] in
lemma pseudoInner_symm (x : B) (v w : E x) :
    pseudoInner (B := B) (E := E) x v w = pseudoInner (B := B) (E := E) x w v := by
  simpa [pseudoInner] using (PseudoRiemannianBundle.symm (B := B) (E := E) x v w)

omit [TopologicalSpace B] in
lemma pseudoInner_nondegenerate (x : B) (v : E x) (hv : ∀ w : E x,
    pseudoInner (B := B) (E := E) x v w = 0) :
    v = 0 :=
  PseudoRiemannianBundle.nondegenerate (B := B) (E := E) x v hv

end PseudoRiemannianBundle

/-! ### Smoothness of pseudo-Riemannian structures on vector bundles -/

section ContMDiff

open scoped ENat

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n n' : WithTop ℕ∞}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [∀ x, SeminormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℝ (E x)]
  [FiberBundle F E] [VectorBundle ℝ F E]
  [PseudoRiemannianBundle (B := B) (E := E)]

variable (IB n F E) in
/-- A `C^n` pseudo-Riemannian metric along a vector bundle `E → B`, packaged bundle-first.

This mirrors Mathlib's `Bundle.ContMDiffRiemannianMetric`, but replaces positivity by fiberwise
nondegeneracy. -/
structure ContMDiffPseudoRiemannianMetric : Type _ where
  /-- The fiberwise bilinear form. -/
  metric (b : B) : E b →L[ℝ] E b →L[ℝ] ℝ
  /-- Symmetry: `g_b(v,w) = g_b(w,v)`. -/
  symm (b : B) (v w : E b) : metric b v w = metric b w v
  /-- Nondegeneracy: if `g_b(v, w) = 0` for all `w`, then `v = 0`. -/
  nondegenerate (b : B) (v : E b) (hv : ∀ w : E b, metric b v w = 0) : v = 0
  /-- Smoothness as a section of the bundle of bilinear forms. -/
  contMDiff :
    ContMDiff IB (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun b ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) b (metric b))

variable (IB n F E) in
/-- Prop-valued smoothness predicate for a pseudo-Riemannian bundle.

This is stated as an existence statement (as in Mathlib's `IsContinuousRiemannianBundle`), so it is
Prop-valued in terms of existing bundle data. -/
class IsContMDiffPseudoRiemannianBundle : Prop where
  exists_contMDiff :
    ∃ g : ContMDiffPseudoRiemannianMetric (IB := IB) (n := n) (F := F) (E := E),
      ∀ (b : B) (v w : E b), pseudoInner (B := B) (E := E) b v w = g.metric b v w

lemma IsContMDiffPseudoRiemannianBundle.of_le
    [h : IsContMDiffPseudoRiemannianBundle (IB := IB) (n := n) (F := F) (E := E)] (h' : n' ≤ n) :
    IsContMDiffPseudoRiemannianBundle (IB := IB) (n := n') (F := F) (E := E) := by
  rcases h.exists_contMDiff with ⟨g, hg⟩
  refine ⟨⟨?_, ?_⟩⟩
  · refine
      { metric := g.metric
        symm := g.symm
        nondegenerate := g.nondegenerate
        contMDiff := g.contMDiff.of_le h' }
  · intro b v w
    simpa using hg b v w

instance [IsContMDiffPseudoRiemannianBundle (IB := IB) (n := (1 : WithTop ℕ∞)) (F := F) (E := E)] :
    IsContMDiffPseudoRiemannianBundle (IB := IB) (n := (0 : WithTop ℕ∞)) (F := F) (E := E) :=
  IsContMDiffPseudoRiemannianBundle.of_le (IB := IB) (F := F) (E := E) zero_le_one

instance [IsContMDiffPseudoRiemannianBundle (IB := IB) (n := (2 : WithTop ℕ∞)) (F := F) (E := E)] :
    IsContMDiffPseudoRiemannianBundle (IB := IB) (n := (1 : WithTop ℕ∞)) (F := F) (E := E) :=
  IsContMDiffPseudoRiemannianBundle.of_le (IB := IB) (F := F) (E := E) one_le_two

instance [IsContMDiffPseudoRiemannianBundle (IB := IB) (n := (3 : WithTop ℕ∞)) (F := F) (E := E)] :
    IsContMDiffPseudoRiemannianBundle (IB := IB) (n := (2 : WithTop ℕ∞)) (F := F) (E := E) :=
  IsContMDiffPseudoRiemannianBundle.of_le (IB := IB) (n := (3 : WithTop ℕ∞)) (F := F) (E := E)
    (by norm_cast)

namespace ContMDiffPseudoRiemannianMetric

/-- A smooth pseudo-Riemannian metric along a bundle induces the corresponding fiberwise
structure. -/
@[reducible] def toPseudoRiemannianBundle
    (g : ContMDiffPseudoRiemannianMetric (IB := IB) (n := n) (F := F) (E := E)) :
    PseudoRiemannianBundle (B := B) (E := E) where
  metric := g.metric
  symm := g.symm
  nondegenerate := g.nondegenerate

instance (g : ContMDiffPseudoRiemannianMetric (IB := IB) (n := n) (F := F) (E := E)) :
    letI : PseudoRiemannianBundle (B := B) (E := E) := toPseudoRiemannianBundle (IB := IB) (n := n)
      (F := F) (E := E) g
    IsContMDiffPseudoRiemannianBundle (IB := IB) (n := n) (F := F) (E := E) :=
  letI : PseudoRiemannianBundle (B := B) (E := E) := toPseudoRiemannianBundle (IB := IB) (n := n)
    (F := F) (E := E) g
  ⟨⟨g, fun _ _ _ => rfl⟩⟩

end ContMDiffPseudoRiemannianMetric

section ContMDiffPairing

variable
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  [h : IsContMDiffPseudoRiemannianBundle (IB := IB) (n := n) (F := F) (E := E)]
  {b : M → B} {v w : ∀ x, E (b x)} {s : Set M} {x : M}

omit [PseudoRiemannianBundle (B := B) (E := E)] h in
/-- Given two smooth maps into the same fibers, their pairing under a smooth pseudo-Riemannian
bundle metric is smooth. -/
lemma ContMDiffWithinAt.metric_bundle
    (g : ContMDiffPseudoRiemannianMetric (IB := IB) (n := n) (F := F) (E := E))
    (hv : ContMDiffWithinAt IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (v m : TotalSpace F E)) s x)
    (hw : ContMDiffWithinAt IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (w m : TotalSpace F E)) s x) :
    ContMDiffWithinAt IM 𝓘(ℝ) n (fun m ↦ g.metric (b m) (v m) (w m)) s x := by
  have hb : ContMDiffWithinAt IM IB n b s x := by
    simp only [contMDiffWithinAt_totalSpace] at hv
    exact hv.1
  have : ContMDiffWithinAt IM (IB.prod 𝓘(ℝ)) n
      (fun m ↦ TotalSpace.mk' ℝ (E := Bundle.Trivial B ℝ) (b m)
        (g.metric (b m) (v m) (w m))) s x := by
    apply ContMDiffWithinAt.clm_bundle_apply₂ (F₁ := F) (F₂ := F)
    · exact ContMDiffAt.comp_contMDiffWithinAt x g.contMDiff.contMDiffAt hb
    · exact hv
    · exact hw
  simp only [contMDiffWithinAt_totalSpace] at this
  exact this.2

/-- Given two smooth maps into the same fibers of a pseudo-Riemannian bundle, their pairing is
smooth. -/
lemma ContMDiffWithinAt.pseudoInner_bundle
    (hv : ContMDiffWithinAt IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (v m : TotalSpace F E)) s x)
    (hw : ContMDiffWithinAt IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (w m : TotalSpace F E)) s x) :
    ContMDiffWithinAt IM 𝓘(ℝ) n (fun m ↦ pseudoInner (B := B) (E := E) (b m) (v m) (w m)) s x := by
  rcases h.exists_contMDiff with ⟨g, hg⟩
  have hpair := ContMDiffWithinAt.metric_bundle (IB := IB) (n := n) (F := F) (E := E)
    (b := b) (v := v) (w := w) (s := s) (x := x) g hv hw
  have hrewrite :
      (fun m ↦ pseudoInner (B := B) (E := E) (b m) (v m) (w m)) =
        (fun m ↦ g.metric (b m) (v m) (w m)) := by
    funext m
    simpa [Bundle.pseudoInner] using (hg (b m) (v m) (w m))
  simpa [hrewrite] using hpair

lemma ContMDiffAt.pseudoInner_bundle
    (hv : ContMDiffAt IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (v m : TotalSpace F E)) x)
    (hw : ContMDiffAt IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (w m : TotalSpace F E)) x) :
    ContMDiffAt IM 𝓘(ℝ) n (fun m ↦ pseudoInner (B := B) (E := E) (b m) (v m) (w m)) x :=
  ContMDiffWithinAt.pseudoInner_bundle (IB := IB) (n := n) (F := F) (E := E) hv hw

lemma ContMDiffOn.pseudoInner_bundle
    (hv : ContMDiffOn IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (v m : TotalSpace F E)) s)
    (hw : ContMDiffOn IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (w m : TotalSpace F E)) s) :
    ContMDiffOn IM 𝓘(ℝ) n (fun m ↦ pseudoInner (B := B) (E := E) (b m) (v m) (w m)) s :=
  fun x hx ↦ (hv x hx).pseudoInner_bundle (IB := IB) (n := n) (F := F) (E := E) (hw x hx)

lemma ContMDiff.pseudoInner_bundle
    (hv : ContMDiff IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (v m : TotalSpace F E)))
    (hw : ContMDiff IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (w m : TotalSpace F E))) :
    ContMDiff IM 𝓘(ℝ) n (fun m ↦ pseudoInner (B := B) (E := E) (b m) (v m) (w m)) :=
  fun x ↦ (hv x).pseudoInner_bundle (IB := IB) (n := n) (F := F) (E := E) (hw x)

end ContMDiffPairing

section MDifferentiablePairing

variable
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  [h : IsContMDiffPseudoRiemannianBundle (IB := IB) (n := (1 : WithTop ℕ∞)) (F := F) (E := E)]
  {b : M → B} {v w : ∀ x, E (b x)} {s : Set M} {x : M}

/-- Given two differentiable maps into the same fibers of a pseudo-Riemannian bundle, their
pairing is differentiable. -/
lemma MDifferentiableWithinAt.pseudoInner_bundle
    (hv : MDifferentiableWithinAt IM (IB.prod 𝓘(ℝ, F)) (fun m ↦ (v m : TotalSpace F E)) s x)
    (hw : MDifferentiableWithinAt IM (IB.prod 𝓘(ℝ, F)) (fun m ↦ (w m : TotalSpace F E)) s x) :
    MDifferentiableWithinAt IM 𝓘(ℝ)
      (fun m ↦ pseudoInner (B := B) (E := E) (b m) (v m) (w m)) s x := by
  rcases h.exists_contMDiff with ⟨g, hg⟩
  have hb : MDifferentiableWithinAt IM IB b s x := by
    simp only [mdifferentiableWithinAt_totalSpace] at hv
    exact hv.1
  have hpair : MDifferentiableWithinAt IM (IB.prod 𝓘(ℝ))
      (fun m ↦ TotalSpace.mk' ℝ (E := Bundle.Trivial B ℝ) (b m)
        (g.metric (b m) (v m) (w m))) s x := by
    apply MDifferentiableWithinAt.clm_bundle_apply₂ (F₁ := F) (F₂ := F)
    · exact MDifferentiableAt.comp_mdifferentiableWithinAt x
        (g.contMDiff.mdifferentiableAt one_ne_zero) hb
    · exact hv
    · exact hw
  have hrewrite :
      (fun m ↦ pseudoInner (B := B) (E := E) (b m) (v m) (w m)) =
        (fun m ↦ g.metric (b m) (v m) (w m)) := by
    funext m
    simpa [Bundle.pseudoInner] using (hg (b m) (v m) (w m))
  simp only [mdifferentiableWithinAt_totalSpace] at hpair
  simpa [hrewrite] using hpair.2

lemma MDifferentiableAt.pseudoInner_bundle
    (hv : MDifferentiableAt IM (IB.prod 𝓘(ℝ, F)) (fun m ↦ (v m : TotalSpace F E)) x)
    (hw : MDifferentiableAt IM (IB.prod 𝓘(ℝ, F)) (fun m ↦ (w m : TotalSpace F E)) x) :
    MDifferentiableAt IM 𝓘(ℝ)
      (fun m ↦ pseudoInner (B := B) (E := E) (b m) (v m) (w m)) x :=
  MDifferentiableWithinAt.pseudoInner_bundle (IB := IB) (F := F) (E := E) hv hw

lemma MDifferentiableOn.pseudoInner_bundle
    (hv : MDifferentiableOn IM (IB.prod 𝓘(ℝ, F)) (fun m ↦ (v m : TotalSpace F E)) s)
    (hw : MDifferentiableOn IM (IB.prod 𝓘(ℝ, F)) (fun m ↦ (w m : TotalSpace F E)) s) :
    MDifferentiableOn IM 𝓘(ℝ)
      (fun m ↦ pseudoInner (B := B) (E := E) (b m) (v m) (w m)) s :=
  fun x hx ↦ (hv x hx).pseudoInner_bundle (IB := IB) (F := F) (E := E) (hw x hx)

lemma MDifferentiable.pseudoInner_bundle
    (hv : MDifferentiable IM (IB.prod 𝓘(ℝ, F)) (fun m ↦ (v m : TotalSpace F E)))
    (hw : MDifferentiable IM (IB.prod 𝓘(ℝ, F)) (fun m ↦ (w m : TotalSpace F E))) :
    MDifferentiable IM 𝓘(ℝ)
      (fun m ↦ pseudoInner (B := B) (E := E) (b m) (v m) (w m)) :=
  fun x ↦ (hv x).pseudoInner_bundle (IB := IB) (F := F) (E := E) (hw x)

end MDifferentiablePairing

end ContMDiff

end Bundle

/-! ## Quadratic-form helper -/

namespace PseudoRiemannianMetric

/-- Turn a (curried) symmetric bilinear map on a tangent space into the associated quadratic form
`v ↦ val x v v`.

This is the entry point to quadratic-form invariants (e.g. `QuadraticForm.sigNeg`) from bundled
metric data; compare O'Neill, *Semi-Riemannian Geometry* (1983), p. 47. -/
noncomputable def valToQuadraticForm
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type w} [TopologicalSpace H]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ E H}
    (val : ∀ (x : M), TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ))
    (symm : ∀ (x : M) (v w : TangentSpace I x), (val x v) w = (val x w) v)
    (x : M) : QuadraticForm ℝ (TangentSpace I x) where
  toFun v := val x v v
  toFun_smul a v := by
    simp only [ContinuousLinearMap.map_smul, ContinuousLinearMap.smul_apply, smul_smul]
  exists_companion' :=
      ⟨LinearMap.mk₂ ℝ (fun v y => val x v y + val x y v)
        (fun v₁ v₂ y => by simp only [map_add, add_apply]; ring)
        (fun a v y => by simp only [map_smul, smul_apply]; ring_nf; exact Eq.symm (smul_add ..))
        (fun v y₁ y₂ => by simp only [map_add, add_apply]; ring)
        (fun a v y => by simp only [map_smul, smul_apply]; ring_nf; exact Eq.symm (smul_add ..)),
            by
              intro v y
              simp only [LinearMap.mk₂_apply, ContinuousLinearMap.map_add,
                ContinuousLinearMap.add_apply, symm x]
              ring⟩

end PseudoRiemannianMetric

/-- A general (pseudo-)metric tensor of smoothness class `C^n` on a manifold `M`.

This is the common core shared by Riemannian and pseudo-Riemannian metrics:
a smoothly varying symmetric, nondegenerate bilinear form on each tangent space.

The pseudo-Riemannian notion will extend this with an index/signature constancy condition. -/
@[ext]
structure MetricTensor
    (E : Type v) (H : Type w) (M : Type*) (n : WithTop ℕ∞)
    [inst_norm_grp_E : NormedAddCommGroup E]
    [inst_norm_sp_E : NormedSpace ℝ E]
    [inst_top_H : TopologicalSpace H]
    [inst_top_M : TopologicalSpace M]
    [inst_chart_M : ChartedSpace H M]
    (I : ModelWithCorners ℝ E H)
    [inst_mani : IsManifold I (n + 1) M] :
      Type _ where
  /-- The metric tensor at each point `x : M`, represented as a continuous linear map
      `TₓM →L[ℝ] (TₓM →L[ℝ] ℝ)`. Applying it twice, `(val x v) w`, yields `gₓ(v, w)`. -/
  val : ∀ (x : M), TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ)
  /-- Symmetry: `gₓ(v, w) = gₓ(w, v)`. -/
  symm : ∀ (x : M) (v w : TangentSpace I x), (val x v) w = (val x w) v
  /-- Non-degeneracy: if `gₓ(v, w) = 0` for all `w`, then `v = 0`. -/
  nondegenerate : ∀ (x : M) (v : TangentSpace I x), (∀ w : TangentSpace I x,
    (val x v) w = 0) → v = 0
  /-- Smoothness of the metric tensor as a smooth section of the bundle of bilinear forms.
  We follow the same pattern as Mathlib's Riemannian metric API, using `TotalSpace.mk'`
  for the bundled map. -/
  contMDiff :
    letI : IsManifold I 1 M :=
        IsManifold.of_le (I := I) (M := M) (m := (1 : WithTop ℕ∞)) (n := n + 1)
          (by simp)
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) n
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) x (val x))

namespace MetricTensor

variable {E : Type v} {H : Type w} {M : Type*} {n : WithTop ℕ∞}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners ℝ E H}
variable [IsManifold I (n + 1) M]

/-- Coercion from `MetricTensor` to its `val` function. -/
instance coeFunInst : CoeFun (MetricTensor E H M n I)
    (fun _ => ∀ x : M, TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ)) where
  coe g := g.val

/-- The bilinear form on `TₓM` associated to a metric tensor. -/
noncomputable def toBilinForm (g : MetricTensor E H M n I) (x : M) :
    LinearMap.BilinForm ℝ (TangentSpace I x) where
  toFun := fun v =>
    { toFun := fun w => g.val x v w
      map_add' := fun w₁ w₂ => by simp only [ContinuousLinearMap.map_add]
      map_smul' := fun c w => by simp only [map_smul, smul_eq_mul, RingHom.id_apply] }
  map_add' := fun v₁ v₂ => by
    ext w
    simp only [map_add, add_apply, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
  map_smul' := fun c v => by
    ext w
    simp only [map_smul, coe_smul', Pi.smul_apply, smul_eq_mul, LinearMap.coe_mk, AddHom.coe_mk,
      RingHom.id_apply, LinearMap.smul_apply]

/-- The quadratic form `v ↦ gₓ(v,v)` associated to a metric tensor. -/
noncomputable abbrev toQuadraticForm (g : MetricTensor E H M n I) (x : M) :
    QuadraticForm ℝ (TangentSpace I x) :=
  PseudoRiemannianMetric.valToQuadraticForm g.val g.symm x

@[simp]
lemma toBilinForm_apply (g : MetricTensor E H M n I) (x : M) (v w : TangentSpace I x) :
    toBilinForm g x v w = g.val x v w := rfl

@[simp]
lemma toQuadraticForm_apply (g : MetricTensor E H M n I) (x : M) (v : TangentSpace I x) :
    toQuadraticForm g x v = g.val x v v := rfl

@[simp]
lemma toBilinForm_isSymm (g : MetricTensor E H M n I) (x : M) :
    (toBilinForm g x).IsSymm := by
  refine { eq := ?_ }
  intro v w
  simp [toBilinForm_apply, g.symm x v w]

@[simp]
lemma toBilinForm_nondegenerate (g : MetricTensor E H M n I) (x : M) :
    (toBilinForm g x).Nondegenerate := by
  unfold LinearMap.BilinForm.Nondegenerate LinearMap.Nondegenerate
    LinearMap.SeparatingLeft LinearMap.SeparatingRight
  constructor
  · intro v hv
    simp_rw [toBilinForm_apply] at hv
    exact g.nondegenerate x v hv
  · intro v hv
    simp_rw [toBilinForm_apply] at hv
    have hw : ∀ w : TangentSpace I x, (g.val x v) w = 0 := by
      intro w
      simpa [g.symm x v w] using hv w
    exact g.nondegenerate x v hw

/-- The value `gₓ(v,w)` of a metric tensor. -/
noncomputable def inner (g : MetricTensor E H M n I) (x : M) (v w : TangentSpace I x) : ℝ :=
  g.val x v w

@[simp]
lemma inner_apply (g : MetricTensor E H M n I) (x : M) (v w : TangentSpace I x) :
    inner g x v w = g.val x v w := rfl

/-! ### Smoothness of the pairing `g(v,w)` -/

section PairingSmoothness

variable [IsManifold I 1 M]

variable
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace HM M']
  {b : M' → M} {v w : ∀ x, TangentSpace I (b x)} {s : Set M'} {x : M'}

/-- Smoothness of the metric pairing along a smooth base map, for smooth fields into the fibers. -/
lemma ContMDiffWithinAt.inner
    (g : MetricTensor E H M n I)
    (hv : ContMDiffWithinAt IM (I.prod 𝓘(ℝ, E)) n
      (fun m ↦ (v m : TotalSpace E fun y : M ↦ TangentSpace I y)) s x)
    (hw : ContMDiffWithinAt IM (I.prod 𝓘(ℝ, E)) n
      (fun m ↦ (w m : TotalSpace E fun y : M ↦ TangentSpace I y)) s x) :
    ContMDiffWithinAt IM 𝓘(ℝ) n (fun m ↦ g.inner (b m) (v m) (w m)) s x := by
  have hb : ContMDiffWithinAt IM I n b s x := by
    simp only [contMDiffWithinAt_totalSpace] at hv
    exact hv.1
  have : ContMDiffWithinAt IM (I.prod 𝓘(ℝ)) n
      (fun m ↦ TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) (b m)
        ((g.val (b m)) (v m) (w m))) s x := by
    apply ContMDiffWithinAt.clm_bundle_apply₂ (F₁ := E) (F₂ := E)
    · exact ContMDiffAt.comp_contMDiffWithinAt x g.contMDiff.contMDiffAt hb
    · exact hv
    · exact hw
  simp only [contMDiffWithinAt_totalSpace] at this
  simpa [MetricTensor.inner] using this.2

lemma ContMDiffAt.inner
    (g : MetricTensor E H M n I)
    (hv : ContMDiffAt IM (I.prod 𝓘(ℝ, E)) n
      (fun m ↦ (v m : TotalSpace E fun y : M ↦ TangentSpace I y)) x)
    (hw : ContMDiffAt IM (I.prod 𝓘(ℝ, E)) n
      (fun m ↦ (w m : TotalSpace E fun y : M ↦ TangentSpace I y)) x) :
    ContMDiffAt IM 𝓘(ℝ) n (fun m ↦ g.inner (b m) (v m) (w m)) x :=
  ContMDiffWithinAt.inner (g := g) hv hw

lemma ContMDiffOn.inner
    (g : MetricTensor E H M n I)
    (hv : ContMDiffOn IM (I.prod 𝓘(ℝ, E)) n
      (fun m ↦ (v m : TotalSpace E fun y : M ↦ TangentSpace I y)) s)
    (hw : ContMDiffOn IM (I.prod 𝓘(ℝ, E)) n
      (fun m ↦ (w m : TotalSpace E fun y : M ↦ TangentSpace I y)) s) :
    ContMDiffOn IM 𝓘(ℝ) n (fun m ↦ g.inner (b m) (v m) (w m)) s :=
  fun x hx ↦ ContMDiffWithinAt.inner (g := g) (x := x) (hv x hx) (hw x hx)

lemma ContMDiff.inner
    (g : MetricTensor E H M n I)
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
    (g : MetricTensor E H M n I)
    (hn : (1 : WithTop ℕ∞) ≤ n)
    (hv : MDifferentiableWithinAt IM (I.prod 𝓘(ℝ, E))
      (fun m ↦ (v m : TotalSpace E fun y : M ↦ TangentSpace I y)) s x)
    (hw : MDifferentiableWithinAt IM (I.prod 𝓘(ℝ, E))
      (fun m ↦ (w m : TotalSpace E fun y : M ↦ TangentSpace I y)) s x) :
    MDifferentiableWithinAt IM 𝓘(ℝ) (fun m ↦ g.inner (b m) (v m) (w m)) s x := by
  have hb : MDifferentiableWithinAt IM I b s x := by
    simp only [mdifferentiableWithinAt_totalSpace] at hv
    exact hv.1
  have hpair : MDifferentiableWithinAt IM (I.prod 𝓘(ℝ))
      (fun m ↦ TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) (b m)
        ((g.val (b m)) (v m) (w m))) s x := by
    apply MDifferentiableWithinAt.clm_bundle_apply₂ (F₁ := E) (F₂ := E)
    · exact MDifferentiableAt.comp_mdifferentiableWithinAt x
        ((g.contMDiff.of_le hn).mdifferentiableAt one_ne_zero) hb
    · exact hv
    · exact hw
  simp only [mdifferentiableWithinAt_totalSpace] at hpair
  simpa [MetricTensor.inner] using hpair.2

lemma MDifferentiableAt.inner
    [IsManifold I 1 M]
    (g : MetricTensor E H M n I)
    (hn : (1 : WithTop ℕ∞) ≤ n)
    (hv : MDifferentiableAt IM (I.prod 𝓘(ℝ, E))
      (fun m ↦ (v m : TotalSpace E fun y : M ↦ TangentSpace I y)) x)
    (hw : MDifferentiableAt IM (I.prod 𝓘(ℝ, E))
      (fun m ↦ (w m : TotalSpace E fun y : M ↦ TangentSpace I y)) x) :
    MDifferentiableAt IM 𝓘(ℝ) (fun m ↦ g.inner (b m) (v m) (w m)) x :=
  MDifferentiableWithinAt.inner (g := g) hn hv hw

lemma MDifferentiableOn.inner
    [IsManifold I 1 M]
    (g : MetricTensor E H M n I)
    (hn : (1 : WithTop ℕ∞) ≤ n)
    (hv : MDifferentiableOn IM (I.prod 𝓘(ℝ, E))
      (fun m ↦ (v m : TotalSpace E fun y : M ↦ TangentSpace I y)) s)
    (hw : MDifferentiableOn IM (I.prod 𝓘(ℝ, E))
      (fun m ↦ (w m : TotalSpace E fun y : M ↦ TangentSpace I y)) s) :
    MDifferentiableOn IM 𝓘(ℝ) (fun m ↦ g.inner (b m) (v m) (w m)) s :=
  fun x hx ↦ MDifferentiableWithinAt.inner (g := g) (x := x) hn (hv x hx) (hw x hx)

lemma MDifferentiable.inner
    [IsManifold I 1 M]
    (g : MetricTensor E H M n I)
    (hn : (1 : WithTop ℕ∞) ≤ n)
    (hv : MDifferentiable IM (I.prod 𝓘(ℝ, E))
      (fun m ↦ (v m : TotalSpace E fun y : M ↦ TangentSpace I y)))
    (hw : MDifferentiable IM (I.prod 𝓘(ℝ, E))
      (fun m ↦ (w m : TotalSpace E fun y : M ↦ TangentSpace I y))) :
    MDifferentiable IM 𝓘(ℝ) (fun m ↦ g.inner (b m) (v m) (w m)) :=
  fun x ↦ MDifferentiableAt.inner (g := g) (x := x) hn (hv x) (hw x)

end MDifferentiablePairing

/-! ## Flat / sharp (musical isomorphisms) -/

/-- Index lowering map `v ↦ gₓ(v, -)` as a continuous linear map. -/
abbrev flatL (g : MetricTensor E H M n I) (x : M) :
    TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ) :=
  g.val x

/-- Index lowering map `v ↦ gₓ(v, -)` as a linear map. -/
abbrev flat (g : MetricTensor E H M n I) (x : M) :
    TangentSpace I x →ₗ[ℝ] (TangentSpace I x →L[ℝ] ℝ) :=
  (g.flatL x).toLinearMap

@[simp]
lemma flat_apply (g : MetricTensor E H M n I) (x : M) (v w : TangentSpace I x) :
    (flat g x v) w = g.val x v w := rfl

@[simp]
lemma flatL_apply (g : MetricTensor E H M n I) (x : M) (v w : TangentSpace I x) :
    (flatL g x v) w = g.val x v w := rfl

lemma flat_inj (g : MetricTensor E H M n I) (x : M) : Function.Injective (flat g x) := by
  rw [← LinearMap.ker_eq_bot]
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  apply g.nondegenerate x v
  intro w
  exact DFunLike.congr_fun hv w

lemma flatL_inj (g : MetricTensor E H M n I) (x : M) : Function.Injective (flatL g x) :=
  flat_inj g x

/-- Index lowering on the total space of the tangent bundle. -/
noncomputable abbrev flatBundleMap (g : MetricTensor E H M n I) :
    Bundle.TotalSpace E (fun y : M ↦ TangentSpace I y) →
      Bundle.TotalSpace (E →L[ℝ] ℝ) (fun y : M ↦ TangentSpace I y →L[ℝ] ℝ)
  | ⟨x, v⟩ => ⟨x, g.flatL x v⟩

lemma flatBundleMap_apply (g : MetricTensor E H M n I) (x : M) (v : TangentSpace I x) :
    g.flatBundleMap ⟨x, v⟩ = ⟨x, g.flatL x v⟩ := rfl

/-! ### Smoothness of index lowering -/

/-- The family `x ↦ g.flatL x` is a smooth section of the bundle of continuous linear maps from the
tangent bundle to the cotangent bundle. -/
lemma contMDiff_flatL [IsManifold I 1 M] (g : MetricTensor E H M n I) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) n
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y : M ↦ TangentSpace I y →L[ℝ] (TangentSpace I y →L[ℝ] ℝ))
        x (g.flatL x)) := by
  simpa [flatL] using g.contMDiff

section FlatSmoothness

variable
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace HM M']
  {b : M' → M} {v : ∀ x, TangentSpace I (b x)} {s : Set M'} {x : M'}

/-- Lowering an index with a smooth metric tensor sends smooth vector fields to smooth covector
fields. -/
lemma ContMDiffWithinAt.flatL
    [IsManifold I 1 M]
    (g : MetricTensor E H M n I)
    (hv : ContMDiffWithinAt IM (I.prod 𝓘(ℝ, E)) n
      (fun m ↦ (v m : TotalSpace E fun y : M ↦ TangentSpace I y)) s x) :
    ContMDiffWithinAt IM (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) n
      (fun m ↦ TotalSpace.mk' (E →L[ℝ] ℝ)
        (E := fun y : M ↦ TangentSpace I y →L[ℝ] ℝ)
        (b m) (g.flatL (b m) (v m))) s x := by
  have hv' := hv
  simp only [contMDiffWithinAt_totalSpace] at hv'
  have hflat : ContMDiffWithinAt IM (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) n
      (fun m ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y : M ↦ TangentSpace I y →L[ℝ] (TangentSpace I y →L[ℝ] ℝ))
        (b m) (g.flatL (b m))) s x := by
    exact ContMDiffAt.comp_contMDiffWithinAt x (contMDiff_flatL (g := g)).contMDiffAt hv'.1
  exact ContMDiffWithinAt.clm_bundle_apply (F₁ := E) (F₂ := E →L[ℝ] ℝ) hflat hv

lemma ContMDiffAt.flatL
    [IsManifold I 1 M]
    (g : MetricTensor E H M n I)
    (hv : ContMDiffAt IM (I.prod 𝓘(ℝ, E)) n
      (fun m ↦ (v m : TotalSpace E fun y : M ↦ TangentSpace I y)) x) :
    ContMDiffAt IM (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) n
      (fun m ↦ TotalSpace.mk' (E →L[ℝ] ℝ)
        (E := fun y : M ↦ TangentSpace I y →L[ℝ] ℝ)
        (b m) (g.flatL (b m) (v m))) x :=
  ContMDiffWithinAt.flatL (g := g) hv

lemma ContMDiffOn.flatL
    [IsManifold I 1 M]
    (g : MetricTensor E H M n I)
    (hv : ContMDiffOn IM (I.prod 𝓘(ℝ, E)) n
      (fun m ↦ (v m : TotalSpace E fun y : M ↦ TangentSpace I y)) s) :
    ContMDiffOn IM (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) n
      (fun m ↦ TotalSpace.mk' (E →L[ℝ] ℝ)
        (E := fun y : M ↦ TangentSpace I y →L[ℝ] ℝ)
        (b m) (g.flatL (b m) (v m))) s :=
  fun x hx ↦ ContMDiffWithinAt.flatL (g := g) (hv x hx)

lemma ContMDiff.flatL
    [IsManifold I 1 M]
    (g : MetricTensor E H M n I)
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
    (g : MetricTensor E H M n I)
    (hn : (1 : WithTop ℕ∞) ≤ n)
    (hv : MDifferentiableWithinAt IM (I.prod 𝓘(ℝ, E))
      (fun m ↦ (v m : TotalSpace E fun y : M ↦ TangentSpace I y)) s x) :
    MDifferentiableWithinAt IM (I.prod 𝓘(ℝ, E →L[ℝ] ℝ))
      (fun m ↦ TotalSpace.mk' (E →L[ℝ] ℝ)
        (E := fun y : M ↦ TangentSpace I y →L[ℝ] ℝ)
        (b m) (g.flatL (b m) (v m))) s x := by
  have hv' := hv
  simp only [mdifferentiableWithinAt_totalSpace] at hv'
  have hflat : MDifferentiableWithinAt IM (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ))
      (fun m ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y : M ↦ TangentSpace I y →L[ℝ] (TangentSpace I y →L[ℝ] ℝ))
        (b m) (g.flatL (b m))) s x := by
    exact MDifferentiableAt.comp_mdifferentiableWithinAt x
      (((contMDiff_flatL (g := g)).of_le hn).mdifferentiableAt one_ne_zero) hv'.1
  exact MDifferentiableWithinAt.clm_bundle_apply (F₁ := E) (F₂ := E →L[ℝ] ℝ) hflat hv

lemma MDifferentiableAt.flatL
    [IsManifold I 1 M]
    (g : MetricTensor E H M n I)
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
    (g : MetricTensor E H M n I)
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
    (g : MetricTensor E H M n I)
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
lemma contMDiff_flatBundleMap [IsManifold I 1 M] (g : MetricTensor E H M n I) :
    ContMDiff (I.prod 𝓘(ℝ, E)) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) n g.flatBundleMap := by
  simpa [flatBundleMap] using
    (ContMDiff.flatL (g := g)
      (b := fun p : Bundle.TotalSpace E (fun y : M ↦ TangentSpace I y) => p.1)
      (v := fun p => p.2) contMDiff_id)

/-- Index lowering is differentiable on the total space of the tangent bundle. -/
lemma mdifferentiable_flatBundleMap [IsManifold I 1 M]
    (g : MetricTensor E H M n I) (hn : (1 : WithTop ℕ∞) ≤ n) :
    MDifferentiable (I.prod 𝓘(ℝ, E)) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) g.flatBundleMap := by
  simpa [flatBundleMap] using
    (MDifferentiable.flatL (g := g)
      (b := fun p : Bundle.TotalSpace E (fun y : M ↦ TangentSpace I y) => p.1)
      (v := fun p => p.2) hn mdifferentiable_id)

section FiniteDimensional

variable [inst_tangent_findim : ∀ (x : M), FiniteDimensional ℝ (TangentSpace I x)]

/-! In finite dimensions, nondegeneracy implies that `flatL` is automatically surjective, so the
musical isomorphisms can be packaged as inverse continuous linear equivalences. In infinite
dimensions, one would need a stronger nondegeneracy hypothesis to obtain such equivalences. -/

lemma flatL_surj (g : MetricTensor E H M n I) (x : M) : Function.Surjective (g.flatL x) := by
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inst_tangent_findim x
  have h_finrank_eq :
      finrank ℝ (TangentSpace I x) = finrank ℝ (TangentSpace I x →L[ℝ] ℝ) := by
    have h_dual_eq : finrank ℝ (TangentSpace I x →L[ℝ] ℝ) =
        finrank ℝ (Module.Dual ℝ (TangentSpace I x)) := by
      let to_dual : (TangentSpace I x →L[ℝ] ℝ) → Module.Dual ℝ (TangentSpace I x) :=
        fun f => f.toLinearMap
      let from_dual : Module.Dual ℝ (TangentSpace I x) → (TangentSpace I x →L[ℝ] ℝ) :=
        fun f => ContinuousLinearMap.mk f (by
          apply LinearMap.continuous_of_finiteDimensional)
      let equiv : (TangentSpace I x →L[ℝ] ℝ) ≃ₗ[ℝ] Module.Dual ℝ (TangentSpace I x) :=
        { toFun := to_dual
          invFun := from_dual
          map_add' := fun f g => by ext v; rfl
          map_smul' := fun c f => by ext v; rfl
          left_inv := fun f => by ext v; rfl
          right_inv := fun f => by ext v; rfl }
      exact LinearEquiv.finrank_eq equiv
    rw [h_dual_eq, ← Subspace.dual_finrank_eq]
  exact
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank h_finrank_eq).mp (flatL_inj g x)

/-- `flatEquiv` as a continuous linear equivalence.

In finite dimensions, nondegeneracy of the metric implies surjectivity of `flatL`, so no extra
data are required. -/
noncomputable def flatEquiv (g : MetricTensor E H M n I) (x : M) :
    TangentSpace I x ≃L[ℝ] (TangentSpace I x →L[ℝ] ℝ) :=
  LinearEquiv.toContinuousLinearEquiv <|
    LinearEquiv.ofBijective (g.flatL x).toLinearMap ⟨g.flatL_inj x, g.flatL_surj x⟩

@[simp]
lemma flatEquiv_apply (g : MetricTensor E H M n I) (x : M) (v w : TangentSpace I x) :
    (g.flatEquiv x v) w = g.val x v w := rfl

/-- Index raising equivalence as the inverse of `flatEquiv`.

This is the finite-dimensional `sharp` isomorphism; in infinite dimensions one would need a
stronger hypothesis to package index-raising in this form. -/
noncomputable def sharpEquiv (g : MetricTensor E H M n I) (x : M) :
    (TangentSpace I x →L[ℝ] ℝ) ≃L[ℝ] TangentSpace I x :=
  (g.flatEquiv x).symm

/-- Index raising map `ω ↦ sharp ω` as a continuous linear map. -/
noncomputable def sharpL (g : MetricTensor E H M n I) (x : M) :
    (TangentSpace I x →L[ℝ] ℝ) →L[ℝ] TangentSpace I x :=
  (g.sharpEquiv x).toContinuousLinearMap

/-- Index raising map `sharp` as a linear map. -/
noncomputable def sharp (g : MetricTensor E H M n I) (x : M) :
    (TangentSpace I x →L[ℝ] ℝ) →ₗ[ℝ] TangentSpace I x :=
  (g.sharpEquiv x).toLinearEquiv.toLinearMap

/-- Index raising on the total space of the cotangent bundle. -/
noncomputable abbrev sharpBundleMap (g : MetricTensor E H M n I) :
    Bundle.TotalSpace (E →L[ℝ] ℝ) (fun y : M ↦ TangentSpace I y →L[ℝ] ℝ) →
      Bundle.TotalSpace E (fun y : M ↦ TangentSpace I y)
  | ⟨x, ω⟩ => ⟨x, g.sharpL x ω⟩

lemma sharpBundleMap_apply (g : MetricTensor E H M n I) (x : M) (ω : TangentSpace I x →L[ℝ] ℝ) :
    g.sharpBundleMap ⟨x, ω⟩ = ⟨x, g.sharpL x ω⟩ := rfl

/-- Fiberwise musical isomorphism between the total spaces of the tangent and cotangent bundles. -/
noncomputable def flatBundleEquiv (g : MetricTensor E H M n I) :
    Bundle.TotalSpace E (fun y : M ↦ TangentSpace I y) ≃
      Bundle.TotalSpace (E →L[ℝ] ℝ) (fun y : M ↦ TangentSpace I y →L[ℝ] ℝ) where
  toFun := g.flatBundleMap
  invFun := g.sharpBundleMap
  left_inv := by
    rintro ⟨x, v⟩
    change Bundle.TotalSpace.mk x (g.sharpL x (g.flatL x v)) = Bundle.TotalSpace.mk x v
    exact congrArg (Bundle.TotalSpace.mk x) ((g.flatEquiv x).left_inv v)
  right_inv := by
    rintro ⟨x, ω⟩
    change
      (Bundle.TotalSpace.mk x (g.flatL x (g.sharpL x ω)) :
        Bundle.TotalSpace (E →L[ℝ] ℝ) (fun y : M ↦ TangentSpace I y →L[ℝ] ℝ)) =
      Bundle.TotalSpace.mk x ω
    exact congrArg (Bundle.TotalSpace.mk x) ((g.flatEquiv x).right_inv ω)

@[simp]
lemma sharpL_apply_flatL (g : MetricTensor E H M n I) (x : M) (v : TangentSpace I x) :
    g.sharpL x (g.flatL x v) = v :=
  (g.flatEquiv x).left_inv v

@[simp]
lemma flatL_apply_sharpL (g : MetricTensor E H M n I) (x : M)
    (ω : TangentSpace I x →L[ℝ] ℝ) : g.flatL x (g.sharpL x ω) = ω :=
  (g.flatEquiv x).right_inv ω

@[simp]
lemma flat_sharp_apply (g : MetricTensor E H M n I) (x : M)
    (ω : TangentSpace I x →L[ℝ] ℝ) : g.flat x (g.sharp x ω) = ω := by
  ext v
  have h := congrArg (fun f : TangentSpace I x →L[ℝ] ℝ => f v) (flatL_apply_sharpL (g := g) x ω)
  simpa [flat, flatL, sharp, sharpL] using h

lemma sharp_flat_apply (g : MetricTensor E H M n I) (x : M) (v : TangentSpace I x) :
    g.sharp x (g.flat x v) = v := by
  have h := sharpL_apply_flatL (g := g) x v
  simpa [sharp, sharpL, flat, flatL] using h

/-- Metric evaluated at `sharp ω₁` and `sharp ω₂`. -/
lemma apply_sharp_sharp (g : MetricTensor E H M n I) (x : M)
    (ω₁ ω₂ : TangentSpace I x →L[ℝ] ℝ) :
    g.val x (g.sharpL x ω₁) (g.sharpL x ω₂) = ω₁ (g.sharpL x ω₂) := by
  rw [← flatL_apply (g := g) x (g.sharpL x ω₁)]
  rw [flatL_apply_sharpL (g := g) x ω₁]

/-- Metric evaluated at `v` and `sharp ω`. -/
lemma apply_vec_sharp (g : MetricTensor E H M n I) (x : M) (v : TangentSpace I x)
    (ω : TangentSpace I x →L[ℝ] ℝ) :
    g.val x v (g.sharpL x ω) = ω v := by
  rw [g.symm x v (g.sharpL x ω)]
  rw [← flatL_apply (g := g) x (g.sharpL x ω)]
  rw [flatL_apply_sharpL (g := g) x ω]


end FiniteDimensional

end MetricTensor
