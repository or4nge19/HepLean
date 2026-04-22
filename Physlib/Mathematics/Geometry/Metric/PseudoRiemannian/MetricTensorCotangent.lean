/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Physlib.Mathematics.Geometry.Metric.PseudoRiemannian.Basic

/-!
# Metric tensor: cotangent metric and index

Induced cotangent-space metric (via the musical isomorphism) and the pointwise index
(`QuadraticForm.sigNeg`) for `MetricTensor`, continuing
`Physlib/Mathematics/Geometry/Metric/PseudoRiemannian/Basic.lean`.
-/

@[expose] public section

section PseudoRiemannianMetric

open Bundle Set Finset Function Filter Module Topology ContinuousLinearMap
open scoped Manifold Bundle LinearMap Dual

namespace MetricTensor

variable {E : Type v} {H : Type w} {M : Type*} {n : WithTop ℕ∞}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners ℝ E H}
variable [IsManifold I (n + 1) M]

section FiniteDimensional

variable [inst_tangent_findim : ∀ (x : M), FiniteDimensional ℝ (TangentSpace I x)]

/-! ## Cotangent metric induced by `g` -/

/-- The induced metric value on the cotangent space at `x`. -/
noncomputable def cotangentMetricVal (g : MetricTensor E H M n I) (x : M)
    (ω₁ ω₂ : TangentSpace I x →L[ℝ] ℝ) : ℝ :=
  g.val x (g.sharpL x ω₁) (g.sharpL x ω₂)

@[simp] lemma cotangentMetricVal_eq_apply_sharp (g : MetricTensor E H M n I) (x : M)
    (ω₁ ω₂ : TangentSpace I x →L[ℝ] ℝ) :
    cotangentMetricVal g x ω₁ ω₂ = ω₁ (g.sharpL x ω₂) := by
  simp [cotangentMetricVal]

lemma cotangentMetricVal_symm (g : MetricTensor E H M n I) (x : M)
    (ω₁ ω₂ : TangentSpace I x →L[ℝ] ℝ) :
    cotangentMetricVal g x ω₁ ω₂ = cotangentMetricVal g x ω₂ ω₁ := by
  unfold cotangentMetricVal
  rw [g.symm x (g.sharpL x ω₁) (g.sharpL x ω₂)]

/-- The induced cotangent metric as a bilinear form. -/
noncomputable def cotangentToBilinForm (g : MetricTensor E H M n I) (x : M) :
    LinearMap.BilinForm ℝ (TangentSpace I x →L[ℝ] ℝ) where
  toFun ω₁ :=
    { toFun := fun ω₂ => cotangentMetricVal g x ω₁ ω₂
      map_add' := fun ω₂ ω₃ => by simp [cotangentMetricVal, ContinuousLinearMap.map_add]
      map_smul' := fun c ω₂ => by simp [cotangentMetricVal, map_smul, smul_eq_mul, RingHom.id_apply]
    }
  map_add' := fun ω₁ ω₂ => by
    ext ω₃
    simp [cotangentMetricVal, ContinuousLinearMap.map_add, ContinuousLinearMap.add_apply,
      LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
  map_smul' := fun c ω₁ => by
    ext ω₂
    simp [cotangentMetricVal, ContinuousLinearMap.smul_apply,
      LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply, LinearMap.smul_apply]

/-- The induced cotangent metric as a quadratic form. -/
noncomputable def cotangentToQuadraticForm (g : MetricTensor E H M n I) (x : M) :
    QuadraticForm ℝ (TangentSpace I x →L[ℝ] ℝ) where
  toFun ω := cotangentMetricVal g x ω ω
  toFun_smul a ω := by
    simp [cotangentMetricVal, ContinuousLinearMap.smul_apply]
    ring
  exists_companion' :=
    ⟨LinearMap.mk₂ ℝ (fun ω₁ ω₂ =>
        cotangentMetricVal g x ω₁ ω₂ + cotangentMetricVal g x ω₂ ω₁)
      (fun ω₁ ω₂ ω₃ => by simp [cotangentMetricVal, map_add, add_apply]; ring)
      (fun a ω₁ ω₂ => by
        simp [cotangentMetricVal, map_smul, smul_apply]
        ring_nf)
      (fun ω₁ ω₂ ω₃ => by simp [cotangentMetricVal, map_add, add_apply]; ring)
      (fun a ω₁ ω₂ => by
        simp [cotangentMetricVal, map_smul, smul_apply]
        ring_nf),
      by
        intro ω₁ ω₂
        simp [LinearMap.mk₂_apply, cotangentMetricVal, ContinuousLinearMap.map_add,
          ContinuousLinearMap.add_apply]
        ring⟩

@[simp]
lemma cotangentToBilinForm_apply (g : MetricTensor E H M n I) (x : M)
    (ω₁ ω₂ : TangentSpace I x →L[ℝ] ℝ) :
    cotangentToBilinForm g x ω₁ ω₂ = cotangentMetricVal g x ω₁ ω₂ := rfl

@[simp]
lemma cotangentToQuadraticForm_apply (g : MetricTensor E H M n I) (x : M)
    (ω : TangentSpace I x →L[ℝ] ℝ) :
    cotangentToQuadraticForm g x ω = cotangentMetricVal g x ω ω := rfl

@[simp]
lemma cotangentToBilinForm_isSymm (g : MetricTensor E H M n I) (x : M) :
    (cotangentToBilinForm g x).IsSymm := by
  refine { eq := ?_ }
  intro ω₁ ω₂
  simpa [cotangentToBilinForm_apply] using (cotangentMetricVal_symm (g := g) x ω₁ ω₂)

/-- Nondegeneracy of the cotangent metric. -/
lemma cotangentMetricVal_nondegenerate (g : MetricTensor E H M n I) (x : M)
    (ω : TangentSpace I x →L[ℝ] ℝ)
    (h : ∀ v : TangentSpace I x →L[ℝ] ℝ, cotangentMetricVal g x ω v = 0) :
    ω = 0 := by
  apply ContinuousLinearMap.ext
  intro v
  have h_forall : ∀ w : TangentSpace I x, ω w = 0 := by
    intro w
    let ω' : TangentSpace I x →L[ℝ] ℝ := g.flatL x w
    have this : g.sharpL x ω' = w := by
      simp [ω']
    have h_apply : cotangentMetricVal g x ω ω' = 0 := h ω'
    simp [cotangentMetricVal_eq_apply_sharp] at h_apply
    simpa [this] using h_apply
  exact h_forall v

@[simp]
lemma cotangentToBilinForm_nondegenerate (g : MetricTensor E H M n I) (x : M) :
    (cotangentToBilinForm g x).Nondegenerate := by
  unfold LinearMap.BilinForm.Nondegenerate LinearMap.Nondegenerate
    LinearMap.SeparatingLeft LinearMap.SeparatingRight
  constructor
  · intro ω hω
    apply cotangentMetricVal_nondegenerate (g := g) x ω
    intro v
    exact hω v
  · intro ω hω
    apply cotangentMetricVal_nondegenerate (g := g) x ω
    intro v
    have hv : ∀ y : TangentSpace I x →L[ℝ] ℝ, ((g.cotangentToBilinForm x) ω) y = 0 := by
      intro y
      rw [LinearMap.BilinForm.isSymm_def.mp (cotangentToBilinForm_isSymm (g := g) x)]
      simp [hω]
    exact hv v

/-- The cotangent quadratic form is equivalent to the tangent quadratic form via `sharp`. -/
theorem cotangentToQuadraticForm_equivalent_toQuadraticForm (g : MetricTensor E H M n I) (x : M) :
    (g.cotangentToQuadraticForm x).Equivalent (g.toQuadraticForm x) := by
  refine ⟨?_⟩
  refine
    { toLinearEquiv := (g.sharpEquiv x).toLinearEquiv
      map_app' := fun ω => ?_ }
  simp [cotangentToQuadraticForm_apply, cotangentMetricVal, toQuadraticForm, sharpEquiv, sharpL]

end FiniteDimensional

/-- The (negative) index of a metric tensor at a point, defined as the negative index of the
associated quadratic form `v ↦ gₓ(v,v)`.

This is a pointwise invariant; it need not be locally constant. -/
noncomputable def index (g : MetricTensor E H M n I) (x : M) : ℕ :=
  sigNeg (g.toQuadraticForm x)

@[simp]
lemma index_def (g : MetricTensor E H M n I) (x : M) :
    g.index x = sigNeg (g.toQuadraticForm x) :=
  rfl

end MetricTensor

end PseudoRiemannianMetric
