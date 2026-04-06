/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Units.WithDim.Speed
/-!

# Examples of units in Physlib

In this module we give some examples of how to use the units system in Physlib.
This module should not be imported into any other module, and the results here
should not be used in the proofs of any other results other then those in this file.

-/

@[expose] public section

namespace UnitExamples
open Dimension CarriesDimension UnitChoices UnitDependent HasDim
/-!

## Defining a length dependent on units

-/

/-- The length corresponding to 400 meters. -/
noncomputable def meters400 : Dimensionful (WithDim L𝓭 ℝ) := toDimensionful SI ⟨400⟩

/-- Changing that length to miles.
  400 meters is very almost a quarter of a mile. -/
example : meters400 {SI with length := LengthUnit.miles} = ⟨1/4 - 73/50292⟩ := by
  simp [meters400, toDimensionful_apply_apply, dimScale, LengthUnit.miles]
  ext
  simp only [WithDim.smul_val]
  trans 1609.344⁻¹ * 400
  · rfl
  norm_num

/-!

## Proving propositions are dimensionally correct

-/

/-!

## Cases with only WithDim

-/

open WithDim

/-- An example of dimensions corresponding to `E = m c^2` using `WithDim`. -/
def EnergyMassWithDim' (m : WithDim M𝓭 ℝ) (E : WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)
    (c : WithDim (L𝓭 * T𝓭⁻¹) ℝ) : Prop := E = cast (m * c * c)

lemma energyMassWithDim'_isDimensionallyCorrect :
    IsDimensionallyCorrect EnergyMassWithDim' := by simp [funext_iff, EnergyMassWithDim']

/-- An example of dimensions corresponding to `F = m a` using `WithDim`. -/
def NewtonsSecondWithDim' (m : WithDim M𝓭 ℝ) (F : WithDim (M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)
    (a : WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ) : Prop :=
    F = cast (m * a)

lemma newtonsSecondWithDim'_isDimensionallyCorrect :
    IsDimensionallyCorrect NewtonsSecondWithDim' := by simp [funext_iff, NewtonsSecondWithDim']

/-- An example of dimensions corresponding to `s = d/t` using `WithDim`. -/
def SpeedEq (s : WithDim (L𝓭 * T𝓭⁻¹) ℝ) (d : WithDim L𝓭 ℝ) (t : WithDim T𝓭 ℝ) : Prop :=
  s = cast (d / t)

lemma speedEq_isDimensionallyCorrect : IsDimensionallyCorrect SpeedEq := by
  simp [funext_iff, SpeedEq]

/-- An example with complicated dimensions. -/
def OddDimensions (m1 m2 : WithDim (M𝓭) ℝ)
    (θ : WithDim Θ𝓭 ℝ) (I1 I2 : WithDim (C𝓭/T𝓭) ℝ) (d : WithDim L𝓭 ℝ) (t : WithDim T𝓭 ℝ)
    (X : WithDim (L𝓭 * T𝓭⁻¹ ^ 3 * Θ𝓭⁻¹ * C𝓭 ^2) ℝ) : Prop :=
    X = cast (m1 * (d / t) / (m2 * θ) * I2 * I1)

lemma oddDimensions_isDimensionallyCorrect : IsDimensionallyCorrect OddDimensions := by
  simp [funext_iff, OddDimensions]

/-- An example of dimensions corresponding to `E = m c^2` using `WithDim` with `.val`. -/
def EnergyMassWithDim (m : WithDim M𝓭 ℝ) (E : WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)
    (c : WithDim (L𝓭 * T𝓭⁻¹) ℝ) : Prop :=
  E.1 = m.1 * c.1 ^ 2

lemma energyMassWithDim_isDimensionallyCorrect : IsDimensionallyCorrect EnergyMassWithDim := by
  simp [funext_iff, EnergyMassWithDim]
  intros
  rw [WithDim.scaleUnit_val_eq_scaleUnit_val_of_dim_eq]

/-- An example of dimensions corresponding to `F = m a` using `WithDim` with `.val`. -/
def NewtonsSecondWithDim (m : WithDim M𝓭 ℝ) (F : WithDim (M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)
    (a : WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ) : Prop :=
  F.1 = m.1 * a.1

lemma newtonsSecondWithDim_isDimensionallyCorrect :
    IsDimensionallyCorrect NewtonsSecondWithDim := by
  simp [funext_iff, NewtonsSecondWithDim]
  intros
  rw [WithDim.scaleUnit_val_eq_scaleUnit_val_of_dim_eq]

/-- An example of dimensions corresponding to `E = m c` using `WithDim` with `.val`,
  which is not dimensionally correct. -/
def EnergyMassWithDimNot (m : WithDim M𝓭 ℝ) (E : WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)
    (c : WithDim (L𝓭 * T𝓭⁻¹) ℝ) : Prop :=
  E.1 = m.1 * c.1

lemma energyMassWithDimNot_not_isDimensionallyCorrect :
    ¬ IsDimensionallyCorrect EnergyMassWithDimNot := by
  simp only [isDimensionallyCorrect_fun_iff, not_forall, funext_iff, scaleUnit_apply_fun]
  /- We show that `EnergyMassWithDimNot` is not dimensionally correct by
    changing from `SI` to `SIPrimed` with values of `E`, `m` and `c` all equal to `1`. -/
  use SI, SIPrimed, ⟨1⟩, ⟨1⟩, ⟨1⟩
  unfold EnergyMassWithDimNot
  simp [WithDim.scaleUnit_val, M𝓭, NNReal.smul_def]
  norm_num

/-!

## Cases with Dimensionful

-/
open DimSpeed

/-- The equation `E = m c^2`, in this equation we `E` and `m` are implicitly in the
  units `u`, while the speed of light is explicitly written in those units. -/
def EnergyMass (m : WithDim M𝓭 ℝ) (E : WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)
    (u : UnitChoices) : Prop :=
    E.1 = m.1 * (speedOfLight u).1 ^ 2

/-- The equation `E = m c^2`, in this version everything is written explicitly in
  terms of a choice of units. -/
def EnergyMass' (m : Dimensionful (WithDim M𝓭 ℝ))
    (E : Dimensionful (WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ))
    (u : UnitChoices) : Prop :=
    (E.1 u).1 = (m.1 u).1 * (speedOfLight u).1 ^ 2

/-- The lemma that the proposition `EnergyMass` is dimensionally correct-/
lemma energyMass_isDimensionallyCorrect :
    IsDimensionallyCorrect EnergyMass := by
  /- Scale such that the unit u1 is taken to u2. -/
  intro u1 u2
  /- Let `m` be the mass, `E` be the energy and `u` be the actual units we start with. -/
  funext m E u
  calc _
    _ = ((scaleUnit u2 u1 E).1 =
        (scaleUnit u2 u1 m).1 * (speedOfLight.1 (scaleUnit u2 u1 u)).1 ^ 2) := by
      rfl
    _ = ((u2.dimScale u1 (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹)).1 • E.1 =
        (u2.dimScale u1 M𝓭).1 * m.1 * ((u2.dimScale u1 (L𝓭 * T𝓭⁻¹)).1 *
          (speedOfLight.1 u).1) ^ 2) := by
      conv_lhs => rw [scaleUnit_apply, scaleUnit_apply, Dimensionful.of_scaleUnit]
      rfl
    _ = ((u2.dimScale u1 (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹)).1 • E.1 =
        ((u2.dimScale u1 M𝓭 * u2.dimScale u1 (L𝓭 * T𝓭⁻¹) * u2.dimScale u1 (L𝓭 * T𝓭⁻¹)).1) *
          (m.1 * ((speedOfLight.1 u).1) ^ 2)) := by
        simp only [map_mul, NNReal.val_eq_coe, NNReal.coe_mul, smul_eq_mul, eq_iff_iff]
        ring_nf
    _ = ((u2.dimScale u1 (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹)).1 • E.1 =
        ((u2.dimScale u1 (M𝓭 * (L𝓭 * T𝓭⁻¹) * (L𝓭 * T𝓭⁻¹))).1) *
          (m.1 * ((speedOfLight.1 u).1) ^ 2)) := by
        simp
    _ = ((u2.dimScale u1 (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹)).1 • E.1 =
        ((u2.dimScale u1 (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹)).1) *
          (m.1 * ((speedOfLight.1 u).1) ^ 2)) := by
      congr 4
      ext <;> simp; try module
    _ = ((u2.dimScale u1 (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹)).1 • E.1 =
        ((u2.dimScale u1 (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹)).1) •
          (m.1 * ((speedOfLight.1 u).1) ^ 2)) := by
      rfl
  simp only [map_mul, NNReal.val_eq_coe, NNReal.coe_mul, smul_eq_mul, mul_eq_mul_left_iff,
    mul_eq_zero, NNReal.coe_eq_zero, dimScale_ne_zero, or_self, or_false, eq_iff_iff]
  rfl

/-!

## Examples of using `isDimensionallyCorrect`

We now explore the consequences of `energyMass_isDimensionallyCorrect` and how we can use it.

-/

lemma example1_energyMass : EnergyMass ⟨2⟩ ⟨2 * 299792458 ^ 2⟩ SI := by
  simp only [EnergyMass, mul_eq_mul_left_iff, OfNat.ofNat_ne_zero,
    or_false]
  simp [speedOfLight, toDimensionful_apply_apply, dimScale, SI]

/- The lemma `energyMass_isDimensionallyCorrect` allows us to scale the units
  of `example1_energyMass`, that is - we proved it in one set of units, but we get the result
  in any set of units. -/
lemma example2_energyMass (u : UnitChoices) :
    EnergyMass (scaleUnit SI u ⟨2⟩) (scaleUnit SI u ⟨2 * 299792458 ^ 2⟩) u := by
  conv_rhs => rw [← UnitChoices.scaleUnit_apply_fst SI u]
  have h1 := congrFun (congrFun (congrFun (energyMass_isDimensionallyCorrect SI u)
    (scaleUnit SI u ⟨2⟩))
    (scaleUnit SI u ⟨2 * 299792458 ^ 2⟩)) (scaleUnit SI u SI)
  rw [← h1]
  simp only [scaleUnit_apply_fst, scaleUnit_apply_fun, scaleUnit_symm_apply,
    scaleUnit_apply_fun_left]
  exact example1_energyMass

/-!

## Examples with other functions
-/

/-- An example of a dimensionally correct result using functions. -/
def CosDim (t : WithDim T𝓭 ℝ) (ω : WithDim T𝓭⁻¹ ℝ) (a : ℝ) : Prop :=
  Real.cos (ω.1 * t.1) = a

lemma cosDim_isDimensionallyCorrect : IsDimensionallyCorrect CosDim := by
  simp [funext_iff, CosDim]

/-!

## An example involving derivatives

-/

TODO "LCR7N" "Add an example involving derivatives."
end UnitExamples
