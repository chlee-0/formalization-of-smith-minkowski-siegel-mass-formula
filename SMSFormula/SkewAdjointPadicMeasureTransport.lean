import SMSFormula.SkewAdjointPadicMeasure
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Integral coordinate transport of the p-adic skew-adjoint measure

An element of `GL_d(Z_p)` acts on `Q_p^d`, preserves the unit coordinate
lattice, and has determinant of p-adic norm one. Conjugating this action by
the rationally transported skew-adjoint basis therefore preserves the
coordinate lattice and its normalized additive Haar measure.

This file remains on the additive skew-adjoint model. It does not construct a
measure on an orthogonal group or compare a group stabilizer volume.
-/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Operator

namespace Matrix

private theorem map_addHaarMeasure_eq_self_of_image_eq
    {V K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
    [NormedAddCommGroup V] [NormedSpace K V] [FiniteDimensional K V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    (C : TopologicalSpace.PositiveCompacts V) (e : V ≃L[K] V)
    (hC : e '' (C : Set V) = C) :
    Measure.map e (Measure.addHaarMeasure C) = Measure.addHaarMeasure C := by
  have hpre : e ⁻¹' (C : Set V) = C := by
    calc
      e ⁻¹' (C : Set V) = e ⁻¹' (e '' (C : Set V)) :=
        congrArg (fun s : Set V ↦ e ⁻¹' s) hC.symm
      _ = C := e.toEquiv.preimage_image _
  letI : Measure.IsAddHaarMeasure
      (Measure.map e (Measure.addHaarMeasure C)) :=
    e.isAddHaarMeasure_map _
  letI : SigmaFinite (Measure.addHaarMeasure C) := inferInstance
  letI : SigmaFinite (Measure.map e (Measure.addHaarMeasure C)) :=
    e.toHomeomorph.toMeasurableEquiv.sigmaFinite_map
  symm
  apply (Measure.addHaarMeasure_eq_iff C
    (Measure.map e (Measure.addHaarMeasure C))).2
  calc
    (Measure.map e (Measure.addHaarMeasure C)) C =
        Measure.addHaarMeasure C (e ⁻¹' (C : Set V)) :=
      Measure.map_apply e.continuous.measurable C.isCompact.measurableSet
    _ = Measure.addHaarMeasure C C :=
      congrArg (Measure.addHaarMeasure C) hpre
    _ = 1 := Measure.addHaarMeasure_self

variable {d : ℕ}

/-- The `Q_p`-linear coordinate automorphism obtained from an integral
matrix unit in `GL_d(Z_p)`. -/
def padicIntegralCoordinateAutomorphism (p : ℕ) [Fact (Nat.Prime p)]
    (U : GL (Fin d) ℤ_[p]) :
    (Fin d → ℚ_[p]) ≃L[ℚ_[p]] (Fin d → ℚ_[p]) :=
  ((GeneralLinearGroup.toLin
      (GeneralLinearGroup.map PadicInt.Coe.ringHom U)).toLinearEquiv).toContinuousLinearEquiv

theorem padicIntegralCoordinateAutomorphism_coe
    (p : ℕ) [Fact (Nat.Prime p)] (U : GL (Fin d) ℤ_[p])
    (z : Fin d → ℤ_[p]) :
    padicIntegralCoordinateAutomorphism p U (fun i ↦ (z i : ℚ_[p])) =
      fun i ↦
        ((GeneralLinearGroup.toLin U).toLinearEquiv z i : ℚ_[p]) := by
  funext i
  simp [padicIntegralCoordinateAutomorphism, Matrix.mulVec, dotProduct]

theorem padicIntegralCoordinateAutomorphism_image_unitLattice
    (p : ℕ) [Fact (Nat.Prime p)] (U : GL (Fin d) ℤ_[p]) :
    padicIntegralCoordinateAutomorphism p U ''
        Set.range (fun z : Fin d → ℤ_[p] ↦ fun i ↦ (z i : ℚ_[p])) =
      Set.range (fun z : Fin d → ℤ_[p] ↦ fun i ↦ (z i : ℚ_[p])) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
    exact ⟨(GeneralLinearGroup.toLin U).toLinearEquiv z,
      (padicIntegralCoordinateAutomorphism_coe p U z).symm⟩
  · rintro _ ⟨z, rfl⟩
    let z' := (GeneralLinearGroup.toLin U⁻¹).toLinearEquiv z
    refine ⟨fun i ↦ (z' i : ℚ_[p]), ⟨z', rfl⟩, ?_⟩
    rw [padicIntegralCoordinateAutomorphism_coe]
    have hz' : (GeneralLinearGroup.toLin U).toLinearEquiv z' = z := by
      have hinv :
          (GeneralLinearGroup.toLin U⁻¹).toLinearEquiv =
            (GeneralLinearGroup.toLin U).toLinearEquiv.symm := by
        rw [map_inv]
        exact LinearMap.GeneralLinearGroup.toLinearEquiv_inv _
      change (GeneralLinearGroup.toLin U).toLinearEquiv z' = z
      rw [show z' = (GeneralLinearGroup.toLin U).toLinearEquiv.symm z by
        simp only [z', hinv]]
      exact (GeneralLinearGroup.toLin U).toLinearEquiv.apply_symm_apply z
    exact congrArg (fun w : Fin d → ℤ_[p] ↦ fun i ↦ (w i : ℚ_[p])) hz'

theorem padicIntegralCoordinateAutomorphism_det_norm
    (p : ℕ) [Fact (Nat.Prime p)] (U : GL (Fin d) ℤ_[p]) :
    ‖((GeneralLinearGroup.map PadicInt.Coe.ringHom U :
        GL (Fin d) ℚ_[p]) : Matrix (Fin d) (Fin d) ℚ_[p]).det‖ = 1 := by
  change ‖((GeneralLinearGroup.det
    (GeneralLinearGroup.map PadicInt.Coe.ringHom U) : ℚ_[p]ˣ) : ℚ_[p])‖ = 1
  rw [GeneralLinearGroup.map_det]
  exact PadicInt.norm_units (GeneralLinearGroup.det U)

theorem padicIntegralCoordinateAutomorphism_linearMap_det_norm
    (p : ℕ) [Fact (Nat.Prime p)] (U : GL (Fin d) ℤ_[p]) :
    ‖LinearMap.det (padicIntegralCoordinateAutomorphism p U).toLinearMap‖ = 1 := by
  change ‖LinearMap.det (Matrix.toLin'
    (GeneralLinearGroup.map PadicInt.Coe.ringHom U :
      GL (Fin d) ℚ_[p]).1)‖ = 1
  rw [LinearMap.det_toLin']
  exact padicIntegralCoordinateAutomorphism_det_norm p U

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance skewAdjointPadicTransportIsTopologicalAddGroup
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    IsTopologicalAddGroup
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  Submodule.topologicalAddGroup _

local instance skewAdjointPadicTransportMeasurableSpace
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _

local instance skewAdjointPadicTransportBorelSpace
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩

local instance skewAdjointPadicTransportSecondCountableTopology
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    SecondCountableTopology
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule := by
  letI : SecondCountableTopology (ι → ℚ_[p]) :=
    TopologicalSpace.instSecondCountableTopologyForallOfCountable
  letI : SecondCountableTopology (Matrix ι ι ℚ_[p]) :=
    TopologicalSpace.instSecondCountableTopologyForallOfCountable
  exact TopologicalSpace.secondCountableTopology_induced
    (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule
    (Matrix ι ι ℚ_[p])
    ((↑) : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule → Matrix ι ι ℚ_[p])

/-- The integral coordinate automorphism conjugated to the p-adic
skew-adjoint model by the transported rational basis. -/
def skewAdjointPadicIntegralCoordinateAutomorphism
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (U : GL
      (Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F))) ℤ_[p]) :
    (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule ≃L[ℚ_[p]]
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ((skewAdjointPadicCoordinateEquiv F p).trans
    (padicIntegralCoordinateAutomorphism p U)).trans
      (skewAdjointPadicCoordinateEquiv F p).symm

theorem skewAdjointPadicIntegralCoordinateAutomorphism_det_norm
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (U : GL
      (Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F))) ℤ_[p]) :
    ‖LinearMap.det
      (skewAdjointPadicIntegralCoordinateAutomorphism F p U).toLinearMap‖ = 1 := by
  have hdet :
      LinearEquiv.det
          (skewAdjointPadicIntegralCoordinateAutomorphism F p U).toLinearEquiv =
        LinearEquiv.det (padicIntegralCoordinateAutomorphism p U).toLinearEquiv := by
    unfold skewAdjointPadicIntegralCoordinateAutomorphism
    exact LinearEquiv.det_conj _
      (skewAdjointPadicCoordinateEquiv F p).symm.toLinearEquiv
  have hval := congrArg (fun z : ℚ_[p]ˣ ↦ (z : ℚ_[p])) hdet
  have hval' :
      LinearMap.det
          (skewAdjointPadicIntegralCoordinateAutomorphism F p U).toLinearMap =
        LinearMap.det (padicIntegralCoordinateAutomorphism p U).toLinearMap := by
    simpa only [LinearEquiv.coe_det] using hval
  rw [hval']
  exact padicIntegralCoordinateAutomorphism_linearMap_det_norm p U

theorem skewAdjointPadicIntegralCoordinateAutomorphism_image_lattice
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (U : GL
      (Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F))) ℤ_[p]) :
    skewAdjointPadicIntegralCoordinateAutomorphism F p U ''
        (skewAdjointPadicCoordinateLattice F p :
          Set (skewAdjointMatricesLieSubalgebra
            (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) =
      skewAdjointPadicCoordinateLattice F p := by
  let c := skewAdjointPadicCoordinateEquiv F p
  let u := padicIntegralCoordinateAutomorphism p U
  let S := Set.range (fun z :
    Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F)) → ℤ_[p] ↦
      fun i ↦ (z i : ℚ_[p]))
  change (((c.trans u).trans c.symm) '' (c.symm '' S)) = c.symm '' S
  have hu : u '' S = S :=
    padicIntegralCoordinateAutomorphism_image_unitLattice p U
  apply Set.Subset.antisymm
  · rintro x ⟨_, ⟨q, hq, rfl⟩, rfl⟩
    refine ⟨u q, ?_, ?_⟩
    · rw [← hu]
      exact ⟨q, hq, rfl⟩
    · simp [c, u]
  · rintro x ⟨q, hq, rfl⟩
    have hq' : q ∈ u '' S := by rwa [hu]
    obtain ⟨q', hq'S, hq'eq⟩ := hq'
    refine ⟨c.symm q', ⟨q', hq'S, rfl⟩, ?_⟩
    simp [c, u, hq'eq]

set_option backward.isDefEq.respectTransparency false in
theorem map_skewAdjointPadicCoordinateMeasure_integralCoordinateAutomorphism
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (U : GL
      (Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F))) ℤ_[p]) :
    Measure.map (skewAdjointPadicIntegralCoordinateAutomorphism F p U)
        (skewAdjointPadicCoordinateMeasure F p) =
      skewAdjointPadicCoordinateMeasure F p := by
  letI := skewAdjointPadicTransportIsTopologicalAddGroup F p
  letI := skewAdjointPadicTransportMeasurableSpace F p
  letI := skewAdjointPadicTransportBorelSpace F p
  unfold skewAdjointPadicCoordinateMeasure
  exact map_addHaarMeasure_eq_self_of_image_eq
    (skewAdjointPadicCoordinateLattice F p)
    (skewAdjointPadicIntegralCoordinateAutomorphism F p U)
    (skewAdjointPadicIntegralCoordinateAutomorphism_image_lattice F p U)

/-- Integral changes of the transported p-adic skew-adjoint coordinates
preserve the normalized coordinate Haar measure. -/
theorem measurePreserving_skewAdjointPadicIntegralCoordinateAutomorphism
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (U : GL
      (Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F))) ℤ_[p]) :
    MeasurePreserving (skewAdjointPadicIntegralCoordinateAutomorphism F p U)
      (skewAdjointPadicCoordinateMeasure F p)
      (skewAdjointPadicCoordinateMeasure F p) := by
  letI := skewAdjointPadicTransportMeasurableSpace F p
  exact
    ⟨(skewAdjointPadicIntegralCoordinateAutomorphism F p U).continuous.measurable,
      map_skewAdjointPadicCoordinateMeasure_integralCoordinateAutomorphism F p U⟩

end Matrix
