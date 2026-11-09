import SMSFormula.SkewAdjointPadicElementaryCoordinateMeasure

/-!
# Transport between the form-adapted and fixed-basis p-adic coordinate measures

The continuous basis change obtained by reading form-adapted coordinates in
the fixed scalar-extended basis maps the form-adapted integral-coordinate
lattice exactly onto the fixed-basis integral-coordinate lattice.  Consequently
it pushes the form-adapted normalized additive Haar measure to the fixed-basis
coordinate measure.

This is a transport between two coordinate normalizations.  The file
does not compute the basis-change determinant or identify a scalar multiple
between the two measures on the same carrier.
-/

noncomputable section

open MeasureTheory

namespace Matrix

variable {n : ℕ}

local instance skewAdjointPadicElementaryTransportIsTopologicalAddGroup
    (p : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℚ) :
    IsTopologicalAddGroup
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  Submodule.topologicalAddGroup _

local instance skewAdjointPadicElementaryTransportMeasurableSpace
    (p : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _

local instance skewAdjointPadicElementaryTransportBorelSpace
    (p : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩

local instance skewAdjointPadicElementaryTransportSecondCountableTopology
    (p : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℚ) :
    SecondCountableTopology
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule := by
  letI : SecondCountableTopology (Fin n → ℚ_[p]) :=
    TopologicalSpace.instSecondCountableTopologyForallOfCountable
  letI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℚ_[p]) :=
    TopologicalSpace.instSecondCountableTopologyForallOfCountable
  exact TopologicalSpace.secondCountableTopology_induced
    (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule
    (Matrix (Fin n) (Fin n) ℚ_[p])
    ((↑) : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule →
        Matrix (Fin n) (Fin n) ℚ_[p])

/-- The continuous basis change which sends each form-adapted p-adic basis
vector to the same-index vector of the fixed scalar-extended basis. -/
def skewAdjointFormElementaryToFixedPadicBasisChange
    (p : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) :
    (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule ≃L[ℚ_[p]]
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  (skewAdjointFormElementaryPadicCoordinateEquiv p F hF hdet).trans
    (skewAdjointPadicCoordinateEquiv F p).symm

/-- Fixed coordinates after the basis change are literally the original
form-adapted coordinates. -/
@[simp]
theorem skewAdjointPadicCoordinateEquiv_formElementaryToFixedBasisChange
    (p : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0)
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
    skewAdjointPadicCoordinateEquiv F p
        (skewAdjointFormElementaryToFixedPadicBasisChange
          p F hF hdet x) =
      skewAdjointFormElementaryPadicCoordinateEquiv p F hF hdet x := by
  exact (skewAdjointPadicCoordinateEquiv F p).apply_symm_apply _

/-- The basis change has the advertised value on every form-adapted basis
vector. -/
theorem skewAdjointFormElementaryToFixedPadicBasisChange_apply_basis
    (p : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0)
    (j : Fin (Module.finrank ℚ
      (skewAdjointMatricesLieSubalgebra F))) :
    skewAdjointFormElementaryToFixedPadicBasisChange p F hF hdet
        (skewAdjointFormElementaryPadicFinBasis p F hF hdet j) =
      skewAdjointScalarExtensionFinBasis (K := ℚ_[p]) F j := by
  apply (skewAdjointPadicCoordinateEquiv F p).injective
  rw [skewAdjointPadicCoordinateEquiv_formElementaryToFixedBasisChange]
  ext i
  change
    (skewAdjointFormElementaryPadicFinBasis
      p F hF hdet).equivFun
        (skewAdjointFormElementaryPadicFinBasis p F hF hdet j) i =
      (skewAdjointScalarExtensionFinBasis
        (K := ℚ_[p]) F).equivFun
          (skewAdjointScalarExtensionFinBasis (K := ℚ_[p]) F j) i
  rw [Module.Basis.equivFun_self, Module.Basis.equivFun_self]

/-- The basis change maps the form-adapted integral-coordinate lattice onto
the fixed-basis integral-coordinate lattice. -/
theorem skewAdjointFormElementaryToFixedPadicBasisChange_image_lattice
    (p : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) :
    skewAdjointFormElementaryToFixedPadicBasisChange p F hF hdet ''
        (skewAdjointFormElementaryPadicCoordinateLattice
          p F hF hdet :
            Set (skewAdjointMatricesLieSubalgebra
              (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) =
      (skewAdjointPadicCoordinateLattice F p :
        Set (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    refine (mem_skewAdjointPadicCoordinateLattice_iff F p _).2 ?_
    have hx' :=
      (mem_skewAdjointFormElementaryPadicCoordinateLattice_iff
        p F hF hdet x).1 hx
    intro i
    simpa only [
      skewAdjointPadicCoordinateEquiv_formElementaryToFixedBasisChange]
      using hx' i
  · intro y hy
    refine
      ⟨(skewAdjointFormElementaryToFixedPadicBasisChange
          p F hF hdet).symm y, ?_, by simp⟩
    refine
      (mem_skewAdjointFormElementaryPadicCoordinateLattice_iff
        p F hF hdet _).2 ?_
    have hy' := (mem_skewAdjointPadicCoordinateLattice_iff F p y).1 hy
    intro i
    rw [←
      skewAdjointPadicCoordinateEquiv_formElementaryToFixedBasisChange
        p F hF hdet]
    simpa using hy' i

/-- Pushforward of the form-adapted normalized coordinate measure is the
fixed-basis normalized coordinate measure. -/
theorem map_skewAdjointFormElementaryPadicCoordinateMeasure_basisChange
    (p : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) :
    Measure.map
        (skewAdjointFormElementaryToFixedPadicBasisChange p F hF hdet)
        (skewAdjointFormElementaryPadicCoordinateMeasure p F hF hdet) =
      skewAdjointPadicCoordinateMeasure F p := by
  let e := skewAdjointFormElementaryToFixedPadicBasisChange p F hF hdet
  let C := skewAdjointFormElementaryPadicCoordinateLattice p F hF hdet
  let D := skewAdjointPadicCoordinateLattice F p
  let μ := skewAdjointFormElementaryPadicCoordinateMeasure p F hF hdet
  have himage : e '' (C : Set _) = (D : Set _) :=
    skewAdjointFormElementaryToFixedPadicBasisChange_image_lattice
      p F hF hdet
  have hpre : e ⁻¹' (D : Set _) = (C : Set _) := by
    calc
      e ⁻¹' (D : Set _) = e ⁻¹' (e '' (C : Set _)) :=
        congrArg (fun s : Set _ ↦ e ⁻¹' s) himage.symm
      _ = C := e.toEquiv.preimage_image _
  letI : Measure.IsAddHaarMeasure μ :=
    skewAdjointFormElementaryPadicCoordinateMeasure_isAddHaarMeasure
      p F hF hdet
  letI : Measure.IsAddHaarMeasure (Measure.map e μ) :=
    e.isAddHaarMeasure_map μ
  letI : SigmaFinite μ := by
    dsimp [μ]
    unfold skewAdjointFormElementaryPadicCoordinateMeasure
    infer_instance
  letI : SigmaFinite (Measure.map e μ) :=
    e.toHomeomorph.toMeasurableEquiv.sigmaFinite_map
  have hnormalized : Measure.map e μ D = 1 := by
    rw [Measure.map_apply e.continuous.measurable D.isCompact.measurableSet]
    rw [hpre]
    exact
      skewAdjointFormElementaryPadicCoordinateMeasure_lattice
        p F hF hdet
  have hunique : Measure.addHaarMeasure D = Measure.map e μ :=
    (Measure.addHaarMeasure_eq_iff D (Measure.map e μ)).2 hnormalized
  change Measure.map e μ = skewAdjointPadicCoordinateMeasure F p
  unfold skewAdjointPadicCoordinateMeasure
  exact hunique.symm

end Matrix
