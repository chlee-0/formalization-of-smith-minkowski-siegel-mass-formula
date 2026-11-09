import SMSFormula.RationalQuadraticIsometrySpinCandidateGeneralHaarModulus
import SMSFormula.SkewAdjointPadicMeasureGeneralTransport

/-!
# P-adic tangent Haar transport under an arbitrary rational isometry

The rational skew-adjoint equivalence attached to an arbitrary supplied
quadratic isometry is scalar-extended to every p-adic field.  Its matrix in
the fixed scalar-extended rational bases is unchanged.  Factoring it through
the normalized coordinate-lattice equivalence therefore gives the reciprocal
p-adic norm of the canonical rational tangent determinant.

No orthogonal-group chart, integral group locus, finite cylinder, or raw
normalization certificate is selected.
-/

noncomputable section

open PositiveDefiniteIntegralLattice MeasureTheory Matrix
open scoped Matrix Matrix.Norms.Operator ENNReal TensorProduct

namespace RationalQuadraticSpaceMatrix

variable {r s : ℕ}
variable (U : RationalQuadraticSpaceMatrix r)
variable (V : RationalQuadraticSpaceMatrix s)
variable (e : U.quadraticForm.IsometryEquiv V.quadraticForm)

local instance sourcePadicSkewAdjointIsTopologicalAddGroup
    (p : ℕ) [Fact (Nat.Prime p)] :
    IsTopologicalAddGroup
      (skewAdjointMatricesLieSubalgebra
        (U.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  Submodule.topologicalAddGroup _

local instance targetPadicSkewAdjointIsTopologicalAddGroup
    (p : ℕ) [Fact (Nat.Prime p)] :
    IsTopologicalAddGroup
      (skewAdjointMatricesLieSubalgebra
        (V.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  Submodule.topologicalAddGroup _

local instance sourcePadicSkewAdjointMeasurableSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (U.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _

local instance sourcePadicSkewAdjointBorelSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (U.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩

local instance targetPadicSkewAdjointMeasurableSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (V.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _

local instance targetPadicSkewAdjointBorelSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (V.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩

local instance sourcePadicSkewAdjointSecondCountableTopology
    (p : ℕ) [Fact (Nat.Prime p)] :
    SecondCountableTopology
      (skewAdjointMatricesLieSubalgebra
        (U.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule := by
  letI : SecondCountableTopology (Fin r → ℚ_[p]) :=
    TopologicalSpace.instSecondCountableTopologyForallOfCountable
  letI : SecondCountableTopology (Matrix (Fin r) (Fin r) ℚ_[p]) :=
    TopologicalSpace.instSecondCountableTopologyForallOfCountable
  exact TopologicalSpace.secondCountableTopology_induced _ _
    ((↑) : (skewAdjointMatricesLieSubalgebra
      (U.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule →
        Matrix (Fin r) (Fin r) ℚ_[p])

local instance targetPadicSkewAdjointSecondCountableTopology
    (p : ℕ) [Fact (Nat.Prime p)] :
    SecondCountableTopology
      (skewAdjointMatricesLieSubalgebra
        (V.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule := by
  letI : SecondCountableTopology (Fin s → ℚ_[p]) :=
    TopologicalSpace.instSecondCountableTopologyForallOfCountable
  letI : SecondCountableTopology (Matrix (Fin s) (Fin s) ℚ_[p]) :=
    TopologicalSpace.instSecondCountableTopologyForallOfCountable
  exact TopologicalSpace.secondCountableTopology_induced _ _
    ((↑) : (skewAdjointMatricesLieSubalgebra
      (V.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule →
        Matrix (Fin s) (Fin s) ℚ_[p])

/-- Scalar extension of the rational tangent equivalence to the native
p-adic skew-adjoint carriers. -/
def rationalIsometryPadicSkewAdjointLinearEquiv
    (p : ℕ) [Fact (Nat.Prime p)] :
    (skewAdjointMatricesLieSubalgebra
        (U.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule ≃ₗ[ℚ_[p]]
      (skewAdjointMatricesLieSubalgebra
        (V.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  (skewAdjointScalarExtensionEquiv (K := ℚ_[p]) U.pairingMatrix).symm ≪≫ₗ
    LinearEquiv.baseChange ℚ ℚ_[p] _ _
      (rationalIsometrySkewAdjointLinearEquiv U V e) ≪≫ₗ
    skewAdjointScalarExtensionEquiv (K := ℚ_[p]) V.pairingMatrix

/-- The p-adic scalar extension is continuous for the existing native
finite-dimensional topologies. -/
def rationalIsometryPadicSkewAdjointContinuousLinearEquiv
    (p : ℕ) [Fact (Nat.Prime p)] :
    (skewAdjointMatricesLieSubalgebra
        (U.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule ≃L[ℚ_[p]]
      (skewAdjointMatricesLieSubalgebra
        (V.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  (rationalIsometryPadicSkewAdjointLinearEquiv U V e p).toContinuousLinearEquiv

/-- On scalar-extended rational tangent vectors, the p-adic map is literally
scalar extension of rational conjugation. -/
@[simp]
theorem rationalIsometryPadicSkewAdjointLinearEquiv_scalarExtension
    (p : ℕ) [Fact (Nat.Prime p)] (a : ℚ_[p])
    (X : skewAdjointMatricesLieSubalgebra U.pairingMatrix) :
    rationalIsometryPadicSkewAdjointLinearEquiv U V e p
        (skewAdjointScalarExtensionEquiv (K := ℚ_[p]) U.pairingMatrix
          (a ⊗ₜ[ℚ] X)) =
      skewAdjointScalarExtensionEquiv (K := ℚ_[p]) V.pairingMatrix
        (a ⊗ₜ[ℚ] rationalIsometrySkewAdjointLinearEquiv U V e X) := by
  change skewAdjointScalarExtensionEquiv (K := ℚ_[p]) V.pairingMatrix
      (LinearEquiv.baseChange ℚ ℚ_[p] _ _
        (rationalIsometrySkewAdjointLinearEquiv U V e)
        ((skewAdjointScalarExtensionEquiv (K := ℚ_[p]) U.pairingMatrix).symm
          (skewAdjointScalarExtensionEquiv (K := ℚ_[p]) U.pairingMatrix
            (a ⊗ₜ[ℚ] X)))) = _
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.baseChange_tmul]

/-- The fixed source p-adic tangent basis, reindexed by the dimension equality
furnished by the rational tangent equivalence. -/
def rationalIsometryPadicSkewAdjointSourceBasis
    (p : ℕ) [Fact (Nat.Prime p)] :
    Module.Basis
      (Fin (Module.finrank ℚ
        (skewAdjointMatricesLieSubalgebra V.pairingMatrix)))
      ℚ_[p]
      (skewAdjointMatricesLieSubalgebra
        (U.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  (skewAdjointScalarExtensionFinBasis (K := ℚ_[p]) U.pairingMatrix).reindex
    (Fin.castOrderIso
      (rationalIsometrySkewAdjointLinearEquiv U V e).finrank_eq)

/-- Mapping the reindexed source basis gives the scalar extension of the
rationally transported basis. -/
theorem rationalIsometryPadicSkewAdjointSourceBasis_map
    (p : ℕ) [Fact (Nat.Prime p)] :
    (rationalIsometryPadicSkewAdjointSourceBasis U V e p).map
        (rationalIsometryPadicSkewAdjointLinearEquiv U V e p) =
      skewAdjointScalarExtensionBasis (K := ℚ_[p]) V.pairingMatrix
        (rationalIsometrySkewAdjointTransportedFinBasis U V e) := by
  apply DFunLike.ext _ _
  intro i
  have hsource :
      rationalIsometryPadicSkewAdjointSourceBasis U V e p i =
        skewAdjointScalarExtensionEquiv (K := ℚ_[p]) U.pairingMatrix
          (1 ⊗ₜ[ℚ] Matrix.skewAdjointFinBasis U.pairingMatrix
            ((Fin.castOrderIso
              (rationalIsometrySkewAdjointLinearEquiv U V e).finrank_eq).symm
                i)) := by
    calc
      rationalIsometryPadicSkewAdjointSourceBasis U V e p i =
          skewAdjointScalarExtensionFinBasis (K := ℚ_[p]) U.pairingMatrix
            ((Fin.castOrderIso
              (rationalIsometrySkewAdjointLinearEquiv U V e).finrank_eq).symm
                i) := Module.Basis.reindex_apply _ _ _
      _ = _ := by
        apply Subtype.ext
        rw [skewAdjointScalarExtensionFinBasis,
          coe_skewAdjointScalarExtensionBasis_apply,
          coe_skewAdjointScalarExtensionEquiv_tmul]
        simp
  rw [Module.Basis.map_apply, hsource,
    rationalIsometryPadicSkewAdjointLinearEquiv_scalarExtension]
  calc
    skewAdjointScalarExtensionEquiv (K := ℚ_[p]) V.pairingMatrix
        (1 ⊗ₜ[ℚ]
          rationalIsometrySkewAdjointLinearEquiv U V e
            (Matrix.skewAdjointFinBasis U.pairingMatrix
              ((Fin.castOrderIso
                (rationalIsometrySkewAdjointLinearEquiv U V e).finrank_eq).symm
                  i))) =
      skewAdjointScalarExtensionEquiv (K := ℚ_[p]) V.pairingMatrix
        (1 ⊗ₜ[ℚ]
          rationalIsometrySkewAdjointTransportedFinBasis U V e i) := by
            congr 2
            simp only [rationalIsometrySkewAdjointTransportedFinBasis,
              Module.Basis.reindex_apply, Module.Basis.map_apply]
            congr 1
    _ = skewAdjointScalarExtensionBasis (K := ℚ_[p]) V.pairingMatrix
        (rationalIsometrySkewAdjointTransportedFinBasis U V e) i := by
          apply Subtype.ext
          rw [coe_skewAdjointScalarExtensionEquiv_tmul,
            coe_skewAdjointScalarExtensionBasis_apply]
          simp

/-- The p-adic determinant in the fixed scalar-extended bases is the literal
p-adic image of the rational modulus. -/
theorem rationalIsometryPadicSkewAdjointDet_apply
    (p : ℕ) [Fact (Nat.Prime p)] :
    (skewAdjointScalarExtensionFinBasis (K := ℚ_[p]) V.pairingMatrix).det
        ((rationalIsometryPadicSkewAdjointSourceBasis U V e p).map
          (rationalIsometryPadicSkewAdjointLinearEquiv U V e p)) =
      algebraMap ℚ ℚ_[p] (rationalIsometrySkewAdjointDetScalar U V e) := by
  rw [rationalIsometryPadicSkewAdjointSourceBasis_map,
    rationalIsometrySkewAdjointDetScalar]
  have hpoint (j : Fin (Module.finrank ℚ
      (skewAdjointMatricesLieSubalgebra V.pairingMatrix))) :
      skewAdjointScalarExtensionBasis (K := ℚ_[p]) V.pairingMatrix
          (rationalIsometrySkewAdjointTransportedFinBasis U V e) j =
        skewAdjointScalarExtensionEquiv (K := ℚ_[p]) V.pairingMatrix
          (1 ⊗ₜ[ℚ]
            rationalIsometrySkewAdjointTransportedFinBasis U V e j) := by
    apply Subtype.ext
    rw [coe_skewAdjointScalarExtensionBasis_apply (Q := ℚ) (K := ℚ_[p]),
      coe_skewAdjointScalarExtensionEquiv_tmul (Q := ℚ) (K := ℚ_[p])]
    simp
  have hdet := skewAdjointScalarExtensionBasis_det_apply
      (Q := ℚ) (K := ℚ_[p]) V.pairingMatrix
      (Matrix.skewAdjointFinBasis V.pairingMatrix)
      (rationalIsometrySkewAdjointTransportedFinBasis U V e)
  change (skewAdjointScalarExtensionFinBasis (K := ℚ_[p]) V.pairingMatrix).det
      (fun j => skewAdjointScalarExtensionBasis (K := ℚ_[p]) V.pairingMatrix
        (rationalIsometrySkewAdjointTransportedFinBasis U V e) j) = _
  rw [show
    (fun j => skewAdjointScalarExtensionBasis (K := ℚ_[p]) V.pairingMatrix
      (rationalIsometrySkewAdjointTransportedFinBasis U V e) j) =
    (fun j => skewAdjointScalarExtensionEquiv (K := ℚ_[p]) V.pairingMatrix
      (1 ⊗ₜ[ℚ]
        rationalIsometrySkewAdjointTransportedFinBasis U V e j)) by
      funext j
      exact hpoint j]
  exact hdet

/-- The normalized auxiliary equivalence which preserves fixed p-adic
coordinates after the forced tangent-basis reindexing. -/
def rationalIsometryPadicFixedCoordinateEquiv
    (p : ℕ) [Fact (Nat.Prime p)] :
    (skewAdjointMatricesLieSubalgebra
        (U.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule ≃L[ℚ_[p]]
      (skewAdjointMatricesLieSubalgebra
        (V.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  (rationalIsometryPadicSkewAdjointSourceBasis U V e p).equivFun
      |>.toContinuousLinearEquiv |>.trans
    (skewAdjointPadicCoordinateEquiv V.pairingMatrix p).symm

@[simp]
theorem rationalIsometryPadicFixedCoordinateEquiv_coordinate_apply
    (p : ℕ) [Fact (Nat.Prime p)]
    (X : (skewAdjointMatricesLieSubalgebra
      (U.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
    skewAdjointPadicCoordinateEquiv V.pairingMatrix p
        (rationalIsometryPadicFixedCoordinateEquiv U V e p X) =
      (rationalIsometryPadicSkewAdjointSourceBasis U V e p).equivFun X := by
  exact (skewAdjointPadicCoordinateEquiv V.pairingMatrix p).apply_symm_apply _

/-- Reindexed source coordinates are the original fixed source coordinates at
the inverse forced index. -/
theorem rationalIsometryPadicSkewAdjointSourceBasis_equivFun_apply
    (p : ℕ) [Fact (Nat.Prime p)]
    (X : (skewAdjointMatricesLieSubalgebra
      (U.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule)
    (i : Fin (Module.finrank ℚ
      (skewAdjointMatricesLieSubalgebra V.pairingMatrix))) :
    (rationalIsometryPadicSkewAdjointSourceBasis U V e p).equivFun X i =
      skewAdjointPadicCoordinateEquiv U.pairingMatrix p X
        ((Fin.castOrderIso
          (rationalIsometrySkewAdjointLinearEquiv U V e).finrank_eq).symm i) := by
  let b := skewAdjointScalarExtensionFinBasis (K := ℚ_[p]) U.pairingMatrix
  let h := Fin.castOrderIso
    (rationalIsometrySkewAdjointLinearEquiv U V e).finrank_eq
  have hrepr := Module.Basis.repr_reindex b X h.toEquiv
  have hcoord := congrArg
    (fun c : Fin (Module.finrank ℚ
      (skewAdjointMatricesLieSubalgebra V.pairingMatrix)) →₀ ℚ_[p] => c i) hrepr
  change (b.reindex h).equivFun X i = b.equivFun X (h.symm i)
  simp only [Module.Basis.equivFun_apply]
  simpa only [Finsupp.mapDomain_equiv_apply, Equiv.apply_symm_apply] using hcoord

/-- The auxiliary fixed-coordinate equivalence maps the normalized source
unit-coordinate lattice exactly onto the target lattice. -/
theorem rationalIsometryPadicFixedCoordinateEquiv_image_coordinateLattice
    (p : ℕ) [Fact (Nat.Prime p)] :
    rationalIsometryPadicFixedCoordinateEquiv U V e p ''
        (skewAdjointPadicCoordinateLattice U.pairingMatrix p : Set _) =
      (skewAdjointPadicCoordinateLattice V.pairingMatrix p : Set _) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨X, hX, rfl⟩
    refine (mem_skewAdjointPadicCoordinateLattice_iff
      V.pairingMatrix p _).2 ?_
    have hX' := (mem_skewAdjointPadicCoordinateLattice_iff
      U.pairingMatrix p X).1 hX
    intro i
    rw [rationalIsometryPadicFixedCoordinateEquiv_coordinate_apply,
      rationalIsometryPadicSkewAdjointSourceBasis_equivFun_apply]
    exact hX' _
  · intro Y hY
    refine ⟨(rationalIsometryPadicFixedCoordinateEquiv U V e p).symm Y,
      ?_, by simp⟩
    refine (mem_skewAdjointPadicCoordinateLattice_iff
      U.pairingMatrix p _).2 ?_
    have hY' := (mem_skewAdjointPadicCoordinateLattice_iff
      V.pairingMatrix p Y).1 hY
    intro j
    let h := Fin.castOrderIso
      (rationalIsometrySkewAdjointLinearEquiv U V e).finrank_eq
    have hcoord :
        skewAdjointPadicCoordinateEquiv V.pairingMatrix p Y (h j) =
          skewAdjointPadicCoordinateEquiv U.pairingMatrix p
            ((rationalIsometryPadicFixedCoordinateEquiv U V e p).symm Y) j := by
      calc
        _ = skewAdjointPadicCoordinateEquiv V.pairingMatrix p
              (rationalIsometryPadicFixedCoordinateEquiv U V e p
                ((rationalIsometryPadicFixedCoordinateEquiv U V e p).symm Y))
              (h j) := by simp
        _ = (rationalIsometryPadicSkewAdjointSourceBasis U V e p).equivFun
              ((rationalIsometryPadicFixedCoordinateEquiv U V e p).symm Y)
              (h j) := by
                rw [rationalIsometryPadicFixedCoordinateEquiv_coordinate_apply]
        _ = skewAdjointPadicCoordinateEquiv U.pairingMatrix p
              ((rationalIsometryPadicFixedCoordinateEquiv U V e p).symm Y) j := by
                rw [rationalIsometryPadicSkewAdjointSourceBasis_equivFun_apply]
                simp [h]
    rw [← hcoord]
    exact hY' (h j)

set_option synthInstance.maxHeartbeats 200000 in
/-- Literal transport of the fixed-coordinate p-adic Haar by the normalized
auxiliary equivalence. -/
theorem map_rationalIsometryPadicFixedCoordinateMeasure
    (p : ℕ) [Fact (Nat.Prime p)] :
    Measure.map (rationalIsometryPadicFixedCoordinateEquiv U V e p)
        (skewAdjointPadicCoordinateMeasure U.pairingMatrix p) =
      skewAdjointPadicCoordinateMeasure V.pairingMatrix p := by
  let h := rationalIsometryPadicFixedCoordinateEquiv U V e p
  let C := skewAdjointPadicCoordinateLattice U.pairingMatrix p
  let D := skewAdjointPadicCoordinateLattice V.pairingMatrix p
  let mu := skewAdjointPadicCoordinateMeasure U.pairingMatrix p
  have himage : h '' (C : Set _) = (D : Set _) :=
    rationalIsometryPadicFixedCoordinateEquiv_image_coordinateLattice U V e p
  have hpre : h ⁻¹' (D : Set _) = (C : Set _) := by
    calc
      h ⁻¹' (D : Set _) = h ⁻¹' (h '' (C : Set _)) :=
        congrArg (fun t : Set _ => h ⁻¹' t) himage.symm
      _ = C := h.toEquiv.preimage_image _
  letI : Measure.IsAddHaarMeasure mu :=
    skewAdjointPadicCoordinateMeasure_isAddHaarMeasure U.pairingMatrix p
  letI : Measure.IsAddHaarMeasure (Measure.map h mu) :=
    h.isAddHaarMeasure_map mu
  letI : LocallyCompactSpace
      (skewAdjointMatricesLieSubalgebra
        (U.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
    (skewAdjointPadicCoordinateEquiv U.pairingMatrix p).toHomeomorph
      |>.isClosedEmbedding.locallyCompactSpace
  letI : SigmaCompactSpace
      (skewAdjointMatricesLieSubalgebra
        (U.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule := by
    infer_instance
  letI : SigmaFinite mu := by
    dsimp [mu]
    unfold skewAdjointPadicCoordinateMeasure
    exact Measure.sigmaFinite_addHaarMeasure
      (K₀ := skewAdjointPadicCoordinateLattice U.pairingMatrix p)
  letI : SigmaFinite (Measure.map h mu) :=
    h.toHomeomorph.toMeasurableEquiv.sigmaFinite_map
  have hnormalized : Measure.map h mu D = 1 := by
    rw [Measure.map_apply h.continuous.measurable D.isCompact.measurableSet]
    rw [hpre]
    exact skewAdjointPadicCoordinateMeasure_lattice U.pairingMatrix p
  have hunique : Measure.addHaarMeasure D = Measure.map h mu :=
    (Measure.addHaarMeasure_eq_iff D (Measure.map h mu)).2 hnormalized
  change Measure.map h mu = skewAdjointPadicCoordinateMeasure V.pairingMatrix p
  unfold skewAdjointPadicCoordinateMeasure
  exact hunique.symm

/-- The normalized auxiliary equivalence sends the reindexed source basis to
the fixed target basis. -/
theorem rationalIsometryPadicFixedCoordinateEquiv_apply_sourceBasis
    (p : ℕ) [Fact (Nat.Prime p)]
    (i : Fin (Module.finrank ℚ
      (skewAdjointMatricesLieSubalgebra V.pairingMatrix))) :
    rationalIsometryPadicFixedCoordinateEquiv U V e p
        (rationalIsometryPadicSkewAdjointSourceBasis U V e p i) =
      skewAdjointScalarExtensionFinBasis (K := ℚ_[p]) V.pairingMatrix i := by
  apply (skewAdjointPadicCoordinateEquiv V.pairingMatrix p).injective
  rw [rationalIsometryPadicFixedCoordinateEquiv_coordinate_apply]
  ext j
  change
    (rationalIsometryPadicSkewAdjointSourceBasis U V e p).equivFun
        (rationalIsometryPadicSkewAdjointSourceBasis U V e p i) j =
      (skewAdjointScalarExtensionFinBasis (K := ℚ_[p]) V.pairingMatrix).equivFun
        (skewAdjointScalarExtensionFinBasis (K := ℚ_[p]) V.pairingMatrix i) j
  rw [Module.Basis.equivFun_self, Module.Basis.equivFun_self]

/-- The actual p-adic tangent map, expressed as a target-carrier automorphism
after removing the normalized fixed-coordinate equivalence. -/
def rationalIsometryPadicSkewAdjointAutomorphism
    (p : ℕ) [Fact (Nat.Prime p)] :
    (skewAdjointMatricesLieSubalgebra
        (V.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule ≃L[ℚ_[p]]
      (skewAdjointMatricesLieSubalgebra
        (V.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  (rationalIsometryPadicFixedCoordinateEquiv U V e p).symm.trans
    (rationalIsometryPadicSkewAdjointContinuousLinearEquiv U V e p)

set_option maxRecDepth 2048 in
/-- The residual target automorphism has determinant equal to the p-adic image
of the canonical rational tangent modulus. -/
theorem rationalIsometryPadicSkewAdjointAutomorphism_det
    (p : ℕ) [Fact (Nat.Prime p)] :
    LinearMap.det
        (rationalIsometryPadicSkewAdjointAutomorphism U V e p).toLinearMap =
      algebraMap ℚ ℚ_[p] (rationalIsometrySkewAdjointDetScalar U V e) := by
  let b := skewAdjointScalarExtensionFinBasis (K := ℚ_[p]) V.pairingMatrix
  let c := rationalIsometryPadicSkewAdjointSourceBasis U V e p
  let h := rationalIsometryPadicFixedCoordinateEquiv U V e p
  let A := rationalIsometryPadicSkewAdjointAutomorphism U V e p
  have hA : ∀ i, A (b i) =
      rationalIsometryPadicSkewAdjointContinuousLinearEquiv U V e p (c i) := by
    intro i
    change rationalIsometryPadicSkewAdjointContinuousLinearEquiv U V e p
        (h.symm (b i)) = _
    have hb : h.symm (b i) = c i := by
      apply h.injective
      rw [h.apply_symm_apply]
      exact (rationalIsometryPadicFixedCoordinateEquiv_apply_sourceBasis
        U V e p i).symm
    exact congrArg
      (rationalIsometryPadicSkewAdjointContinuousLinearEquiv U V e p) hb
  calc
    LinearMap.det A.toLinearMap = b.det (fun i => A (b i)) := by
      symm
      have hcomp := Module.Basis.det_comp b A.toLinearMap b
      simpa only [Module.Basis.det_self, mul_one] using hcomp
    _ = b.det (c.map
        (rationalIsometryPadicSkewAdjointLinearEquiv U V e p)) := by
      congr 1
      funext i
      rw [Module.Basis.map_apply]
      exact hA i
    _ = algebraMap ℚ ℚ_[p]
        (rationalIsometrySkewAdjointDetScalar U V e) :=
      rationalIsometryPadicSkewAdjointDet_apply U V e p

set_option maxRecDepth 2048 in
/-- The arbitrary-isometry p-adic tangent map transports the fixed coordinate
Haar by the reciprocal norm of the canonical rational tangent modulus. -/
theorem map_rationalIsometryPadicSkewAdjointCoordinateMeasure
    (p : ℕ) [Fact (Nat.Prime p)] :
    Measure.map
        (rationalIsometryPadicSkewAdjointContinuousLinearEquiv U V e p)
        (skewAdjointPadicCoordinateMeasure U.pairingMatrix p) =
      ‖algebraMap ℚ ℚ_[p]
        (rationalIsometrySkewAdjointDetScalar U V e)‖₊⁻¹ •
        skewAdjointPadicCoordinateMeasure V.pairingMatrix p := by
  let h := rationalIsometryPadicFixedCoordinateEquiv U V e p
  let A := rationalIsometryPadicSkewAdjointAutomorphism U V e p
  let mu := skewAdjointPadicCoordinateMeasure U.pairingMatrix p
  let nu := skewAdjointPadicCoordinateMeasure V.pairingMatrix p
  have he : Measure.map h mu = nu :=
    map_rationalIsometryPadicFixedCoordinateMeasure U V e p
  have hA := map_skewAdjointPadicCoordinateMeasure_continuousLinearEquiv_det
    V.pairingMatrix p A
  have hfun : (fun y => A (h y)) =
      rationalIsometryPadicSkewAdjointContinuousLinearEquiv U V e p := by
    funext y
    simp [A, h, rationalIsometryPadicSkewAdjointAutomorphism]
  have hcomp : A ∘ h =
      rationalIsometryPadicSkewAdjointContinuousLinearEquiv U V e p := by
    funext y
    exact congrFun hfun y
  calc
    Measure.map
        (rationalIsometryPadicSkewAdjointContinuousLinearEquiv U V e p) mu =
      Measure.map A (Measure.map h mu) := by
        rw [Measure.map_map A.continuous.measurable h.continuous.measurable]
        rw [hcomp]
    _ = Measure.map A nu := by rw [he]
    _ = ‖LinearMap.det A.toLinearMap‖₊⁻¹ • nu := hA
    _ = _ := by
      rw [rationalIsometryPadicSkewAdjointAutomorphism_det]

end RationalQuadraticSpaceMatrix

end
