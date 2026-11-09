import SMSFormula.RationalQuadraticIsometryGeneralSpinHaarModulus
import SMSFormula.SkewAdjointPadicMeasureGeneralTransport

/-!
# P-adic tangent Haar transport for an anisotropic presentation

The rational skew-adjoint presentation equivalence is extended to every
native p-adic tangent carrier.  Its action on the fixed scalar-extended
rational bases and its determinant are computed literally.  The forced basis
reindexing is shown to preserve the normalized unit-coordinate lattice and
additive Haar, after which the actual presentation map is proved to scale the
fixed coordinate Haar by the reciprocal p-adic norm of the single rational
presentation modulus.  No p-adic group chart, finite directed cylinder, or
restricted-product measure is evaluated in this file.
-/

noncomputable section

open PositiveDefiniteIntegralLattice MeasureTheory Matrix
open scoped Matrix Matrix.Norms.Operator ENNReal TensorProduct

namespace RationalQuadraticSpaceMatrix
namespace AnisotropicComplementPresentation

variable {n m : ℕ}
variable {V : RationalQuadraticSpaceMatrix n} {x : Fin n → ℚ}
variable (P : V.AnisotropicComplementPresentation x m)

local instance blockPadicSkewAdjointIsTopologicalAddGroup
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (p : ℕ) [Fact (Nat.Prime p)] :
    IsTopologicalAddGroup
      (skewAdjointMatricesLieSubalgebra
        ((P.blockSpace hx).pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  Submodule.topologicalAddGroup _

local instance ambientPadicSkewAdjointIsTopologicalAddGroup
    (p : ℕ) [Fact (Nat.Prime p)] :
    IsTopologicalAddGroup
      (skewAdjointMatricesLieSubalgebra
        (V.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  Submodule.topologicalAddGroup _

local instance blockPadicSkewAdjointMeasurableSpace
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        ((P.blockSpace hx).pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _

local instance blockPadicSkewAdjointBorelSpace
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        ((P.blockSpace hx).pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩

local instance ambientPadicSkewAdjointMeasurableSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (V.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _

local instance ambientPadicSkewAdjointBorelSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (V.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩

local instance blockPadicSkewAdjointSecondCountableTopology
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (p : ℕ) [Fact (Nat.Prime p)] :
    SecondCountableTopology
      (skewAdjointMatricesLieSubalgebra
        ((P.blockSpace hx).pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule := by
  letI : SecondCountableTopology (Fin (m + 1) → ℚ_[p]) :=
    TopologicalSpace.instSecondCountableTopologyForallOfCountable
  letI : SecondCountableTopology (Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ_[p]) :=
    TopologicalSpace.instSecondCountableTopologyForallOfCountable
  exact TopologicalSpace.secondCountableTopology_induced _ _
    ((↑) : (skewAdjointMatricesLieSubalgebra
      ((P.blockSpace hx).pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule →
        Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ_[p])

local instance ambientPadicSkewAdjointSecondCountableTopology
    (p : ℕ) [Fact (Nat.Prime p)] :
    SecondCountableTopology
      (skewAdjointMatricesLieSubalgebra
        (V.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule := by
  letI : SecondCountableTopology (Fin n → ℚ_[p]) :=
    TopologicalSpace.instSecondCountableTopologyForallOfCountable
  letI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℚ_[p]) :=
    TopologicalSpace.instSecondCountableTopologyForallOfCountable
  exact TopologicalSpace.secondCountableTopology_induced _ _
    ((↑) : (skewAdjointMatricesLieSubalgebra
      (V.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule →
        Matrix (Fin n) (Fin n) ℚ_[p])

/-- Scalar extension of the rational presentation tangent equivalence to a
native p-adic skew-adjoint carrier. -/
def blockToAmbientPadicSkewAdjointLinearEquiv
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (p : ℕ) [Fact (Nat.Prime p)] :
    (skewAdjointMatricesLieSubalgebra
        ((P.blockSpace hx).pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule
      ≃ₗ[ℚ_[p]]
    (skewAdjointMatricesLieSubalgebra
        (V.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  (skewAdjointScalarExtensionEquiv (K := ℚ_[p])
      (P.blockSpace hx).pairingMatrix).symm ≪≫ₗ
    LinearEquiv.baseChange ℚ ℚ_[p] _ _
      (P.blockToAmbientSkewAdjointLinearEquiv hx) ≪≫ₗ
    skewAdjointScalarExtensionEquiv (K := ℚ_[p]) V.pairingMatrix

/-- The p-adic scalar extension is continuous on the existing
finite-dimensional coordinate topologies. -/
def blockToAmbientPadicSkewAdjointContinuousLinearEquiv
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (p : ℕ) [Fact (Nat.Prime p)] :
    (skewAdjointMatricesLieSubalgebra
        ((P.blockSpace hx).pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule
      ≃L[ℚ_[p]]
    (skewAdjointMatricesLieSubalgebra
        (V.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  (P.blockToAmbientPadicSkewAdjointLinearEquiv hx p).toContinuousLinearEquiv

/-- On scalar-extended rational tangent vectors, the p-adic presentation map
is literally scalar extension of the rational presentation map. -/
@[simp]
theorem blockToAmbientPadicSkewAdjointLinearEquiv_scalarExtension
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (p : ℕ) [Fact (Nat.Prime p)] (a : ℚ_[p])
    (X : skewAdjointMatricesLieSubalgebra (P.blockSpace hx).pairingMatrix) :
    P.blockToAmbientPadicSkewAdjointLinearEquiv hx p
        (skewAdjointScalarExtensionEquiv (K := ℚ_[p])
          (P.blockSpace hx).pairingMatrix (a ⊗ₜ[ℚ] X)) =
      skewAdjointScalarExtensionEquiv (K := ℚ_[p]) V.pairingMatrix
        (a ⊗ₜ[ℚ] P.blockToAmbientSkewAdjointLinearEquiv hx X) := by
  change skewAdjointScalarExtensionEquiv (K := ℚ_[p]) V.pairingMatrix
      (LinearEquiv.baseChange ℚ ℚ_[p] _ _
        (P.blockToAmbientSkewAdjointLinearEquiv hx)
        ((skewAdjointScalarExtensionEquiv (K := ℚ_[p])
          (P.blockSpace hx).pairingMatrix).symm
          (skewAdjointScalarExtensionEquiv (K := ℚ_[p])
            (P.blockSpace hx).pairingMatrix (a ⊗ₜ[ℚ] X)))) = _
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.baseChange_tmul]

/-- The fixed block p-adic tangent basis, reindexed by the forced equality
with the ambient tangent dimension. -/
def blockToAmbientPadicSkewAdjointSourceBasis
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (p : ℕ) [Fact (Nat.Prime p)] :
    Module.Basis
      (Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra V.pairingMatrix)))
      ℚ_[p]
      (skewAdjointMatricesLieSubalgebra
        ((P.blockSpace hx).pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  (skewAdjointScalarExtensionFinBasis (K := ℚ_[p])
      (P.blockSpace hx).pairingMatrix).reindex
    (Fin.castOrderIso
      (P.blockToAmbientSkewAdjointLinearEquiv hx).finrank_eq)

/-- Mapping the reindexed block p-adic basis gives the scalar extension of
the rationally transported presentation basis. -/
theorem blockToAmbientPadicSkewAdjointSourceBasis_map
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (p : ℕ) [Fact (Nat.Prime p)] :
    (P.blockToAmbientPadicSkewAdjointSourceBasis hx p).map
        (P.blockToAmbientPadicSkewAdjointLinearEquiv hx p) =
      skewAdjointScalarExtensionBasis (K := ℚ_[p]) V.pairingMatrix
        (P.blockToAmbientSkewAdjointTransportedFinBasis hx) := by
  apply DFunLike.ext _ _
  intro i
  have hsource :
      P.blockToAmbientPadicSkewAdjointSourceBasis hx p i =
        skewAdjointScalarExtensionEquiv (K := ℚ_[p])
          (P.blockSpace hx).pairingMatrix
          (1 ⊗ₜ[ℚ] Matrix.skewAdjointFinBasis
            (P.blockSpace hx).pairingMatrix
            ((Fin.castOrderIso
              (P.blockToAmbientSkewAdjointLinearEquiv hx).finrank_eq).symm i)) := by
    calc
      P.blockToAmbientPadicSkewAdjointSourceBasis hx p i =
          skewAdjointScalarExtensionFinBasis (K := ℚ_[p])
            (P.blockSpace hx).pairingMatrix
            ((Fin.castOrderIso
              (P.blockToAmbientSkewAdjointLinearEquiv hx).finrank_eq).symm i) :=
        Module.Basis.reindex_apply _ _ _
      _ = _ := by
        apply Subtype.ext
        rw [skewAdjointScalarExtensionFinBasis,
          coe_skewAdjointScalarExtensionBasis_apply,
          coe_skewAdjointScalarExtensionEquiv_tmul]
        simp
  rw [Module.Basis.map_apply, hsource,
    P.blockToAmbientPadicSkewAdjointLinearEquiv_scalarExtension hx p]
  calc
    skewAdjointScalarExtensionEquiv (K := ℚ_[p]) V.pairingMatrix
        (1 ⊗ₜ[ℚ]
          P.blockToAmbientSkewAdjointLinearEquiv hx
            (Matrix.skewAdjointFinBasis (P.blockSpace hx).pairingMatrix
              ((Fin.castOrderIso
                (P.blockToAmbientSkewAdjointLinearEquiv hx).finrank_eq).symm i))) =
      skewAdjointScalarExtensionEquiv (K := ℚ_[p]) V.pairingMatrix
        (1 ⊗ₜ[ℚ] P.blockToAmbientSkewAdjointTransportedFinBasis hx i) := by
          congr 2
          simp only [blockToAmbientSkewAdjointTransportedFinBasis,
            Module.Basis.reindex_apply, Module.Basis.map_apply]
          congr 1
    _ = skewAdjointScalarExtensionBasis (K := ℚ_[p]) V.pairingMatrix
        (P.blockToAmbientSkewAdjointTransportedFinBasis hx) i := by
          apply Subtype.ext
          rw [coe_skewAdjointScalarExtensionEquiv_tmul,
            coe_skewAdjointScalarExtensionBasis_apply]
          simp

/-- The p-adic determinant in the fixed scalar-extended bases is the literal
p-adic image of the rational presentation modulus. -/
theorem blockToAmbientPadicSkewAdjointDet_apply
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (p : ℕ) [Fact (Nat.Prime p)] :
    (skewAdjointScalarExtensionFinBasis (K := ℚ_[p]) V.pairingMatrix).det
        ((P.blockToAmbientPadicSkewAdjointSourceBasis hx p).map
          (P.blockToAmbientPadicSkewAdjointLinearEquiv hx p)) =
      algebraMap ℚ ℚ_[p] (P.blockToAmbientSkewAdjointDetScalar hx) := by
  rw [P.blockToAmbientPadicSkewAdjointSourceBasis_map hx p]
  rw [blockToAmbientSkewAdjointDetScalar]
  have hpoint (j : Fin (Module.finrank ℚ
      (skewAdjointMatricesLieSubalgebra V.pairingMatrix))) :
      skewAdjointScalarExtensionBasis (K := ℚ_[p]) V.pairingMatrix
          (P.blockToAmbientSkewAdjointTransportedFinBasis hx) j =
        skewAdjointScalarExtensionEquiv (K := ℚ_[p]) V.pairingMatrix
          (1 ⊗ₜ[ℚ] P.blockToAmbientSkewAdjointTransportedFinBasis hx j) := by
    apply Subtype.ext
    rw [coe_skewAdjointScalarExtensionBasis_apply (Q := ℚ) (K := ℚ_[p]),
      coe_skewAdjointScalarExtensionEquiv_tmul (Q := ℚ) (K := ℚ_[p])]
    simp
  have hdet := skewAdjointScalarExtensionBasis_det_apply (Q := ℚ) (K := ℚ_[p])
      V.pairingMatrix
      (Matrix.skewAdjointFinBasis V.pairingMatrix)
      (P.blockToAmbientSkewAdjointTransportedFinBasis hx)
  change (skewAdjointScalarExtensionFinBasis (K := ℚ_[p]) V.pairingMatrix).det
      (fun j => skewAdjointScalarExtensionBasis (K := ℚ_[p]) V.pairingMatrix
        (P.blockToAmbientSkewAdjointTransportedFinBasis hx) j) = _
  rw [show
    (fun j => skewAdjointScalarExtensionBasis (K := ℚ_[p]) V.pairingMatrix
      (P.blockToAmbientSkewAdjointTransportedFinBasis hx) j) =
    (fun j => skewAdjointScalarExtensionEquiv (K := ℚ_[p]) V.pairingMatrix
      (1 ⊗ₜ[ℚ] P.blockToAmbientSkewAdjointTransportedFinBasis hx j)) by
      funext j
      exact hpoint j]
  exact hdet

/-- The auxiliary p-adic presentation equivalence which preserves the fixed
coordinate function literally.  It uses only the already forced reindexing
of the block tangent basis. -/
def blockToAmbientPadicFixedCoordinateEquiv
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (p : ℕ) [Fact (Nat.Prime p)] :
    (skewAdjointMatricesLieSubalgebra
        ((P.blockSpace hx).pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule
      ≃L[ℚ_[p]]
    (skewAdjointMatricesLieSubalgebra
        (V.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  (P.blockToAmbientPadicSkewAdjointSourceBasis hx p).equivFun.toContinuousLinearEquiv.trans
    (skewAdjointPadicCoordinateEquiv V.pairingMatrix p).symm

/-- Ambient fixed coordinates after the auxiliary equivalence are the
reindexed fixed block coordinates. -/
@[simp]
theorem blockToAmbientPadicFixedCoordinateEquiv_coordinate_apply
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (p : ℕ) [Fact (Nat.Prime p)]
    (X : (skewAdjointMatricesLieSubalgebra
        ((P.blockSpace hx).pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
    skewAdjointPadicCoordinateEquiv V.pairingMatrix p
        (P.blockToAmbientPadicFixedCoordinateEquiv hx p X) =
      (P.blockToAmbientPadicSkewAdjointSourceBasis hx p).equivFun X := by
  exact (skewAdjointPadicCoordinateEquiv V.pairingMatrix p).apply_symm_apply _

/-- A reindexed block coordinate is the original fixed block coordinate at
the inverse forced index. -/
theorem blockToAmbientPadicSkewAdjointSourceBasis_equivFun_apply
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (p : ℕ) [Fact (Nat.Prime p)]
    (X : (skewAdjointMatricesLieSubalgebra
        ((P.blockSpace hx).pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule)
    (i : Fin (Module.finrank ℚ
      (skewAdjointMatricesLieSubalgebra V.pairingMatrix))) :
    (P.blockToAmbientPadicSkewAdjointSourceBasis hx p).equivFun X i =
      skewAdjointPadicCoordinateEquiv (P.blockSpace hx).pairingMatrix p X
        ((Fin.castOrderIso
          (P.blockToAmbientSkewAdjointLinearEquiv hx).finrank_eq).symm i) := by
  let b := skewAdjointScalarExtensionFinBasis (K := ℚ_[p])
      (P.blockSpace hx).pairingMatrix
  let e := Fin.castOrderIso
      (P.blockToAmbientSkewAdjointLinearEquiv hx).finrank_eq
  have hrepr := Module.Basis.repr_reindex b X e.toEquiv
  have hcoord := congrArg
    (fun c : Fin (Module.finrank ℚ
      (skewAdjointMatricesLieSubalgebra V.pairingMatrix)) →₀ ℚ_[p] => c i) hrepr
  change (b.reindex e).equivFun X i = b.equivFun X (e.symm i)
  simp only [Module.Basis.equivFun_apply]
  simpa only [Finsupp.mapDomain_equiv_apply, Equiv.apply_symm_apply] using hcoord

/-- The auxiliary fixed-coordinate equivalence maps the normalized block
unit-coordinate lattice exactly onto the ambient one. -/
theorem blockToAmbientPadicFixedCoordinateEquiv_image_coordinateLattice
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (p : ℕ) [Fact (Nat.Prime p)] :
    P.blockToAmbientPadicFixedCoordinateEquiv hx p ''
        (skewAdjointPadicCoordinateLattice
          (P.blockSpace hx).pairingMatrix p : Set _) =
      (skewAdjointPadicCoordinateLattice V.pairingMatrix p : Set _) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨X, hX, rfl⟩
    refine (mem_skewAdjointPadicCoordinateLattice_iff
      V.pairingMatrix p _).2 ?_
    have hX' := (mem_skewAdjointPadicCoordinateLattice_iff
      (P.blockSpace hx).pairingMatrix p X).1 hX
    intro i
    rw [P.blockToAmbientPadicFixedCoordinateEquiv_coordinate_apply hx p X,
      P.blockToAmbientPadicSkewAdjointSourceBasis_equivFun_apply hx p X i]
    exact hX' _
  · intro Y hY
    refine ⟨(P.blockToAmbientPadicFixedCoordinateEquiv hx p).symm Y, ?_,
      (P.blockToAmbientPadicFixedCoordinateEquiv hx p).apply_symm_apply Y⟩
    refine (mem_skewAdjointPadicCoordinateLattice_iff
      (P.blockSpace hx).pairingMatrix p _).2 ?_
    have hY' := (mem_skewAdjointPadicCoordinateLattice_iff
      V.pairingMatrix p Y).1 hY
    intro j
    let e := Fin.castOrderIso
      (P.blockToAmbientSkewAdjointLinearEquiv hx).finrank_eq
    have hcoord :
        skewAdjointPadicCoordinateEquiv V.pairingMatrix p Y (e j) =
          skewAdjointPadicCoordinateEquiv (P.blockSpace hx).pairingMatrix p
            ((P.blockToAmbientPadicFixedCoordinateEquiv hx p).symm Y) j := by
      calc
        _ = skewAdjointPadicCoordinateEquiv V.pairingMatrix p
              (P.blockToAmbientPadicFixedCoordinateEquiv hx p
                ((P.blockToAmbientPadicFixedCoordinateEquiv hx p).symm Y))
              (e j) := by
                rw [(P.blockToAmbientPadicFixedCoordinateEquiv hx p).apply_symm_apply Y]
        _ = (P.blockToAmbientPadicSkewAdjointSourceBasis hx p).equivFun
              ((P.blockToAmbientPadicFixedCoordinateEquiv hx p).symm Y)
              (e j) := by
                rw [P.blockToAmbientPadicFixedCoordinateEquiv_coordinate_apply]
        _ = skewAdjointPadicCoordinateEquiv (P.blockSpace hx).pairingMatrix p
              ((P.blockToAmbientPadicFixedCoordinateEquiv hx p).symm Y) j := by
                rw [P.blockToAmbientPadicSkewAdjointSourceBasis_equivFun_apply]
                simpa only [e] using congrArg
                  (skewAdjointPadicCoordinateEquiv (P.blockSpace hx).pairingMatrix p
                    ((P.blockToAmbientPadicFixedCoordinateEquiv hx p).symm Y))
                  (e.symm_apply_apply j)
    rw [← hcoord]
    exact hY' (e j)

set_option synthInstance.maxHeartbeats 200000 in
/-- Literal transport of the block fixed-coordinate p-adic Haar to the
ambient fixed-coordinate Haar.  The determinant-bearing presentation map is
factored through this normalized auxiliary equivalence below. -/
theorem map_blockToAmbientPadicFixedCoordinateMeasure
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (p : ℕ) [Fact (Nat.Prime p)] :
    Measure.map (P.blockToAmbientPadicFixedCoordinateEquiv hx p)
        (skewAdjointPadicCoordinateMeasure (P.blockSpace hx).pairingMatrix p) =
      skewAdjointPadicCoordinateMeasure V.pairingMatrix p := by
  let e := P.blockToAmbientPadicFixedCoordinateEquiv hx p
  let C := skewAdjointPadicCoordinateLattice (P.blockSpace hx).pairingMatrix p
  let D := skewAdjointPadicCoordinateLattice V.pairingMatrix p
  let μ := skewAdjointPadicCoordinateMeasure (P.blockSpace hx).pairingMatrix p
  have himage : e '' (C : Set _) = (D : Set _) :=
    P.blockToAmbientPadicFixedCoordinateEquiv_image_coordinateLattice hx p
  have hpre : e ⁻¹' (D : Set _) = (C : Set _) := by
    calc
      e ⁻¹' (D : Set _) = e ⁻¹' (e '' (C : Set _)) :=
        congrArg (fun s : Set _ ↦ e ⁻¹' s) himage.symm
      _ = C := e.toEquiv.preimage_image _
  letI : MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        ((P.blockSpace hx).pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
    borel _
  letI : BorelSpace
      (skewAdjointMatricesLieSubalgebra
        ((P.blockSpace hx).pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
    ⟨rfl⟩
  letI : Measure.IsAddHaarMeasure μ :=
    skewAdjointPadicCoordinateMeasure_isAddHaarMeasure
      (P.blockSpace hx).pairingMatrix p
  letI : Measure.IsAddHaarMeasure (Measure.map e μ) :=
    e.isAddHaarMeasure_map μ
  letI : LocallyCompactSpace
      (skewAdjointMatricesLieSubalgebra
        ((P.blockSpace hx).pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
    (skewAdjointPadicCoordinateEquiv
      (P.blockSpace hx).pairingMatrix p).toHomeomorph.isClosedEmbedding.locallyCompactSpace
  letI : SigmaCompactSpace
      (skewAdjointMatricesLieSubalgebra
        ((P.blockSpace hx).pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule := by
    infer_instance
  letI : SigmaFinite μ := by
    dsimp [μ]
    unfold skewAdjointPadicCoordinateMeasure
    exact Measure.sigmaFinite_addHaarMeasure
      (K₀ := skewAdjointPadicCoordinateLattice (P.blockSpace hx).pairingMatrix p)
  letI : SigmaFinite (Measure.map e μ) :=
    e.toHomeomorph.toMeasurableEquiv.sigmaFinite_map
  have hnormalized : Measure.map e μ D = 1 := by
    rw [Measure.map_apply e.continuous.measurable D.isCompact.measurableSet]
    rw [hpre]
    exact skewAdjointPadicCoordinateMeasure_lattice
      (P.blockSpace hx).pairingMatrix p
  have hunique : Measure.addHaarMeasure D = Measure.map e μ :=
    (Measure.addHaarMeasure_eq_iff D (Measure.map e μ)).2 hnormalized
  change Measure.map e μ = skewAdjointPadicCoordinateMeasure V.pairingMatrix p
  unfold skewAdjointPadicCoordinateMeasure
  exact hunique.symm

/-- The auxiliary equivalence sends each forced-reindexed block basis vector
to the same-index ambient fixed basis vector. -/
theorem blockToAmbientPadicFixedCoordinateEquiv_apply_sourceBasis
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (p : ℕ) [Fact (Nat.Prime p)]
    (i : Fin (Module.finrank ℚ
      (skewAdjointMatricesLieSubalgebra V.pairingMatrix))) :
    P.blockToAmbientPadicFixedCoordinateEquiv hx p
        (P.blockToAmbientPadicSkewAdjointSourceBasis hx p i) =
      skewAdjointScalarExtensionFinBasis (K := ℚ_[p]) V.pairingMatrix i := by
  apply (skewAdjointPadicCoordinateEquiv V.pairingMatrix p).injective
  rw [P.blockToAmbientPadicFixedCoordinateEquiv_coordinate_apply]
  ext j
  change
    (P.blockToAmbientPadicSkewAdjointSourceBasis hx p).equivFun
        (P.blockToAmbientPadicSkewAdjointSourceBasis hx p i) j =
      (skewAdjointScalarExtensionFinBasis (K := ℚ_[p]) V.pairingMatrix).equivFun
        (skewAdjointScalarExtensionFinBasis (K := ℚ_[p]) V.pairingMatrix i) j
  rw [Module.Basis.equivFun_self, Module.Basis.equivFun_self]

/-- The actual presentation map, expressed as a same-carrier ambient
automorphism after removing the fixed-coordinate normalized equivalence. -/
def blockToAmbientPadicSkewAdjointAutomorphism
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (p : ℕ) [Fact (Nat.Prime p)] :
    (skewAdjointMatricesLieSubalgebra
        (V.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule
      ≃L[ℚ_[p]]
    (skewAdjointMatricesLieSubalgebra
        (V.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  (P.blockToAmbientPadicFixedCoordinateEquiv hx p).symm.trans
    (P.blockToAmbientPadicSkewAdjointContinuousLinearEquiv hx p)

set_option maxRecDepth 2048 in
/-- The determinant of the residual ambient automorphism is the literal
p-adic image of the rational presentation modulus. -/
theorem blockToAmbientPadicSkewAdjointAutomorphism_det
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (p : ℕ) [Fact (Nat.Prime p)] :
    LinearMap.det
        (P.blockToAmbientPadicSkewAdjointAutomorphism hx p).toLinearMap =
      algebraMap ℚ ℚ_[p] (P.blockToAmbientSkewAdjointDetScalar hx) := by
  let b := skewAdjointScalarExtensionFinBasis (K := ℚ_[p]) V.pairingMatrix
  let c := P.blockToAmbientPadicSkewAdjointSourceBasis hx p
  let e := P.blockToAmbientPadicFixedCoordinateEquiv hx p
  let A := P.blockToAmbientPadicSkewAdjointAutomorphism hx p
  have hA : ∀ i, A (b i) =
      P.blockToAmbientPadicSkewAdjointContinuousLinearEquiv hx p (c i) := by
    intro i
    change P.blockToAmbientPadicSkewAdjointContinuousLinearEquiv hx p
        (e.symm (b i)) = _
    have hb : e.symm (b i) = c i := by
      apply e.injective
      rw [e.apply_symm_apply]
      exact
        (P.blockToAmbientPadicFixedCoordinateEquiv_apply_sourceBasis
          hx p i).symm
    exact congrArg
      (P.blockToAmbientPadicSkewAdjointContinuousLinearEquiv hx p) hb
  calc
    LinearMap.det A.toLinearMap = b.det (fun i ↦ A (b i)) := by
      symm
      have hcomp := Module.Basis.det_comp b A.toLinearMap b
      simpa only [Module.Basis.det_self, mul_one] using hcomp
    _ = b.det (c.map
        (P.blockToAmbientPadicSkewAdjointLinearEquiv hx p)) := by
      congr 1
      funext i
      rw [Module.Basis.map_apply]
      exact hA i
    _ = algebraMap ℚ ℚ_[p]
        (P.blockToAmbientSkewAdjointDetScalar hx) := by
      exact P.blockToAmbientPadicSkewAdjointDet_apply hx p

set_option maxRecDepth 2048 in
/-- The actual p-adic presentation tangent map carries the fixed normalized
block coordinate Haar to the ambient coordinate Haar scaled by the reciprocal
local norm of the single rational presentation modulus. -/
theorem map_blockToAmbientPadicSkewAdjointCoordinateMeasure
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (p : ℕ) [Fact (Nat.Prime p)] :
    Measure.map
        (P.blockToAmbientPadicSkewAdjointContinuousLinearEquiv hx p)
        (skewAdjointPadicCoordinateMeasure (P.blockSpace hx).pairingMatrix p) =
      ‖algebraMap ℚ ℚ_[p]
        (P.blockToAmbientSkewAdjointDetScalar hx)‖₊⁻¹ •
        skewAdjointPadicCoordinateMeasure V.pairingMatrix p := by
  let e := P.blockToAmbientPadicFixedCoordinateEquiv hx p
  let A := P.blockToAmbientPadicSkewAdjointAutomorphism hx p
  let μ := skewAdjointPadicCoordinateMeasure (P.blockSpace hx).pairingMatrix p
  let ν := skewAdjointPadicCoordinateMeasure V.pairingMatrix p
  have he : Measure.map e μ = ν :=
    P.map_blockToAmbientPadicFixedCoordinateMeasure hx p
  have hA := map_skewAdjointPadicCoordinateMeasure_continuousLinearEquiv_det
    V.pairingMatrix p A
  have hfun : (fun y ↦ A (e y)) =
      P.blockToAmbientPadicSkewAdjointContinuousLinearEquiv hx p := by
    funext y
    dsimp only [A, e, blockToAmbientPadicSkewAdjointAutomorphism]
    change P.blockToAmbientPadicSkewAdjointContinuousLinearEquiv hx p
        ((P.blockToAmbientPadicFixedCoordinateEquiv hx p).symm
          ((P.blockToAmbientPadicFixedCoordinateEquiv hx p) y)) = _
    rw [(P.blockToAmbientPadicFixedCoordinateEquiv hx p).symm_apply_apply y]
  have hcomp : A ∘ e =
      P.blockToAmbientPadicSkewAdjointContinuousLinearEquiv hx p := by
    funext y
    exact congrFun hfun y
  calc
    Measure.map (P.blockToAmbientPadicSkewAdjointContinuousLinearEquiv hx p) μ =
        Measure.map A (Measure.map e μ) := by
      rw [Measure.map_map A.continuous.measurable e.continuous.measurable]
      rw [hcomp]
    _ = Measure.map A ν := by rw [he]
    _ = ‖LinearMap.det A.toLinearMap‖₊⁻¹ • ν := hA
    _ = _ := by
      rw [P.blockToAmbientPadicSkewAdjointAutomorphism_det hx p]

end AnisotropicComplementPresentation
end RationalQuadraticSpaceMatrix

end
