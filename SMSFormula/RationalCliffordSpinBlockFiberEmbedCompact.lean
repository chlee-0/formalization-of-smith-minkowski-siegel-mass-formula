import SMSFormula.RationalCliffordGeneralSpinHorizontalCylinderOrbitPadicCentralCutoffCompact

/-!
# The fixed-last embedding pulls compact sets back to compact sets

The fixed-last-coordinate embedding `e : SO(W) → SO(W ⊕ ⟨a⟩)` is a bijection onto the
fixed-vector fiber, with inverse the upper-left block extraction.  Over a Hausdorff
topological ring the fiber is closed (the last column is a continuous function), and the
extraction is continuous: its matrix is a submatrix, and the matrix of its inverse is the
adjugate of that submatrix because the determinant is one.  Hence `e⁻¹K` is the image of the
compact set `K ∩ fiber` under a continuous map, so it is compact for every compact `K`.  In
particular the lower invariant-differential volume of `e⁻¹K` is finite, which discharges the
finiteness hypothesis of the orbit-mass identity through local densities.
-/

noncomputable section

open MeasureTheory Set Topology

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)

/-- The fixed-vector fiber is closed. -/
theorem isClosed_nonisotropicLastCoordinateFiber (A : Type*) [CommRing A] [Algebra ℚ A]
    [TopologicalSpace A] [IsTopologicalRing A] [T2Space A] :
    IsClosed (W.nonisotropicLastCoordinateFiber a ha A) := by
  have hval : Continuous (fun g : (W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroup A ↦
      g.1.1.1) :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  exact isClosed_eq (Continuous.matrix_mulVec hval continuous_const) continuous_const

/-- The upper-left block extraction is continuous on the fiber. -/
theorem continuous_nonisotropicLastCoordinateFiberExtract (A : Type*) [CommRing A] [Algebra ℚ A]
    [TopologicalSpace A] [IsTopologicalRing A] :
    Continuous (W.nonisotropicLastCoordinateFiberExtract a ha A) := by
  have hval : Continuous (fun g : {g : (W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroup A //
      g ∈ W.nonisotropicLastCoordinateFiber a ha A} ↦ g.1.1.1.1) :=
    Units.continuous_val.comp (continuous_subtype_val.comp
      (continuous_subtype_val.comp continuous_subtype_val))
  have hblock : Continuous (fun g : {g : (W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroup A //
      g ∈ W.nonisotropicLastCoordinateFiber a ha A} ↦ upperLeftBlock g.1.1.1.1) :=
    hval.matrix_submatrix _ _
  have hU : Continuous (fun g : {g : (W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroup A //
      g ∈ W.nonisotropicLastCoordinateFiber a ha A} ↦
        (W.nonisotropicLastCoordinateFiberExtract a ha A g).1.1) := by
    refine Units.continuous_iff.2 ⟨hblock, ?_⟩
    have hinv : ∀ g : {g : (W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroup A //
        g ∈ W.nonisotropicLastCoordinateFiber a ha A},
        ((((W.nonisotropicLastCoordinateFiberExtract a ha A g).1.1)⁻¹ :
          (Matrix (Fin n) (Fin n) A)ˣ) : Matrix (Fin n) (Fin n) A) =
          (upperLeftBlock g.1.1.1.1).adjugate := by
      intro g
      set h := W.nonisotropicLastCoordinateFiberExtract a ha A g
      have hdet : h.1.1.1.det = 1 :=
        (PositiveDefiniteIntegralLattice.mem_specialFormPreservingMatrixSubgroup_iff _ h.1).mp h.2
      rw [Matrix.coe_units_inv, Matrix.inv_def, hdet, Ring.inverse_one, one_smul]
      rfl
    simp_rw [hinv]
    exact hblock.matrix_adjugate
  exact continuous_induced_rng.2 (continuous_induced_rng.2 hU)

/-- The pullback of a compact set under the fixed-last embedding is compact. -/
theorem isCompact_preimage_nonisotropicLastCoordinateFiberEmbedGroup (A : Type*) [CommRing A]
    [Algebra ℚ A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
    {K : Set ((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroup A)}
    (hK : IsCompact K) :
    IsCompact (W.nonisotropicLastCoordinateFiberEmbedGroup a ha A ⁻¹' K) := by
  have hcl := W.isClosed_nonisotropicLastCoordinateFiber a ha A
  have hKF : IsCompact ((Subtype.val : {g : (W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroup A //
      g ∈ W.nonisotropicLastCoordinateFiber a ha A} → _) ⁻¹' K) :=
    hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hK
  have heq : W.nonisotropicLastCoordinateFiberEmbedGroup a ha A ⁻¹' K =
      W.nonisotropicLastCoordinateFiberExtract a ha A '' (Subtype.val ⁻¹' K) := by
    ext h
    constructor
    · intro hh
      exact ⟨W.nonisotropicLastCoordinateFiberEmbed a ha A h, hh,
        W.nonisotropicLastCoordinateFiberExtract_embed a ha A h⟩
    · rintro ⟨g, hg, rfl⟩
      change (W.nonisotropicLastCoordinateFiberEmbed a ha A
        (W.nonisotropicLastCoordinateFiberExtract a ha A g)).1 ∈ K
      rw [W.nonisotropicLastCoordinateFiberEmbed_extract a ha A g]
      exact hg
  rw [heq]
  exact hKF.image (W.continuous_nonisotropicLastCoordinateFiberExtract a ha A)

end RationalQuadraticSpaceMatrix
