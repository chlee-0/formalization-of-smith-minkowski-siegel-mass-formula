import SMSFormula.QuadraticPadicSquareBranchGlueIsometryTransport
import SMSFormula.AdelicGaussianResidueRestrictedOrbitRatioAssembly

/-!
# Block and lattice glue masses through the presentation

The local masses `gR_p, gF_p` of the replacement lemma are glue masses for the lattice Gram form
over `ℚ_p`, while the stabilizer identities (`...CarryingGlue`) express the local densities
`c_v` through glue masses of the block form `W ⊕ ⟨a⟩`.  The supplied presentation `P` is, over
`ℚ_p`, a continuous linear isometry `E_v` from the block form onto the lattice Gram form.  By the
isometric transport of glue masses, for compact open block sets `T, T'`

`glue_block(T) · glue_lattice(E_v T') = glue_block(T') · glue_lattice(E_v T)`,

with arbitrary covering atlases and Haars on both sides: the Jacobian of `E_v` cancels.  So the
ratio `gR_p/gF_p` is the block glue ratio of `E_v⁻¹ T_{R_p}` and `E_v⁻¹ ℤ_p^n`.  Nothing is chosen.
-/

noncomputable section

open MeasureTheory PositiveDefiniteIntegralLattice RationalQuadraticSpaceMatrix
open scoped ENNReal

namespace RationalQuadraticSpaceMatrix
namespace AnisotropicComplementPresentation

variable {n m : ℕ} {V : RationalQuadraticSpaceMatrix n} {x : Fin n → ℚ}
variable (P : V.AnisotropicComplementPresentation x m)

/-- The presentation over `ℚ_p` as a continuous linear equivalence. -/
def blockToAmbientPadicContinuousLinearEquiv (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (p : ℕ) [Fact p.Prime] : (Fin (m + 1) → ℚ_[p]) ≃L[ℚ_[p]] (Fin n → ℚ_[p]) :=
  { (P.blockToAmbientBaseChangeIsometryEquiv hx ℚ_[p]).toLinearEquiv with
    continuous_toFun := P.continuous_blockToAmbientBaseChangeIsometryEquiv hx ℚ_[p]
    continuous_invFun := P.continuous_blockToAmbientBaseChangeIsometryEquiv_symm hx ℚ_[p] }

@[simp]
theorem blockToAmbientPadicContinuousLinearEquiv_apply (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (p : ℕ) [Fact p.Prime] (z : Fin (m + 1) → ℚ_[p]) :
    P.blockToAmbientPadicContinuousLinearEquiv hx p z =
      P.blockToAmbientBaseChangeIsometryEquiv hx ℚ_[p] z :=
  rfl

end AnisotropicComplementPresentation
end RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

variable {n m : ℕ} (L : PositiveDefiniteIntegralLattice n) {x : Fin n → ℚ}
variable (P : L.rationalQuadraticSpaceMatrix.AnisotropicComplementPresentation x m)
variable (hx : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x ≠ 0)

local instance pgtPadicMeasurableSpace (p : ℕ) [Fact p.Prime] : MeasurableSpace ℚ_[p] := borel _
local instance pgtPadicBorelSpace (p : ℕ) [Fact p.Prime] : BorelSpace ℚ_[p] := ⟨rfl⟩

/-- The presentation carries the block form to the lattice `p`-adic Gram form. -/
theorem latticeGram_blockToAmbient (p : ℕ) [Fact p.Prime] (z : Fin (m + 1) → ℚ_[p]) :
    ((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map
        (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap'
        (P.blockToAmbientPadicContinuousLinearEquiv hx p z) =
      (P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[p] z := by
  rw [← commutativeScalarExtensionQuadraticForm_padic_eq,
    P.blockToAmbientPadicContinuousLinearEquiv_apply]
  exact (P.blockToAmbientBaseChangeIsometryEquiv hx ℚ_[p]).map_app z

/-- Block and lattice glue ratios agree: for compact open block sets `T, T'` and arbitrary covering
atlases and Haars on the block and lattice sides,
`glue_block(T) · glue_lattice(E_v T') = glue_block(T') · glue_lattice(E_v T)`. -/
theorem blockGlue_mul_latticeGlue_eq (p : ℕ) [Fact p.Prime]
    (point₁ : ℕ → Fin (m + 1) → ℚ_[p])
    (hpoint₁ : ∀ i, (P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[p] (point₁ i) ≠ 0)
    (tH₁ : ∀ i, Measure (((P.blockSpace hx).commutativeScalarExtensionQuadraticForm
      ℚ_[p]).anisotropicOrthogonal (point₁ i))) [∀ i, (tH₁ i).IsAddHaarMeasure]
    (hcover₁ : {w | (P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[p] w ≠ 0} ⊆
      ⋃ i, ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[p]).padicSquareBranchAtlasRegion
        p point₁ hpoint₁ i)
    (point₂ : ℕ → Fin n → ℚ_[p])
    (hpoint₂ : ∀ i, ((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map
        (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap' (point₂ i) ≠ 0)
    (tH₂ : ∀ i, Measure ((((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map
        (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap').anisotropicOrthogonal (point₂ i)))
    [∀ i, (tH₂ i).IsAddHaarMeasure]
    (hcover₂ : {w | ((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map
        (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap' w ≠ 0} ⊆
      ⋃ i, (((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map
        (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap').padicSquareBranchAtlasRegion
          p point₂ hpoint₂ i)
    (νs : Measure ℚ_[p]) [νs.IsAddHaarMeasure]
    (μ₁ : Measure (Fin (m + 1) → ℚ_[p])) (μ₂ : Measure (Fin n → ℚ_[p]))
    [μ₁.IsAddHaarMeasure] [μ₂.IsAddHaarMeasure]
    {value : ℚ_[p]} (hvalue : value ≠ 0)
    {T T' : Set (Fin (m + 1) → ℚ_[p])} (hTc : IsCompact T) (hTo : IsOpen T)
    (hT'c : IsCompact T') (hT'o : IsOpen T') :
    ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[p]).padicSquareBranchAtlasGlue
        p point₁ hpoint₁ tH₁ νs μ₁ value (Subtype.val ⁻¹' T) *
      (((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map
        (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap').padicSquareBranchAtlasGlue
        p point₂ hpoint₂ tH₂ νs μ₂ value
          (Subtype.val ⁻¹' (P.blockToAmbientPadicContinuousLinearEquiv hx p '' T')) =
    ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[p]).padicSquareBranchAtlasGlue
        p point₁ hpoint₁ tH₁ νs μ₁ value (Subtype.val ⁻¹' T') *
      (((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map
        (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap').padicSquareBranchAtlasGlue
        p point₂ hpoint₂ tH₂ νs μ₂ value
          (Subtype.val ⁻¹' (P.blockToAmbientPadicContinuousLinearEquiv hx p '' T)) :=
  QuadraticMap.padicSquareBranchAtlasGlue_linearIsometry_cross p _ _
    (P.blockToAmbientPadicContinuousLinearEquiv hx p) (latticeGram_blockToAmbient L P hx p)
    point₁ hpoint₁ tH₁ hcover₁ point₂ hpoint₂ tH₂ hcover₂ νs μ₁ μ₂ hvalue hTc hTo hT'c hT'o

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
