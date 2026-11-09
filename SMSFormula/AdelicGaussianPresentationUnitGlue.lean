import SMSFormula.AdelicGaussianPresentationGlueTransport
import SMSFormula.PadicUnitCoordinateHaar
import SMSFormula.PadicQuadraticLocalDensityExplicit
import SMSFormula.RationalAdeleSingularSeriesLocalDensity

/-!
# Block and lattice glue masses of the integral points agree off `D_P`

A continuous linear equivalence of `p`-adic coordinate spaces that maps the unit cube onto the unit
cube preserves the unit-cube Haar measure.  At a prime `p ∤ D_P` the supplied presentation `E_P`
and its inverse are `p`-integral, so `E_P⁻¹(ℤ_p^N) = ℤ_p^N`; hence, by the isometric glue
transport with scalar one,

`glue^{block}_a(ℤ_p^N) = glue^{lattice}_a(ℤ_p^N)`

for the unit-cube Haars and arbitrary covering atlases.  So the block good-place ledger mass
`ν(ℤ_p) · glue^{block}_a(X_a(ℤ_p))` is the lattice glue mass of the integral points, the quantity
attached to the lattice local density.  Nothing is chosen.
-/

noncomputable section

open MeasureTheory Metric PositiveDefiniteIntegralLattice RationalQuadraticSpaceMatrix
open scoped ENNReal

namespace Padic

variable {p : ℕ} [Fact (Nat.Prime p)]

local instance ugMeasurableSpace : MeasurableSpace ℚ_[p] := borel _
local instance ugBorelSpace : BorelSpace ℚ_[p] := ⟨rfl⟩

theorem mem_closedBall_zero_one_iff_forall_mem_subring {κ : Type*} [Fintype κ] (z : κ → ℚ_[p]) :
    z ∈ closedBall (0 : κ → ℚ_[p]) 1 ↔ ∀ i, z i ∈ PadicInt.subring p := by
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
  exact forall_congr' fun i ↦ (PadicInt.mem_subring_iff p).symm

/-- A continuous linear equivalence mapping the unit cube onto the unit cube preserves the
unit-cube Haar measure. -/
theorem map_continuousLinearEquiv_unitHaar {κ ι : Type*} [Fintype κ] [Fintype ι]
    (E : (κ → ℚ_[p]) ≃L[ℚ_[p]] (ι → ℚ_[p]))
    (hE : E ⁻¹' closedBall (0 : ι → ℚ_[p]) 1 = closedBall 0 1) :
    (unitHaar p κ).map E = unitHaar p ι := by
  haveI : ((unitHaar p κ).map E).IsAddHaarMeasure := E.isAddHaarMeasure_map _
  apply eq_unitHaar_of_unitCube
  rw [Measure.map_apply E.continuous.measurable isClosed_closedBall.measurableSet, hE,
    unitHaar_unitCube]

/-- The image of the unit cube is the unit cube when its preimage is. -/
theorem image_closedBall_of_preimage {κ ι : Type*} [Fintype κ] [Fintype ι]
    (E : (κ → ℚ_[p]) ≃L[ℚ_[p]] (ι → ℚ_[p]))
    (hE : E ⁻¹' closedBall (0 : ι → ℚ_[p]) 1 = closedBall 0 1) :
    E '' closedBall (0 : κ → ℚ_[p]) 1 = closedBall 0 1 := by
  rw [← hE, Set.image_preimage_eq _ E.surjective]

end Padic

namespace RationalQuadraticSpaceMatrix.AnisotropicComplementPresentation

variable {n m : ℕ} {V : RationalQuadraticSpaceMatrix n} {x : Fin n → ℚ}
variable (P : V.AnisotropicComplementPresentation x m)
variable (hx : V.nativeRationalQuadraticForm x ≠ 0)

/-- Off the primes of `D_P` the presentation maps the unit cube onto the unit cube. -/
theorem preimage_blockToAmbientPadicContinuousLinearEquiv_closedBall (p : ℕ) [Fact p.Prime]
    (hp : ¬ p ∣ P.presentationDenominator hx) :
    P.blockToAmbientPadicContinuousLinearEquiv hx p ⁻¹' closedBall (0 : Fin n → ℚ_[p]) 1 =
      closedBall 0 1 := by
  ext z
  rw [Set.mem_preimage, Padic.mem_closedBall_zero_one_iff_forall_mem_subring,
    Padic.mem_closedBall_zero_one_iff_forall_mem_subring,
    blockToAmbientPadicContinuousLinearEquiv_apply]
  exact P.blockToAmbientBaseChangeIsometryEquiv_mem_subring_iff hx p hp z

end RationalQuadraticSpaceMatrix.AnisotropicComplementPresentation

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

variable {n m : ℕ} (L : PositiveDefiniteIntegralLattice n) {x : Fin n → ℚ}
variable (P : L.rationalQuadraticSpaceMatrix.AnisotropicComplementPresentation x m)
variable (hx : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x ≠ 0)

local instance ugPadicMeasurableSpace' (p : ℕ) [Fact p.Prime] : MeasurableSpace ℚ_[p] := borel _
local instance ugPadicBorelSpace' (p : ℕ) [Fact p.Prime] : BorelSpace ℚ_[p] := ⟨rfl⟩

/-- Block and lattice glue masses of the integral points agree off the primes of `D_P`, for the
unit-cube Haars and arbitrary covering atlases. -/
theorem blockGlue_integralPoints_eq_latticeGlue (p : ℕ) [Fact (Nat.Prime p)]
    (hp : ¬ p ∣ P.presentationDenominator hx)
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
    (νs : Measure ℚ_[p]) [νs.IsAddHaarMeasure] {value : ℚ_[p]} (hvalue : value ≠ 0) :
    ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[p]).padicSquareBranchAtlasGlue
        p point₁ hpoint₁ tH₁ νs (Padic.unitHaar p (Fin (m + 1))) value
        (Subtype.val ⁻¹' closedBall 0 1) =
      (((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map
        (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap').padicSquareBranchAtlasGlue
        p point₂ hpoint₂ tH₂ νs (Padic.unitHaar p (Fin n)) value
          (Subtype.val ⁻¹' closedBall 0 1) := by
  have hpre := P.preimage_blockToAmbientPadicContinuousLinearEquiv_closedBall hx p hp
  have hmap : (Padic.unitHaar p (Fin (m + 1))).map (P.blockToAmbientPadicContinuousLinearEquiv hx p) =
      (1 : ℝ≥0∞) • Padic.unitHaar p (Fin n) := by
    rw [one_smul]
    exact Padic.map_continuousLinearEquiv_unitHaar _ hpre
  have h := QuadraticMap.padicSquareBranchAtlasGlue_linearIsometry p _ _
    (P.blockToAmbientPadicContinuousLinearEquiv hx p) (latticeGram_blockToAmbient L P hx p)
    point₁ hpoint₁ tH₁ hcover₁ point₂ hpoint₂ tH₂ hcover₂ νs _ _ hmap hvalue
    (isCompact_closedBall 0 1) (IsUltrametricDist.isOpen_closedBall 0 one_ne_zero)
  rw [Padic.image_closedBall_of_preimage _ hpre, one_mul] at h
  exact h

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

namespace PositiveDefiniteIntegralLattice

local instance ugPadicMeasurableSpace'' (p : ℕ) [Fact p.Prime] : MeasurableSpace ℚ_[p] := borel _
local instance ugPadicBorelSpace'' (p : ℕ) [Fact p.Prime] : BorelSpace ℚ_[p] := ⟨rfl⟩

theorem norm_intCast_padic_eq_one {p : ℕ} [Fact p.Prime] {M : ℤ} (hM : ¬ (p : ℤ) ∣ M) :
    ‖((M : ℤ_[p]) : ℚ_[p])‖ = 1 := by
  change ‖(M : ℤ_[p])‖ = 1
  exact le_antisymm (PadicInt.norm_le_one _)
    (not_lt.mp fun h ↦ hM ((PadicInt.norm_int_lt_one_iff_dvd M).mp h))

/-- The lattice glue of the integral points is the local residue density at an odd prime `p ∤ M`:
`glue_M(ℤ_p^N) · ν(ℤ_p) = δ_p(M)` for the unit-cube vector Haar and every covering atlas. -/
theorem latticeGlue_toReal_mul_eq_localResidueDensity {n : ℕ} (L : PositiveDefiniteIntegralLattice (n + 1))
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) {M : ℤ} (hM0 : M ≠ 0) (hM : ¬ (p : ℤ) ∣ M)
    (point : ℕ → Fin (n + 1) → ℚ_[p])
    (hpoint : ∀ i, ((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map
        (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap' (point i) ≠ 0)
    (tH : ∀ i, Measure ((((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map
        (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap').anisotropicOrthogonal (point i)))
    [∀ i, (tH i).IsAddHaarMeasure]
    (hcover : {w | ((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map
        (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap' w ≠ 0} ⊆
      ⋃ i, (((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map
        (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap').padicSquareBranchAtlasRegion
          p point hpoint i)
    (νs : Measure ℚ_[p]) [νs.IsAddHaarMeasure] :
    ((((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map
        (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap').padicSquareBranchAtlasGlue
        p point hpoint tH νs (Padic.unitHaar p (Fin (n + 1))) (((M : ℤ) : ℤ_[p]) : ℚ_[p])
          {x | ‖x.1‖ ≤ 1}).toReal * (νs (closedBall 0 1)).toReal =
      L.localResidueDensity M p := by
  have h := PadicInt.localDensity_toReal_eq_card_div hp (L.pairingMatrix.map (Int.castRingHom ℤ_[p]))
    _ rfl ((M : ℤ) : ℤ_[p]) (norm_intCast_padic_eq_one hM) _ rfl point hpoint tH νs
    (Padic.unitHaar p (Fin (n + 1))) hcover
  rw [Padic.unitHaar_unitCube, ENNReal.toReal_one, div_one] at h
  rw [h, L.localResidueDensity_eq_levelOne hp hM0 hM, normalizedResidueCount,
    ← card_residueSet_eq_card_filter_padic L p M 1]
  push_cast
  rw [div_eq_inv_mul]
  simp only [pow_one]

end PositiveDefiniteIntegralLattice
