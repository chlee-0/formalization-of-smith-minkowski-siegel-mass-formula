import SMSFormula.AdelicGaussianResidueRestrictedOrbitCompactOpen
import SMSFormula.RationalAdeleFiniteLocalReplacementGlueRatio

/-!
# The Riesz ratio at a central-cutoff orbit, assembled

All local inputs of the orbit-test Riesz ratio are produced from the supplied local subgroups:

* residue data carrying the local orbits (compact open orbits, carrier existence);
* the local masses `gF_p = glue_M(ℤ_p^n)`, `gR_p = glue_M(T_{R_p})` of the replacement lemma
  (atlas existence and the tube law), whose positivity needs an integral representation of `M`
  at `p`.  That representation is the image `E_v x_old` of the old base point, which is
  integral by the orbit-integrality hypothesis.

Hence, for a lattice value `M = Q(x)`, compact open local subgroups `s_v` with integral orbits,
`p_v ∤ D_P` off `S ∪ bad`, the integral-orbit hypotheses and `0 < N(O) < ∞`, there exist
residue data and local masses with

`σ(U)/M_native(U) = c_G · ((∏ gR/∏ gF) · σ(X_a ∩ {x_f integral})) / N(O)`.

The ratio `gR_p/gF_p` is intrinsic (the eventual ratio of restricted to full residue counts).
Nothing is chosen in the conclusion.
-/

noncomputable section

open PositiveDefiniteIntegralLattice RationalQuadraticSpaceMatrix Rat.HeightOneSpectrum MeasureTheory
open scoped ENNReal

local instance orbitRatioAssemblyDecidableEq : DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

variable {n m : ℕ} (L : PositiveDefiniteIntegralLattice n) {x : Fin n → ℚ}
variable (P : L.rationalQuadraticSpaceMatrix.AnisotropicComplementPresentation x m) [NeZero m]
variable (hx : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x ≠ 0)

/-- The scalar-extended lattice form over `ℚ_p` is the quadratic map of the `p`-adic Gram
matrix of the lattice. -/
theorem commutativeScalarExtensionQuadraticForm_padic_eq (p : ℕ) [Fact p.Prime]
    (w : Fin n → ℚ_[p]) :
    L.rationalQuadraticSpaceMatrix.commutativeScalarExtensionQuadraticForm ℚ_[p] w =
      ((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map
        (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap' w := by
  rw [L.padicFormMatrix_eq_map_of_rationalFormMatrix_eq rfl p]
  rfl

section Ratio

local instance : MeasurableSpace (P.lowerSpace.nonisotropicLastQuadraticShell
    (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx RationalAdele) := borel _
local instance : BorelSpace (P.lowerSpace.nonisotropicLastQuadraticShell
    (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx RationalAdele) := ⟨rfl⟩

variable (hn : 4 < n) {b : ℝ} (hb : 0 < b)
variable (x₀ : adelicValueFiber L (algebraMap ℚ RationalAdele
  (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x)))
variable (K : Subgroup L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup)
variable (hc : IsCompact (K : Set L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup))
variable (ho : IsOpen (K : Set L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup))
include hn hc ho

/-- The assembled Riesz ratio at the central-cutoff orbit. -/
theorem exists_div_nativeShellMeasure_eq_localRatio_integralCarrier
    (M : ℤ) (hM : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x = ((M : ℤ) : ℚ))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (s : ∀ v : {v // v ∈ S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces},
      Subgroup ((P.blockSpace hx).HeightOnePadicCliffordGeneralSpinGroup v.1))
    (hodd : (P.blockSpace hx).cliffordSpinCandidateOddUnimodularBadPlaces ⊆
      S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces)
    (haunit : ∀ v, v ∉ S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces →
      finiteAdelicUnitHeightOneComponentHom v
          (Units.map (algebraMap ℚ RationalFiniteAdele).toMonoidHom
            (Units.mk0 (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx)) ∈
        padicIntegralUnitsSubgroup (primesEquiv v).1)
    (hden : ∀ v : IsDedekindDomain.HeightOneSpectrum ℤ,
      v ∉ S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces →
      ¬ (primesEquiv v : ℕ) ∣ P.presentationDenominator hx)
    (hsc : ∀ (v : IsDedekindDomain.HeightOneSpectrum ℤ)
      (h : v ∈ S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces),
      IsCompact (s ⟨v, h⟩ : Set ((P.blockSpace hx).HeightOnePadicCliffordGeneralSpinGroup v)))
    (hso : ∀ (v : IsDedekindDomain.HeightOneSpectrum ℤ)
      (h : v ∈ S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces),
      IsOpen (s ⟨v, h⟩ : Set ((P.blockSpace hx).HeightOnePadicCliffordGeneralSpinGroup v)))
    (hOint : ∀ (v : IsDedekindDomain.HeightOneSpectrum ℤ)
      (h : v ∈ S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces),
      ∀ z ∈ (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap P.lowerSpace
        (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx
        ℚ_[(primesEquiv v).1]) '' (s ⟨v, h⟩ : Set _), ∀ i,
        P.blockToAmbientBaseChangeIsometryEquiv hx ℚ_[(primesEquiv v).1] z.1 i ∈
          PadicInt.subring (primesEquiv v).1)
    (h0 : P.lowerSpace.fullAdelicNonisotropicLastShellMeasure
      (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx
        ((CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap P.lowerSpace
          (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx RationalAdele) ''
          ((P.blockSpace hx).centralCutoffSubgroup ⊤
            ((P.blockSpace hx).cliffordGeneralSpinHorizontalCylinderSubgroup S s) : Set _)) ≠ 0)
    (htop : P.lowerSpace.fullAdelicNonisotropicLastShellMeasure
      (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx
        ((CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap P.lowerSpace
          (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx RationalAdele) ''
          ((P.blockSpace hx).centralCutoffSubgroup ⊤
            ((P.blockSpace hx).cliffordGeneralSpinHorizontalCylinderSubgroup S s) : Set _)) ≠ ⊤) :
    ∃ (e : ℕ → ℕ) (R : ∀ p : ℕ, Set (Fin n → ZMod (p ^ e p))) (gF gR : ℕ → ℝ≥0∞),
      (∀ p ∈ placeBlockPrimes (S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces), p.Prime ∧ 1 ≤ e p) ∧
      (∀ (v : IsDedekindDomain.HeightOneSpectrum ℤ)
        (h : v ∈ S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces)
        (z : P.lowerSpace.nonisotropicLastQuadraticShell
          (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx ℚ_[(primesEquiv v).1]),
        P.blockToAmbientBaseChangeIsometryEquiv hx ℚ_[(primesEquiv v).1] z.1 ∈
            PadicInt.restrictedIntegralVectors (e (primesEquiv v)) (R (primesEquiv v)) ↔
          z ∈ (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap P.lowerSpace
            (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx
            ℚ_[(primesEquiv v).1]) '' (s ⟨v, h⟩ : Set _)) ∧
      (∀ p ∈ placeBlockPrimes (S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces), gF p ≠ 0) ∧
      (∀ p ∈ placeBlockPrimes (S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces), gF p ≠ ⊤) ∧
      (∀ p ∈ placeBlockPrimes (S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces), ∀ᶠ v : ℕ in Filter.atTop,
        (L.restrictedResidueCount M (placeBlockPrimes (S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces)) e R (p ^ v) : ℝ≥0∞) * gF p =
          (L.fullResidueCount M (p ^ v) : ℝ≥0∞) * gR p) ∧
      let a := algebraMap ℚ RationalAdele
        (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x)
      let σ := gaussianFiberMeasure L hn hb a
      let Mn := nativeShellMeasureOnValueFiber L P hx
      let U := (fun g ↦ g • x₀) ''
        (K : Set L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup)
      σ U / Mn U =
        (P.blockToAmbientFullAdelicGeneralSpinHorizontalHaarScalar hx : ℝ≥0∞) *
          (((∏ p ∈ placeBlockPrimes (S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces), gR p) / ∏ p ∈ placeBlockPrimes (S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces), gF p) *
              σ (fiberDividedCarrier L a 1) /
            P.lowerSpace.fullAdelicNonisotropicLastShellMeasure
              (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx
              ((CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap P.lowerSpace
                (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx RationalAdele) ''
                ((P.blockSpace hx).centralCutoffSubgroup ⊤
                  ((P.blockSpace hx).cliffordGeneralSpinHorizontalCylinderSubgroup S s) :
                    Set _))) := by
  obtain ⟨e, R, he, hcar, hO⟩ := exists_residueData_image_centralCutoffOrbit_eq_of_compactOpen L P hx S s
    hodd haunit hden hsc hso hOint
  have hM0 : M ≠ 0 := by
    rintro rfl
    exact hx (by rw [hM]; simp)
  have hrep : ∀ p (hp : p ∈ placeBlockPrimes (S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces)),
      haveI : Fact p.Prime := ⟨(he p hp).1⟩
      ∃ u : Fin n → ℚ_[p], ‖u‖ ≤ 1 ∧
        ((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map
          (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap' u =
            (((M : ℤ) : ℤ_[p]) : ℚ_[p]) := by
    intro p hp
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hp
    let z := CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap P.lowerSpace
      (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx ℚ_[(primesEquiv v).1] 1
    have hz : z ∈ (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap P.lowerSpace
        (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx
        ℚ_[(primesEquiv v).1]) '' (s ⟨v, hv⟩ : Set _) := ⟨1, (s ⟨v, hv⟩).one_mem, rfl⟩
    refine ⟨P.blockToAmbientBaseChangeIsometryEquiv hx ℚ_[(primesEquiv v).1] z.1,
      (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i ↦ hOint v hv z hz i, ?_⟩
    rw [← commutativeScalarExtensionQuadraticForm_padic_eq]
    have hshell : L.rationalQuadraticSpaceMatrix.commutativeScalarExtensionQuadraticForm
        ℚ_[(primesEquiv v).1] (P.blockToAmbientBaseChangeIsometryEquiv hx ℚ_[(primesEquiv v).1] z.1) =
          algebraMap ℚ _ (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) :=
      (P.blockToAmbientShellHomeomorph hx ℚ_[(primesEquiv v).1] z).2
    rw [hshell, hM, padicIntCast_intCast_eq_algebraMap]
  obtain ⟨gF, gR, hgF0, hgFt, hloc, hFne⟩ :=
    L.exists_localGlueRatio_family M hM0 (placeBlockPrimes (S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces)) e R he hrep
  refine ⟨e, R, gF, gR, he, hcar, hgF0, hgFt, hloc, ?_⟩
  exact div_nativeShellMeasure_eq_scalar_mul_localRatio_mul_div L P hx hn hb x₀ K hc ho M hM
    (placeBlockPrimes (S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces)) e R he gF gR hgF0 hgFt hloc hFne _ hO h0 htop

end Ratio

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
