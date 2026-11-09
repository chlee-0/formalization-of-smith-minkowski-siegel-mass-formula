import SMSFormula.AdelicGaussianResidueRestrictedOrbitCarrying
import SMSFormula.RationalCliffordGeneralSpinPadicShellOrbitOpen

/-!
# The orbit image for compact open local subgroups

With the `ℚ_p` shell orbit map continuous and open, the local orbit `s_v · x_old` of a compact
open subgroup `s_v` is compact open in the block shell.  So the orbit-image theorem needs of the
supplied local subgroups only that they are compact open, together with the integrality of their
orbits in ambient coordinates.  Nothing is chosen.
-/

noncomputable section

open PositiveDefiniteIntegralLattice RationalQuadraticSpaceMatrix Rat.HeightOneSpectrum

local instance orbitCompactOpenDecidableEq : DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

variable {n m : ℕ} (L : PositiveDefiniteIntegralLattice n) {x : Fin n → ℚ}
variable (P : L.rationalQuadraticSpaceMatrix.AnisotropicComplementPresentation x m) [NeZero m]
variable (hx : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x ≠ 0)

/-- The orbit image is a carried fiber set for compact open local subgroups whose orbits are
integral in ambient coordinates. -/
theorem exists_residueData_image_centralCutoffOrbit_eq_of_compactOpen
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
          PadicInt.subring (primesEquiv v).1) :
    ∃ (e : ℕ → ℕ) (R : ∀ p : ℕ, Set (Fin n → ZMod (p ^ e p))),
      (∀ p ∈ placeBlockPrimes (S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces),
        p.Prime ∧ 1 ≤ e p) ∧
      (∀ (v : IsDedekindDomain.HeightOneSpectrum ℤ)
        (h : v ∈ S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces)
        (z : P.lowerSpace.nonisotropicLastQuadraticShell
          (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx ℚ_[(primesEquiv v).1]),
        P.blockToAmbientBaseChangeIsometryEquiv hx ℚ_[(primesEquiv v).1] z.1 ∈
            PadicInt.restrictedIntegralVectors (e (primesEquiv v)) (R (primesEquiv v)) ↔
          z ∈ (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap P.lowerSpace
            (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx
            ℚ_[(primesEquiv v).1]) '' (s ⟨v, h⟩ : Set _)) ∧
      haveI : NeZero (localRestrictionLevel (placeBlockPrimes
          (S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces)) e) :=
        ⟨localRestrictionLevel_ne_zero fun _ hp ↦ prime_of_mem_placeBlockPrimes hp⟩
      (P.blockToAmbientShellHomeomorph hx RationalAdele ''
          ((CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap P.lowerSpace
            (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx RationalAdele) ''
            ((P.blockSpace hx).centralCutoffSubgroup ⊤
              ((P.blockSpace hx).cliffordGeneralSpinHorizontalCylinderSubgroup S s) : Set _)) :
          Set (adelicValueFiber L (algebraMap ℚ RationalAdele
            (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x)))) =
        fiberResidueRestrictedSet L _
          (localRestrictionLevel (placeBlockPrimes
            (S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces)) e)
          (localRestrictionSet (placeBlockPrimes
            (S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces)) e R) :=
  exists_residueData_image_centralCutoffOrbit_eq L P hx S s hodd haunit hden
    (fun v h ↦ (P.lowerSpace.isCompact_isOpen_image_padic_nonisotropicLastShellOrbitMap _ hx
      (primesEquiv v).1 (hsc v h) (hso v h)).1)
    (fun v h ↦ (P.lowerSpace.isCompact_isOpen_image_padic_nonisotropicLastShellOrbitMap _ hx
      (primesEquiv v).1 (hsc v h) (hso v h)).2) hOint

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
