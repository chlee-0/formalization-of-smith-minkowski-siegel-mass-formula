import SMSFormula.AdelicGaussianCoreOneShellWeightCapstone

/-!
# The bad set `B`: what its place hypotheses require, and why they are satisfiable

The core theorem `representedNormTheta_mul_spinTamagawa_eq_core` works with the bad set
`B = P.lowerSpace.lastExtensionHorizontalBadPlaces (Q x) hx` and applies the good-place formulas off
`B`.  Its hypotheses `hodd`, `haunit`, `hSB`, `hgp` force every bad place into `B`:

* the dyadic place (always odd-unimodular bad) lies in `B`;
* every place where `Q x` is not a unit lies in `B`.

The set `B` contains the places where the Chevalley-basis Clifford structure constants of
`W ⊕ ⟨Q x⟩` or `W` are non-integral, the block's odd-unimodular bad places, and the prime support
of `Q x` (`RationalCliffordGeneralSpinHorizontalCylinderOrbitIntegralCompletion`).  The last two
parts are needed: for the integral complements used by the core theorem the structure constants
are integral, so the first part alone would make the hypotheses unsatisfiable for general shells.
With `S := B` the hypotheses `hodd`, `haunit`, `hSB` and `hgp` are satisfied
(`capstone_hodd_self`, `capstone_haunit_self`, `capstone_hgp_self`).  `hden` still needs the
presentation denominator to be supported on `B`.
-/

noncomputable section

open PositiveDefiniteIntegralLattice RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

variable {s : ℕ} (L : PositiveDefiniteIntegralLattice (s + 2 + 1)) {x : Fin (s + 2 + 1) → ℚ}
variable (P : L.rationalQuadraticSpaceMatrix.AnisotropicComplementPresentation x (s + 2))
variable (hx : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x ≠ 0)

local instance cbsrDecidableEqK : DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

/-- The dyadic place is always odd-unimodular bad. -/
theorem rationalIdeleDyadicPlace_mem_cliffordSpinCandidateOddUnimodularBadPlaces {m : ℕ}
    (V : RationalQuadraticSpaceMatrix m) :
    RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace ∈
      V.cliffordSpinCandidateOddUnimodularBadPlaces := by
  rw [RationalQuadraticSpaceMatrix.mem_cliffordSpinCandidateOddUnimodularBadPlaces_iff]
  have hv : (Rat.HeightOneSpectrum.primesEquiv
      RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace).1 = 2 := by
    simp [RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace]
  rw [hv, Rat.matrixPairBadPrimeSet, Nat.mem_primeFactors]
  refine ⟨Nat.prime_two, ?_, ?_⟩
  · unfold Rat.matrixPairBadPrimeSupportNat
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right
      (Dvd.dvd.mul_right (Dvd.dvd.mul_right (dvd_refl 2) _) _) _) _) _) _
  · have hdp : Rat.matrixDenominatorProduct V.pairingMatrix ≠ 0 := by
      unfold Rat.matrixDenominatorProduct
      rw [Finset.prod_ne_zero_iff]
      intro i _
      rw [Finset.prod_ne_zero_iff]
      intro j _
      exact Rat.den_ne_zero _
    have hnum : V.pairingMatrix.det.num.natAbs ≠ 0 :=
      Int.natAbs_ne_zero.2 (Rat.num_ne_zero.2 V.form_det_ne_zero)
    unfold Rat.matrixPairBadPrimeSupportNat
    have hden : V.pairingMatrix.det.den ≠ 0 := Rat.den_ne_zero _
    positivity

/-- The hypotheses of the core theorem put the dyadic place in `B`. -/
theorem rationalIdeleDyadicPlace_mem_lastExtensionHorizontalBadPlaces_of_capstoneHyps
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hodd : (P.blockSpace hx).cliffordSpinCandidateOddUnimodularBadPlaces ⊆
      S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces)
    (hgp : ∀ v ∈ S, v ∉ P.lowerSpace.lastExtensionHorizontalBadPlaces
        (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx →
      v ∉ (P.blockSpace hx).cliffordSpinCandidateOddUnimodularBadPlaces) :
    RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace ∈
      P.lowerSpace.lastExtensionHorizontalBadPlaces
        (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx := by
  have h2 := rationalIdeleDyadicPlace_mem_cliffordSpinCandidateOddUnimodularBadPlaces
    (P.blockSpace hx)
  rcases Finset.mem_union.1 (hodd h2) with hS | hH
  · by_contra hB
    exact hgp _ hS hB h2
  · unfold RationalQuadraticSpaceMatrix.lastExtensionHorizontalBadPlaces
    exact Finset.mem_union_left _ hH

/-- The hypotheses of the core theorem put every non-unit place of the norm in `B`. -/
theorem mem_lastExtensionHorizontalBadPlaces_of_capstoneHyps_of_not_unit
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (haunit : ∀ v, v ∉ S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces →
      finiteAdelicUnitHeightOneComponentHom v
          (Units.map (algebraMap ℚ RationalFiniteAdele).toMonoidHom
            (Units.mk0 (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx)) ∈
        padicIntegralUnitsSubgroup (Rat.HeightOneSpectrum.primesEquiv v).1)
    (hgp : ∀ v ∈ S, v ∉ P.lowerSpace.lastExtensionHorizontalBadPlaces
        (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx →
      finiteAdelicUnitHeightOneComponentHom v
          (Units.map (algebraMap ℚ RationalFiniteAdele).toMonoidHom
            (Units.mk0 (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx)) ∈
        padicIntegralUnitsSubgroup (Rat.HeightOneSpectrum.primesEquiv v).1)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hv : finiteAdelicUnitHeightOneComponentHom v
          (Units.map (algebraMap ℚ RationalFiniteAdele).toMonoidHom
            (Units.mk0 (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx)) ∉
        padicIntegralUnitsSubgroup (Rat.HeightOneSpectrum.primesEquiv v).1) :
    v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces
        (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx := by
  by_contra hB
  by_cases hS : v ∈ S
  · exact hv (hgp v hS hB)
  · have hH : v ∉ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces := by
      intro h
      apply hB
      unfold RationalQuadraticSpaceMatrix.lastExtensionHorizontalBadPlaces
      exact Finset.mem_union_left _ h
    exact hv (haunit v (by rw [Finset.mem_union, not_or]; exact ⟨hS, hH⟩))

/-- `S := B` satisfies the hypothesis `hodd` of the core theorem. -/
theorem capstone_hodd_self :
    (P.blockSpace hx).cliffordSpinCandidateOddUnimodularBadPlaces ⊆
      P.lowerSpace.lastExtensionHorizontalBadPlaces
          (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx ∪
        (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces :=
  fun _ hv ↦ Finset.mem_union_left _
    (P.lowerSpace.mem_lastExtensionHorizontalBadPlaces_of_oddUnimodular _ hx hv)

/-- `S := B` satisfies the hypothesis `haunit` of the core theorem. -/
theorem capstone_haunit_self (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hv : v ∉ P.lowerSpace.lastExtensionHorizontalBadPlaces
          (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx ∪
        (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces) :
    finiteAdelicUnitHeightOneComponentHom v
        (Units.map (algebraMap ℚ RationalFiniteAdele).toMonoidHom
          (Units.mk0 (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx)) ∈
      padicIntegralUnitsSubgroup (Rat.HeightOneSpectrum.primesEquiv v).1 := by
  haveI : Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩
  have hvB : v ∉ P.lowerSpace.lastExtensionHorizontalBadPlaces
      (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx :=
    fun h ↦ hv (Finset.mem_union_left _ h)
  have hq : Rat.HeightOneSpectrum.primesEquiv v ∉
      Rat.padicNormPrimeSupport (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) := by
    intro h
    apply hvB
    refine P.lowerSpace.mem_lastExtensionHorizontalBadPlaces_of_normSupport _ hx ?_
    unfold rationalPadicNormSupportPlaces
    exact Finset.mem_map.2 ⟨_, h, by simp⟩
  have hnorm := Rat.nnnorm_ratCast_eq_one_of_not_mem_padicNormPrimeSupport hx _ hq
  have hnorm' : ‖algebraMap ℚ ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]
      (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x)‖ = 1 := by
    have := congrArg (fun r : NNReal ↦ (r : ℝ)) hnorm
    simpa using this
  have hval : ((finiteAdelicUnitHeightOneComponentHom v
      (Units.map (algebraMap ℚ RationalFiniteAdele).toMonoidHom
        (Units.mk0 (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx)) :
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ) : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) =
      algebraMap ℚ ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]
        (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) :=
    (finiteAdelicCliffordGeneralSpinHeightOneAlgHom v).commutes _
  refine (mem_padicIntegralUnitsSubgroup_iff _ _).2 ⟨?_, ?_⟩
  · rw [hval, PadicInt.mem_subring_iff, hnorm']
  · rw [Units.val_inv_eq_inv_val, hval, PadicInt.mem_subring_iff, norm_inv, hnorm', inv_one]

/-- With `S := B`, the hypothesis `hgp` of the core theorem is vacuous. -/
theorem capstone_hgp_self {Prop' : IsDedekindDomain.HeightOneSpectrum ℤ → Prop} :
    ∀ v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces
        (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx,
      v ∉ P.lowerSpace.lastExtensionHorizontalBadPlaces
        (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx → Prop' v :=
  fun _ h h' ↦ absurd h h'

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
