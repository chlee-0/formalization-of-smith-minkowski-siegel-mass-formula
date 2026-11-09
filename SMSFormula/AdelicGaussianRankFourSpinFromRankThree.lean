import SMSFormula.AdelicGaussianRankFourDualAggregate
import SMSFormula.AdelicGaussianSpinTamagawaCommonComplementComparison
import SMSFormula.AdelicGaussianSpecialOrthogonalTamagawaFromRankFour

/-!
# `τ(Spin) = 1` in rank three implies `τ(Spin) = 1` in rank four

For a rank-four lattice `L`, the rank-four shell identities at every shell for the lattice and dual Gaussian tests
(`exists_complement_representedNormTheta_{latticeTest,dualTest}_mul_spinTamagawa_eq_rankFour`) have ternary
complements `L_W`; if `τ(Spin_{L_W}) = 1` for every ternary lattice they hold with the common complement factor
`t = 1`.  With the rank-four aggregate identity `1 + Σρ_Φ = C(a)(1 + Σρ_Ψ)`
(`rankFour_shellDensity_aggregate_identity`) and a width with `C(a) ≠ 1` (`exists_pos_dilationConstant_ne_one`),
the common-complement comparison (`spinTamagawaNumberENNReal_eq_of_commonComplementShellIdentities`) gives
`τ(Spin_L) = 1` (`rankFourSpinTamagawaOne_of_rankThree`).

`RankThreeSpinTamagawaOne` itself is not proved here (it is proved in
`RationalSpecialOrthogonalTamagawaNumberFromSpin`).
-/

noncomputable section

open scoped ENNReal

namespace PositiveDefiniteIntegralLattice

open IntegralFiniteAdelePhase

/-- The rank-four common-complement theorem: if every anisotropic rational complement `x^⊥` of a rank-four lattice
has Spin volume `t < ∞` (for every integral ternary lattice isometric to it), then `τ(Spin_L) = t`. -/
theorem spinTamagawaNumberENNReal_eq_of_complementSpinTamagawa_rankFour (L : PositiveDefiniteIntegralLattice 4)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet) {P : ℝ} (hP : 0 < P)
    (hconv : massLocalInverseProductTendsTo L P) {t : ℝ≥0∞} (ht : t ≠ ⊤)
    (hW : ∀ (x : Fin 4 → ℚ), L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x ≠ 0 →
      ∀ (LW : PositiveDefiniteIntegralLattice 3),
      LW.rationalQuadraticSpaceMatrix.quadraticForm.IsometryEquiv
          (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm.orthogonalRestriction x) →
      ∀ (instL : Fintype LW.ConcreteProperRationalDoubleCosetSet) (PL : ℝ) (hPL0 : 0 < PL)
        (hL : massLocalInverseProductTendsTo LW PL),
      (cliffordSpinCandidateRawOnoTamagawaDataOfLattice LW (by norm_num) instL hPL0 hL).spinTamagawaNumberENNReal
        = t) :
    (cliffordSpinCandidateRawOnoTamagawaDataOfLattice L (by norm_num) inst hP hconv).spinTamagawaNumberENNReal
      = t := by
  haveI : Nonempty (Fin 4) := ⟨0⟩
  obtain ⟨a, ha, hC⟩ := exists_pos_dilationConstant_ne_one (N := 4) (by norm_num)
    ((L.polarRealDeterminantScale : ℝ)⁻¹)
  obtain ⟨hΦnn, hΦsum, -⟩ := L.latticeShellDensity_aggregate ha
  obtain ⟨hΨnn, hΨsum, -⟩ := L.dualShellDensity_aggregate ha
  refine L.spinTamagawaNumberENNReal_eq_of_commonComplementShellIdentities (r := 2) (by norm_num) inst hP
    hconv ha hC ht (fun b ↦ latticeShellDensity L a b.1)
    (fun b ↦ dualShellDensity L a⁻¹ b.1) hΦnn hΨnn hΦsum hΨsum ?_ ?_
    (L.rankFour_shellDensity_aggregate_identity ha)
  · intro b
    obtain ⟨x, hx, LW, eW, instL, PL, hPL0, hL, h⟩ :=
      exists_complement_representedNormTheta_latticeTest_mul_spinTamagawa_eq_rankFour (s := 1) L le_rfl
        inst hP hconv ha b
    have h1 := hW x hx LW eW instL PL hPL0 hL
    calc _ = _ := h
      _ = t * ENNReal.ofReal (latticeShellDensity L a b.1) := by rw [h1]
  · intro b
    obtain ⟨x, hx, LW, eW, instL, PL, hPL0, hL, h⟩ :=
      exists_complement_representedNormTheta_dualTest_mul_spinTamagawa_eq_rankFour L inst hP hconv
        (inv_pos.2 ha) b
    have h1 := hW x hx LW eW instL PL hPL0 hL
    calc _ = _ := h
      _ = t * ENNReal.ofReal (dualShellDensity L a⁻¹ b.1) := by rw [h1]

/-- The rank-four step: `τ(Spin) = 1` for every ternary lattice gives `τ(Spin) = 1` for every rank-four lattice. -/
theorem rankFourSpinTamagawaOne_of_rankThree (h3 : RankThreeSpinTamagawaOne) : RankFourSpinTamagawaOne := by
  intro L inst P hP hconv
  exact L.spinTamagawaNumberENNReal_eq_of_complementSpinTamagawa_rankFour inst hP hconv ENNReal.one_ne_top
    fun x _ LW _ instL PL hPL0 hL ↦ h3 LW instL PL hPL0 hL

end PositiveDefiniteIntegralLattice
