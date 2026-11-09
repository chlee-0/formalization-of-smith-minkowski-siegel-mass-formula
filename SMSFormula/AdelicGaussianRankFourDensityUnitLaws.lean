import SMSFormula.AdelicGaussianRankFourDensityInvariance
import SMSFormula.AdelicGaussianTracePositiveDensityShellIdentity
import SMSFormula.AdelicGaussianRealOrbitDensity

/-!
# The unit-test laws of the rank-four density and the rank-four shell identity

The real factor `e^{2π b a_∞}·G_b` of the orbit unit is `1` on the real sphere `{Q_ℝ = a_∞}`, so
the finite section average of the unit `Φ_∞ ⊗ 1_{U_R}` is the residue indicator `1_{U_R}` itself
(`finiteSectionAverage_gaussianResidueRestrictedUnit`).  The rank-four tube limits then give
* the Euler law `D⁴(unit_univ) = c_∞ · ∏'_p δ_p(M)`;
* the replacement law `D⁴(unit_R) = (∏ gR/∏ gF) · D⁴(unit_univ)`.

With `x₀ = z` (the integral representative), `c_∞ = Re d_∞(orbit test)(a_∞) > 0` (closed form),
trace positivity and invariance, the density-parametric shell theorem gives the rank-four shell
identity at an integral representative
(`exists_complement_representedNormTheta_mul_spinTamagawa_eq_of_integral_rankFour`):

`Θ_b(ψ) · τ(Spin_L) = τ(Spin_{L_W}) · ofReal(D⁴(ψ))`

for every nonnegative core test `ψ`, in every lattice rank at least four.  Nothing is chosen.
-/

noncomputable section

open MeasureTheory Filter Topology PositiveDefiniteIntegralLattice RationalQuadraticSpaceMatrix
open scoped ENNReal Matrix

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

variable {n : ℕ}

/-- The real factor of the orbit unit is `1` on the real sphere. -/
theorem unitRealFactor_eq_one (L : PositiveDefiniteIntegralLattice n) (b : ℝ) (a : RationalAdele) {xr : Fin n → ℝ}
    (hxr : L.rationalQuadraticSpaceMatrix.realQuadraticFormValue xr =
      rationalInfiniteAdeleContinuousAddEquivReal a.1) :
    Real.exp (Real.pi * b * (2 * rationalInfiniteAdeleContinuousAddEquivReal a.1)) *
      realShiftedGaussian L b 0 xr = 1 := by
  rw [realShiftedGaussian_eq, SMSFormula.ShiftedGaussian.quadraticShiftedGaussian_apply]
  simp only [ContinuousMap.id_apply, sub_zero]
  have hQ : L.polarQuadraticForm xr = 2 * rationalInfiniteAdeleContinuousAddEquivReal a.1 := by
    rw [polarQuadraticForm_apply, realPolarMatrix_eq_two_smul_realFormMatrix, Matrix.smul_mulVec,
      dotProduct_smul, smul_eq_mul, ← hxr]
    rfl
  rw [hQ, ← Real.exp_add]
  simp

/-- The finite section average of an orbit unit is its residue indicator (for `x₀` on the sphere). -/
theorem finiteSectionAverage_gaussianResidueRestrictedUnit (L : PositiveDefiniteIntegralLattice n) [NeZero n]
    (b : ℝ) (a : RationalAdele) (N₀ : ℕ) [NeZero N₀] (R : Set (Fin n → ZMod N₀))
    (x₀ : Fin n → ℝ)
    (hx₀ : L.rationalQuadraticSpaceMatrix.realQuadraticFormValue x₀ =
      rationalInfiniteAdeleContinuousAddEquivReal a.1) (xf : Fin n → RationalFiniteAdele) :
    finiteSectionAverage L x₀ (gaussianResidueRestrictedUnit L b a N₀ R).val xf =
      realResidueRestrictedIndicator n N₀ R xf := by
  unfold finiteSectionAverage
  have hsec : (fun xr ↦ (gaussianResidueRestrictedUnit L b a N₀ R).val
      (rationalAdeleVectorJoin n xr xf)) = realResidueRestrictedIndicator n N₀ R xf •
        fun xr ↦ Real.exp (Real.pi * b * (2 * rationalInfiniteAdeleContinuousAddEquivReal a.1)) *
          realShiftedGaussian L b 0 xr := by
    funext xr
    change Real.exp (Real.pi * b * (2 * rationalInfiniteAdeleContinuousAddEquivReal a.1)) *
      (realShiftedGaussian L b 0 (rationalAdeleVectorRealPart n (rationalAdeleVectorJoin n xr xf)) *
        realResidueRestrictedIndicator n N₀ R
          (rationalAdeleVectorFinitePart n (rationalAdeleVectorJoin n xr xf))) = _
    rw [rationalAdeleVectorRealPart_join, rationalAdeleVectorFinitePart_join, Pi.smul_apply,
      smul_eq_mul]
    ring
  rw [hsec, L.rationalQuadraticSpaceMatrix.realOrbitAverage_smul,
    L.rationalQuadraticSpaceMatrix.realOrbitAverage_eq_of_sphere
      L.posDef_rationalQuadraticSpaceMatrix_pairingMatrix_map_real x₀ (c := 1)
      (fun xr hxr ↦ unitRealFactor_eq_one L b a (hxr.trans hx₀)), mul_one]

/-- The finite tube mass of an orbit unit is that of its residue indicator. -/
theorem finiteTubeMass_finiteSectionAverage_unit (L : PositiveDefiniteIntegralLattice n) [NeZero n]
    (b : ℝ) (a : RationalAdele) (N₀ : ℕ) [NeZero N₀] (R : Set (Fin n → ZMod N₀))
    (x₀ : Fin n → ℝ)
    (hx₀ : L.rationalQuadraticSpaceMatrix.realQuadraticFormValue x₀ =
      rationalInfiniteAdeleContinuousAddEquivReal a.1) (w : ℕ) (M : ℤ) :
    L.finiteTubeMass (fun xf ↦ (finiteSectionAverage L x₀
        (gaussianResidueRestrictedUnit L b a N₀ R).val xf : ℂ)) w M =
      L.finiteTubeMass (residueRestrictedIndicator n N₀ R) w M := by
  congr 1
  funext xf
  rw [finiteSectionAverage_gaussianResidueRestrictedUnit L b a N₀ R x₀ hx₀,
    coe_realResidueRestrictedIndicator]

section Laws

variable (L : PositiveDefiniteIntegralLattice (n + 1)) (hn : 3 ≤ n) {M : ℤ} (hM : M ≠ 0) {b : ℝ} (hb : 0 ≤ b)
  (x₀ : Fin (n + 1) → ℝ) (cInf : ℝ) (a : RationalAdele)
  (hx₀ : L.rationalQuadraticSpaceMatrix.realQuadraticFormValue x₀ =
    rationalInfiniteAdeleContinuousAddEquivReal a.1)

include hn hM hx₀ in
/-- The finite density of an orbit unit at a CRT restriction. -/
theorem rankFourFiniteDensity_unit_localRestriction (P : Finset ℕ) (e : ℕ → ℕ)
    (R : ∀ p : ℕ, Set (Fin (n + 1) → ZMod (p ^ e p))) (hP : ∀ p ∈ P, p.Prime ∧ 1 ≤ e p)
    (gF gR : ℕ → ℝ≥0∞) (hgF0 : ∀ p ∈ P, gF p ≠ 0) (hgFt : ∀ p ∈ P, gF p ≠ ⊤)
    (hloc : ∀ p ∈ P, ∀ᶠ v : ℕ in atTop,
      (L.restrictedResidueCount M P e R (p ^ v) : ℝ≥0∞) * gF p =
        (L.fullResidueCount M (p ^ v) : ℝ≥0∞) * gR p)
    (hFne : ∀ p ∈ P, ∀ᶠ v : ℕ in atTop, L.fullResidueCount M (p ^ v) ≠ 0) :
    haveI : NeZero (localRestrictionLevel P e) :=
      ⟨localRestrictionLevel_ne_zero fun p hp ↦ (hP p hp).1⟩
    rankFourFiniteDensity L x₀ M (gaussianResidueRestrictedUnit L b a (localRestrictionLevel P e)
        (localRestrictionSet P e R)).val =
      (((∏ p ∈ P, gR p) / ∏ p ∈ P, gF p).toReal : ℂ) *
        ((∏' p : Nat.Primes, L.localResidueDensity M p : ℝ) : ℂ) := by
  haveI : NeZero (localRestrictionLevel P e) :=
    ⟨localRestrictionLevel_ne_zero fun p hp ↦ (hP p hp).1⟩
  unfold rankFourFiniteDensity
  simp_rw [finiteTubeMass_finiteSectionAverage_unit L b a _ _ x₀ hx₀]
  exact (L.tendsto_factorial_mul_localRestrictionCongruenceIntegral hn hM P e R hP gF gR hgF0 hgFt
    hloc hFne).limUnder_eq

include hn hM hx₀ in
/-- The finite density of the integral orbit unit (any level) is the singular series. -/
theorem rankFourFiniteDensity_unit_univ (N₀ : ℕ) [NeZero N₀] :
    rankFourFiniteDensity L x₀ M (gaussianResidueRestrictedUnit L b a N₀ Set.univ).val =
      ((∏' p : Nat.Primes, L.localResidueDensity M p : ℝ) : ℂ) := by
  unfold rankFourFiniteDensity
  simp_rw [finiteTubeMass_finiteSectionAverage_unit L b a _ _ x₀ hx₀, residueRestrictedIndicator_univ]
  exact (L.tendsto_factorial_mul_congruenceIntegral_tprod_localResidueDensity hn hM).limUnder_eq

end Laws

/-- The rank-four density at an integral representative `z`: `x₀ = z`, `M = Q(z)`, and
`c_∞ = Re d_∞(orbit test)(a_∞)`. -/
def rankFourDensityAt (L : PositiveDefiniteIntegralLattice (n + 1)) (hn : 3 ≤ n) {w : ℝ} (hw : 0 < w)
    (z : Fin (n + 1) → ℤ) (hz : L.quadForm z ≠ 0) :
    TracePositiveCoreDensity L w (algebraMap ℚ RationalAdele
      (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm (fun i ↦ (z i : ℚ)))) :=
  rankFourTracePositiveDensity L hn hz hw.le (fun i ↦ (z i : ℝ)) (realQuadraticFormValue_intVector L z)
    (cInf := (L.rationalQuadraticSpaceMatrix.realLocalValueDensity
      (gaussianOrbitTestRealFactor L w (algebraMap ℚ RationalAdele
        (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm (fun i ↦ (z i : ℚ)))))
      (rationalAdeleRealScalar (algebraMap ℚ RationalAdele
        (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm (fun i ↦ (z i : ℚ)))))).re)
    (by
      have hpos : 0 < rationalAdeleRealScalar (algebraMap ℚ RationalAdele
          (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm (fun i ↦ (z i : ℚ)))) := by
        change 0 < rationalInfiniteAdeleContinuousAddEquivReal (algebraMap ℚ RationalInfiniteAdele _)
        rw [rationalInfiniteAdeleContinuousAddEquivReal_algebraMap, eq_ratCast, Rat.cast_pos]
        refine L.nativeRationalQuadraticForm_pos_of_ne_zero ?_
        rw [L.nativeRationalQuadraticForm_intVector z]
        exact_mod_cast hz
      rw [re_realLocalValueDensity_gaussianOrbitTestRealFactor L hw (by omega) _ hpos]
      have hdet : (0 : ℝ) < (L.polarRealDeterminantScale : ℝ)⁻¹ :=
        inv_pos.2 (by exact_mod_cast L.polarRealDeterminantScale_pos)
      have hΓ : 0 < Real.Gamma (((n + 1 : ℕ) : ℝ) / 2) := Real.Gamma_pos_of_pos (by positivity)
      positivity)
    _ (by rw [L.nativeRationalQuadraticForm_intVector z])

theorem rankFourDensityAt_apply (L : PositiveDefiniteIntegralLattice (n + 1)) (hn : 3 ≤ n) {w : ℝ} (hw : 0 < w)
    (z : Fin (n + 1) → ℤ) (hz : L.quadForm z ≠ 0) (f : realGaussianCore L w) :
    (rankFourDensityAt L hn hw z hz).toLinearMap f =
      (L.rationalQuadraticSpaceMatrix.realLocalValueDensity
        (gaussianOrbitTestRealFactor L w (algebraMap ℚ RationalAdele
          (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm (fun i ↦ (z i : ℚ)))))
        (rationalAdeleRealScalar (algebraMap ℚ RationalAdele
          (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm (fun i ↦ (z i : ℚ)))))).re *
        (rankFourFiniteDensity L (fun i ↦ (z i : ℝ)) (L.quadForm z) f.val).re :=
  rfl

theorem realQuadraticFormValue_intVector_eq_realScalar (L : PositiveDefiniteIntegralLattice n) (z : Fin n → ℤ) :
    L.rationalQuadraticSpaceMatrix.realQuadraticFormValue (fun i ↦ (z i : ℝ)) =
      rationalInfiniteAdeleContinuousAddEquivReal (algebraMap ℚ RationalAdele
        (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm (fun i ↦ (z i : ℚ)))).1 := by
  rw [realQuadraticFormValue_intVector]
  change _ = rationalInfiniteAdeleContinuousAddEquivReal (algebraMap ℚ RationalInfiniteAdele _)
  rw [rationalInfiniteAdeleContinuousAddEquivReal_algebraMap, L.nativeRationalQuadraticForm_intVector z]
  simp

set_option maxHeartbeats 1600000 in
/-- The rank-four shell identity at an integral representative: in every lattice rank at least four,
`Θ_b(ψ) · τ(Spin_L) = τ(Spin_{L_W}) · ofReal(D⁴_z(ψ))` for every nonnegative core test `ψ`. -/
theorem exists_complement_representedNormTheta_mul_spinTamagawa_eq_of_integral_rankFour
    {s : ℕ} (L : PositiveDefiniteIntegralLattice (s + 2 + 1)) (hs : 1 ≤ s)
    (instA : Fintype L.ConcreteProperRationalDoubleCosetSet) {PA : ℝ} (hPA0 : 0 < PA)
    (hA : massLocalInverseProductTendsTo L PA)
    {w : ℝ} (hw : 0 < w)
    (b : L.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm)
    (z : Fin (s + 2 + 1) → ℤ)
    (hz : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm (fun i ↦ (z i : ℚ)) = b.1)
    (ψ : realGaussianCore L w) (hψ : ∀ y, 0 ≤ ψ.val y) :
    ∃ (hz0 : L.quadForm z ≠ 0) (LW : PositiveDefiniteIntegralLattice (s + 2))
      (_ : LW.rationalQuadraticSpaceMatrix.quadraticForm.IsometryEquiv
        (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm.orthogonalRestriction
          (fun i ↦ (z i : ℚ))))
      (instL : Fintype LW.ConcreteProperRationalDoubleCosetSet)
      (PL : ℝ) (hPL0 : 0 < PL) (hL : massLocalInverseProductTendsTo LW PL),
      L.probabilityNormalizedFullAdelicCliffordGeneralSpinRepresentedNormTheta
          (by omega : 1 ≤ s + 1) instA hPA0 hA b (fun y ↦ ENNReal.ofReal (ψ.val y))
          rationalIdeleClassUnitLogCutoff *
        (cliffordSpinCandidateRawOnoTamagawaDataOfLattice L (by omega) instA hPA0 hA).spinTamagawaNumberENNReal =
      (cliffordSpinCandidateRawOnoTamagawaDataOfLattice LW (by omega) instL hPL0 hL).spinTamagawaNumberENNReal *
        ENNReal.ofReal ((rankFourDensityAt L (by omega) hw z hz0).toLinearMap ψ) := by
  have hz0 : L.quadForm z ≠ 0 := by
    intro h
    apply b.2.1
    rw [← hz, L.nativeRationalQuadraticForm_intVector z, h, Int.cast_zero]
  refine ⟨hz0, ?_⟩
  have hx₀ := realQuadraticFormValue_intVector_eq_realScalar L z
  have hDinv : (rankFourDensityAt L (by omega : 3 ≤ s + 2) hw z hz0).IsSpecialOrthogonalInvariant := by
    unfold rankFourDensityAt
    exact rankFourTracePositiveDensity_isSpecialOrthogonalInvariant L _ hz0 hw.le _ _ _ _ _
  have hDloc : (rankFourDensityAt L (by omega : 3 ≤ s + 2) hw z hz0).HasLocalRestrictionLaw
      (L.quadForm z) := by
    intro Pr e R hPr gF gR hgF0 hgFt hloc hFne
    haveI : NeZero (localRestrictionLevel Pr e) :=
      ⟨localRestrictionLevel_ne_zero fun p hp ↦ (hPr p hp).1⟩
    rw [rankFourDensityAt_apply, rankFourDensityAt_apply,
      rankFourFiniteDensity_unit_localRestriction L (by omega) hz0 _ _ hx₀ Pr e R hPr gF gR hgF0 hgFt
        hloc hFne, rankFourFiniteDensity_unit_univ L (by omega) hz0 _ _ hx₀, Complex.re_ofReal_mul]
    ring
  have hDcar : (rankFourDensityAt L (by omega : 3 ≤ s + 2) hw z hz0).toLinearMap
      (gaussianResidueRestrictedUnit L w (algebraMap ℚ RationalAdele
        (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm (fun i ↦ (z i : ℚ)))) 1 Set.univ) =
      (L.rationalQuadraticSpaceMatrix.realLocalValueDensity
          (gaussianOrbitTestRealFactor L w (algebraMap ℚ RationalAdele
            (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm (fun i ↦ (z i : ℚ)))))
          (rationalAdeleRealScalar (algebraMap ℚ RationalAdele
            (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm (fun i ↦ (z i : ℚ)))))).re *
        ∏' p : Nat.Primes, L.localResidueDensity (L.quadForm z) p := by
    rw [rankFourDensityAt_apply, rankFourFiniteDensity_unit_univ L (by omega) hz0 _ _ hx₀,
      Complex.ofReal_re]
  exact exists_complement_representedNormTheta_mul_spinTamagawa_eq_of_integral_of_density L hs instA
    hPA0 hA hw b z hz _ hDinv hDloc hDcar ψ hψ

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
