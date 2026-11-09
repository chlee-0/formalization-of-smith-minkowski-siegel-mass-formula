import SMSFormula.AdelicGaussianTracePositiveDensityMeasure
import SMSFormula.AdelicGaussianFiberEulerRatioIntegralAssembly
import SMSFormula.AdelicGaussianFiberInvariance
import SMSFormula.AdelicGaussianIntegralCarrierEulerProduct

/-!
# The shell identity for any trace-positive invariant core density (rank at least four)

Let `D` be a trace-positive core density at `a = Q(z)` (`TracePositiveCoreDensity`) that is
`SO(𝔸)`-invariant and obeys the two unit-test laws of the Fourier density:
* the replacement law `D(unit_R) = (∏ gR/∏ gF) · D(unit_univ)` for CRT residue restrictions whose
  counts are eventually in the ratio `gR_p : gF_p`;
* the Euler law `D(unit_univ) = Re d_∞(a_∞) · ∏'_p δ_p(M)` at level one.
Then its Riesz fiber measure satisfies the two Euler laws of carried sets, and for every
nonnegative core test `ψ`

`Θ_b(ψ) · τ(Spin_L) = τ(Spin_{L_W}) · ofReal(D(ψ))`

in every lattice rank at least four
(`exists_complement_representedNormTheta_mul_spinTamagawa_eq_of_integral_of_density`).  This is the
`exists_complement_representedNormTheta_mul_spinTamagawa_eq_of_integral` with the Fourier
density replaced by `D`; in rank at least five the Fourier density satisfies all hypotheses
(`realValueTracePositiveDensity_isSpecialOrthogonalInvariant`, the replacement lemma and the
Euler product).  Nothing is chosen: `D` and its laws are supplied.
-/

noncomputable section

open MeasureTheory PositiveDefiniteIntegralLattice RationalQuadraticSpaceMatrix
open scoped ENNReal

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

variable {n : ℕ}

/-- The Fourier density is `SO(𝔸)`-invariant (`realValueDensity_comp_specialOrthogonal`). -/
theorem realValueTracePositiveDensity_isSpecialOrthogonalInvariant (L : PositiveDefiniteIntegralLattice n)
    (hn : 4 < n) {b : ℝ} (hb : 0 < b) (a : RationalAdele) :
    (realValueTracePositiveDensity L hn hb a).IsSpecialOrthogonalInvariant := fun h f ↦
  congrFun (L.rationalQuadraticSpaceMatrix.realValueDensity_comp_specialOrthogonal h f.val) a

namespace TracePositiveCoreDensity

variable {L : PositiveDefiniteIntegralLattice (n + 1)} {b : ℝ} {a : RationalAdele}
variable (D : TracePositiveCoreDensity L b a)

/-- The replacement law of the density at the lattice value `M`. -/
def HasLocalRestrictionLaw (M : ℤ) : Prop :=
  ∀ (Pr : Finset ℕ) (e : ℕ → ℕ) (R : ∀ p : ℕ, Set (Fin (n + 1) → ZMod (p ^ e p)))
    (hPr : ∀ p ∈ Pr, p.Prime ∧ 1 ≤ e p) (gF gR : ℕ → ℝ≥0∞),
    (∀ p ∈ Pr, gF p ≠ 0) → (∀ p ∈ Pr, gF p ≠ ⊤) →
    (∀ p ∈ Pr, ∀ᶠ v : ℕ in Filter.atTop,
      (L.restrictedResidueCount M Pr e R (p ^ v) : ℝ≥0∞) * gF p =
        (L.fullResidueCount M (p ^ v) : ℝ≥0∞) * gR p) →
    (∀ p ∈ Pr, ∀ᶠ v : ℕ in Filter.atTop, L.fullResidueCount M (p ^ v) ≠ 0) →
    haveI : NeZero (localRestrictionLevel Pr e) :=
      ⟨localRestrictionLevel_ne_zero fun p hp ↦ (hPr p hp).1⟩
    D.toLinearMap (gaussianResidueRestrictedUnit L b a (localRestrictionLevel Pr e)
        (localRestrictionSet Pr e R)) =
      ((∏ p ∈ Pr, gR p) / ∏ p ∈ Pr, gF p).toReal *
        D.toLinearMap (gaussianResidueRestrictedUnit L b a (localRestrictionLevel Pr e) Set.univ)

/-- The Riesz fiber measure of a density with the replacement law obeys the local-restriction law
of carried fiber sets. -/
theorem fiberMeasure_localRestriction (hb : 0 < b) {M : ℤ} (hD : D.HasLocalRestrictionLaw M)
    (Pr : Finset ℕ) (e : ℕ → ℕ) (R : ∀ p : ℕ, Set (Fin (n + 1) → ZMod (p ^ e p)))
    (hPr : ∀ p ∈ Pr, p.Prime ∧ 1 ≤ e p) (gF gR : ℕ → ℝ≥0∞)
    (hgF0 : ∀ p ∈ Pr, gF p ≠ 0) (hgFt : ∀ p ∈ Pr, gF p ≠ ⊤)
    (hloc : ∀ p ∈ Pr, ∀ᶠ v : ℕ in Filter.atTop,
      (L.restrictedResidueCount M Pr e R (p ^ v) : ℝ≥0∞) * gF p =
        (L.fullResidueCount M (p ^ v) : ℝ≥0∞) * gR p)
    (hFne : ∀ p ∈ Pr, ∀ᶠ v : ℕ in Filter.atTop, L.fullResidueCount M (p ^ v) ≠ 0) :
    haveI : NeZero (localRestrictionLevel Pr e) :=
      ⟨localRestrictionLevel_ne_zero fun p hp ↦ (hPr p hp).1⟩
    D.fiberMeasure hb (fiberResidueRestrictedSet L a (localRestrictionLevel Pr e)
        (localRestrictionSet Pr e R)) =
      ((∏ p ∈ Pr, gR p) / ∏ p ∈ Pr, gF p) * D.fiberMeasure hb (fiberDividedCarrier L a 1) := by
  haveI : NeZero (localRestrictionLevel Pr e) :=
    ⟨localRestrictionLevel_ne_zero fun p hp ↦ (hPr p hp).1⟩
  have hgRt : ∀ p ∈ Pr, gR p ≠ ⊤ := fun p hp ↦ ne_top_of_eventually_count_mul_eq (hgFt p hp)
    (hloc p hp) (hFne p hp)
  have hratio : (∏ p ∈ Pr, gR p) / ∏ p ∈ Pr, gF p ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.prod_ne_top hgRt) (Finset.prod_ne_zero_iff.2 hgF0)
  rw [D.fiberMeasure_fiberResidueRestrictedSet hb,
    D.fiberMeasure_fiberDividedCarrier_one hb (localRestrictionLevel Pr e),
    hD Pr e R hPr gF gR hgF0 hgFt hloc hFne, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal hratio]

end TracePositiveCoreDensity

/-- The Fourier density has the replacement law (rank at least five): the
`realValueDensity_gaussianResidueRestrictedUnit_localRestriction`. -/
theorem realValueTracePositiveDensity_hasLocalRestrictionLaw (L : PositiveDefiniteIntegralLattice (n + 1))
    (hn : 4 < n + 1) {b : ℝ} (hb : 0 < b) (a : RationalAdele) (M : ℤ)
    (ha : a.2 = algebraMap ℚ RationalFiniteAdele ((M : ℤ) : ℚ)) :
    (realValueTracePositiveDensity L hn hb a).HasLocalRestrictionLaw M :=
  fun Pr e R hPr gF gR hgF0 hgFt hloc hFne ↦
    realValueDensity_gaussianResidueRestrictedUnit_localRestriction L hn b a M ha Pr e R hPr gF gR
      hgF0 hgFt hloc hFne

local instance tpsDecidableEq : DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

set_option maxHeartbeats 1600000 in
/-- The shell identity for a supplied trace-positive invariant core density, rank at least four:
`Θ_b(ψ) · τ_L = τ_{L_W} · ofReal(D(ψ))` for every nonnegative core test `ψ`. -/
theorem exists_complement_representedNormTheta_mul_spinTamagawa_eq_of_integral_of_density
    {s : ℕ} (L : PositiveDefiniteIntegralLattice (s + 2 + 1)) (hs : 1 ≤ s)
    (instA : Fintype L.ConcreteProperRationalDoubleCosetSet) {PA : ℝ} (hPA0 : 0 < PA)
    (hA : massLocalInverseProductTendsTo L PA)
    {w : ℝ} (hw : 0 < w)
    (b : L.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm)
    (z : Fin (s + 2 + 1) → ℤ)
    (hz : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm (fun i ↦ (z i : ℚ)) = b.1)
    (D : TracePositiveCoreDensity L w (algebraMap ℚ RationalAdele
      (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm (fun i ↦ (z i : ℚ)))))
    (hDinv : D.IsSpecialOrthogonalInvariant) (hDloc : D.HasLocalRestrictionLaw (L.quadForm z))
    (hDcar : D.toLinearMap (gaussianResidueRestrictedUnit L w (algebraMap ℚ RationalAdele
        (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm (fun i ↦ (z i : ℚ)))) 1
          Set.univ) =
      (L.rationalQuadraticSpaceMatrix.realLocalValueDensity
          (gaussianOrbitTestRealFactor L w (algebraMap ℚ RationalAdele
            (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm (fun i ↦ (z i : ℚ)))))
          (rationalAdeleRealScalar (algebraMap ℚ RationalAdele
            (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm (fun i ↦ (z i : ℚ)))))).re *
        ∏' p : Nat.Primes, L.localResidueDensity (L.quadForm z) p)
    (ψ : realGaussianCore L w) (hψ : ∀ y, 0 ≤ ψ.val y) :
    ∃ (LW : PositiveDefiniteIntegralLattice (s + 2))
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
        ENNReal.ofReal (D.toLinearMap ψ) := by
  haveI := D.smulInvariantMeasure_fiberMeasure hw hDinv
  have hcar : D.fiberMeasure hw (fiberDividedCarrier L (algebraMap ℚ RationalAdele
      (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm (fun i ↦ (z i : ℚ)))) 1) =
      ENNReal.ofReal ((L.rationalQuadraticSpaceMatrix.realLocalValueDensity
          (gaussianOrbitTestRealFactor L w (algebraMap ℚ RationalAdele
            (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm (fun i ↦ (z i : ℚ)))))
          (rationalAdeleRealScalar (algebraMap ℚ RationalAdele
            (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm (fun i ↦ (z i : ℚ)))))).re *
        ∏' p : Nat.Primes, L.localResidueDensity (L.quadForm z) p) := by
    rw [D.fiberMeasure_fiberDividedCarrier_one hw 1, hDcar]
  have hψm : Measurable (fun y ↦ ENNReal.ofReal (ψ.val y)) :=
    (continuous_of_mem_realGaussianCore L w ψ.2).measurable.ennreal_ofReal
  obtain ⟨LW, eW, instL, PL, hPL0, hL, h⟩ :=
    exists_complement_representedNormTheta_mul_spinTamagawa_eq_of_integral_of_measure L hs instA
      hPA0 hA hw b z hz (D.fiberMeasure hw) (D.fiberMeasure_localRestriction hw hDloc) hcar
      (fun y ↦ ENNReal.ofReal (ψ.val y)) hψm
  refine ⟨LW, eW, instL, PL, hPL0, hL, ?_⟩
  rw [h, D.lintegral_fiberMeasure_core hw ψ hψ]

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
