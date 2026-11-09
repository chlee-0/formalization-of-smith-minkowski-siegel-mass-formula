import SMSFormula.RationalCliffordSpinCandidateLatticeRawOnoTamagawaData
import SMSFormula.RationalCliffordSpinCandidatePlacewiseFiniteSheetHaar

/-!
# Exact comparison of the lattice Spin and special-orthogonal finite scales

The raw Spin scale chosen by the exact lattice Ono datum is not an arbitrary
Haar scalar.  Its inverse is the limit of the Spin integral reciprocal-volume
cutoffs.  Outside a fixed finite set those cutoffs agree with the
special-orthogonal cutoffs; the exceptional discrepancy is a named
finite correction.  Uniqueness of limits therefore identifies the chosen
Spin scale with the lattice `SO` scale exactly.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open scoped ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

set_option maxHeartbeats 800000

/-- The inverse of the exact lattice Spin scale is the exceptional correction
times the inverse of the special-orthogonal finite scale. -/
theorem cliffordSpinCandidateRawFiniteScaleOfLattice_inv_eq_correction_mul_so_inv
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n)
    {P : ℝ} (hP : 0 < P)
    (hconv : massLocalInverseProductTendsTo L P) :
    ((cliffordSpinCandidateRawFiniteScaleOfLattice
        L hn hP hconv : ℝ≥0∞))⁻¹ =
      L.rationalQuadraticSpaceMatrix.specialOrthogonalToCliffordSpinCandidateInverseVolumeCorrection *
        (L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume P)⁻¹ := by
  letI : NeZero n := ⟨by omega⟩
  let V := L.rationalQuadraticSpaceMatrix
  let spinScale := cliffordSpinCandidateRawFiniteScaleOfLattice L hn hP hconv
  let soInverse :=
    L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerInverseVolume P
  let correction :=
    V.specialOrthogonalToCliffordSpinCandidateInverseVolumeCorrection
  have hSpin :
      Filter.Tendsto
        (fun N : ℕ => V.cliffordSpinCandidateIntegralInverseVolumePartialProduct N)
        Filter.atTop (nhds (spinScale : ℝ≥0∞)⁻¹) :=
    (cliffordSpinCandidateRawFiniteScaleOfLattice_certificate
      L hn hP hconv).inverseVolumeProduct_tendsto
  have hSO :=
    L.localPadicSpecialOrthogonalDifferentialStabilizerInverseVolumeProductTendsTo_finiteStabilizerInverseVolume_of_massLocalInverseProductTendsTo
      hconv
  have hSOHeight :
      Filter.Tendsto
        (fun N : ℕ =>
          V.cliffordSpinCandidateSpecialOrthogonalIntegralInverseVolumePartialProduct N)
        Filter.atTop (nhds soInverse) := by
    refine Filter.Tendsto.congr' ?_ hSO
    filter_upwards with N
    exact
      (RationalQuadraticSpaceMatrix.cliffordSpinCandidateSpecialOrthogonalIntegralInverseVolumePartialProduct_eq_lattice
        L N).symm
  have hCorrectionTop : correction ≠ ⊤ :=
    V.specialOrthogonalToCliffordSpinCandidateInverseVolumeCorrection_ne_top
  have hScaled :
      Filter.Tendsto
        (fun N : ℕ => correction *
          V.cliffordSpinCandidateSpecialOrthogonalIntegralInverseVolumePartialProduct N)
        Filter.atTop (nhds (correction * soInverse)) :=
    ENNReal.Tendsto.const_mul hSOHeight (Or.inr hCorrectionTop)
  have hEventually :
      ∀ᶠ N : ℕ in Filter.atTop,
        V.cliffordSpinCandidateIntegralInverseVolumePartialProduct N =
          correction *
            V.cliffordSpinCandidateSpecialOrthogonalIntegralInverseVolumePartialProduct N := by
    obtain ⟨r, hr⟩ : ∃ r, n = r + 2 := ⟨n - 2, by omega⟩
    subst n
    filter_upwards
      [Filter.eventually_ge_atTop
        V.cliffordSpinCandidateIntegralVolumeComparisonBadPlacesCutoff]
      with N hN
    exact
      RationalQuadraticSpaceMatrix.cliffordSpinCandidateIntegralInverseVolumePartialProduct_eq_correction_mul_specialOrthogonal_of_cutoff_le
        L hN
  have hSpinScaled :
      Filter.Tendsto
        (fun N : ℕ => V.cliffordSpinCandidateIntegralInverseVolumePartialProduct N)
        Filter.atTop (nhds (correction * soInverse)) :=
    hScaled.congr' (by
      filter_upwards [hEventually] with N hN
      exact hN.symm)
  have hlimit : (spinScale : ℝ≥0∞)⁻¹ = correction * soInverse :=
    tendsto_nhds_unique hSpin hSpinScaled
  simpa [spinScale, correction, soInverse,
    L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerInverseVolume_eq_inv_volume]
    using hlimit

/-- Datum-facing form of the exact inverse-scale comparison. -/
theorem cliffordSpinCandidateRawOnoTamagawaDataOfLattice_spinScale_inv_eq_correction_mul_soScale_inv
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)] (hn : 3 ≤ n)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P)
    (hconv : massLocalInverseProductTendsTo L P) :
    (((cliffordSpinCandidateRawOnoTamagawaDataOfLattice
        L hn inst hP hconv).spinFiniteScale : ℝ≥0∞))⁻¹ =
      L.rationalQuadraticSpaceMatrix.specialOrthogonalToCliffordSpinCandidateInverseVolumeCorrection *
        ((cliffordSpinCandidateRawOnoTamagawaDataOfLattice
          L hn inst hP hconv).specialOrthogonalFiniteScale)⁻¹ := by
  simpa using
    L.cliffordSpinCandidateRawFiniteScaleOfLattice_inv_eq_correction_mul_so_inv
      hn hP hconv

/-- Direct-scale form: multiplying the chosen raw Spin finite scale by the
exceptional correction gives the raw special-orthogonal scale. -/
theorem cliffordSpinCandidateRawFiniteScaleOfLattice_correction_mul_eq_soScale
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n)
    {P : ℝ} (hP : 0 < P)
    (hconv : massLocalInverseProductTendsTo L P) :
    L.rationalQuadraticSpaceMatrix.specialOrthogonalToCliffordSpinCandidateInverseVolumeCorrection *
        (cliffordSpinCandidateRawFiniteScaleOfLattice
          L hn hP hconv : ℝ≥0∞) =
      L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume P := by
  let c :=
    L.rationalQuadraticSpaceMatrix.specialOrthogonalToCliffordSpinCandidateInverseVolumeCorrection
  let s : ℝ≥0∞ :=
    cliffordSpinCandidateRawFiniteScaleOfLattice L hn hP hconv
  let t := L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume P
  have hc0 : c ≠ 0 :=
    L.rationalQuadraticSpaceMatrix.specialOrthogonalToCliffordSpinCandidateInverseVolumeCorrection_ne_zero
  have hctop : c ≠ ⊤ :=
    L.rationalQuadraticSpaceMatrix.specialOrthogonalToCliffordSpinCandidateInverseVolumeCorrection_ne_top
  have ht0 : t ≠ 0 :=
    L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume_ne_zero P
  have httop : t ≠ ⊤ :=
    L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume_ne_top hP
  have hinv : s⁻¹ = c * t⁻¹ := by
    simpa [c, s, t] using
      L.cliffordSpinCandidateRawFiniteScaleOfLattice_inv_eq_correction_mul_so_inv
        hn hP hconv
  have hs : s = c⁻¹ * t := by
    calc
      s = s⁻¹⁻¹ := (inv_inv s).symm
      _ = (c * t⁻¹)⁻¹ := congrArg Inv.inv hinv
      _ = c⁻¹ * (t⁻¹)⁻¹ := by
        rw [ENNReal.mul_inv (Or.inl hc0) (Or.inl hctop)]
      _ = c⁻¹ * t := by rw [inv_inv]
  change c * s = t
  rw [hs, ← mul_assoc, ENNReal.mul_inv_cancel hc0 hctop, one_mul]

/-- Datum-facing direct-scale comparison. -/
theorem cliffordSpinCandidateRawOnoTamagawaDataOfLattice_correction_mul_spinScale_eq_soScale
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)] (hn : 3 ≤ n)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P)
    (hconv : massLocalInverseProductTendsTo L P) :
    L.rationalQuadraticSpaceMatrix.specialOrthogonalToCliffordSpinCandidateInverseVolumeCorrection *
        ((cliffordSpinCandidateRawOnoTamagawaDataOfLattice
          L hn inst hP hconv).spinFiniteScale : ℝ≥0∞) =
      (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
        L hn inst hP hconv).specialOrthogonalFiniteScale := by
  simpa using
    L.cliffordSpinCandidateRawFiniteScaleOfLattice_correction_mul_eq_soScale
      hn hP hconv

end PositiveDefiniteIntegralLattice
