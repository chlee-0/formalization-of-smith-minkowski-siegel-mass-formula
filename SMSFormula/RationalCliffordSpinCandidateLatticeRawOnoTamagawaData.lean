import SMSFormula.RationalCliffordSpinCandidateOnoRelativeTamagawaData

/-!
# Exact lattice-backed raw Spin--SO Ono datum

This module packages the Schulze--Pillot inverse-product limit used by the
lattice mass formula into the raw Spin--SO Ono datum.  Its special-orthogonal
component is definitionally the lattice measurable-Weil datum; no other limit
or normalization is chosen.
-/

noncomputable section

open RationalQuadraticSpaceMatrix
open PositiveDefiniteIntegralLattice
open scoped NNReal

namespace RationalQuadraticSpaceMatrix

/-- The syntactic `r + 2` convergence endpoint, re-expressed at an arbitrary
rank with the exact hypothesis needed by its proof. -/
theorem
    exists_cliffordSpinCandidateRawDifferentialVolumeProductCertificate_of_rankAtLeastTwo
    {n : ℕ} (L : PositiveDefiniteIntegralLattice n) (hn : 2 ≤ n)
    {P : ℝ} (hP : 0 < P)
    (hconv : massLocalInverseProductTendsTo L P) :
    ∃ finiteScale : ℝ≥0,
      L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawDifferentialVolumeProductCertificate
        finiteScale := by
  obtain ⟨r, rfl⟩ : ∃ r, n = r + 2 := ⟨n - 2, by omega⟩
  exact
    exists_cliffordSpinCandidateRawDifferentialVolumeProductCertificate_of_massLocalInverseProductTendsTo
      (r := r) L hP hconv

end RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The positive finite Spin scale determined by the literal lattice
inverse-product convergence certificate. -/
noncomputable def cliffordSpinCandidateRawFiniteScaleOfLattice
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n)
    {P : ℝ} (hP : 0 < P)
    (hconv : massLocalInverseProductTendsTo L P) : ℝ≥0 :=
  Classical.choose
    (RationalQuadraticSpaceMatrix.exists_cliffordSpinCandidateRawDifferentialVolumeProductCertificate_of_rankAtLeastTwo
      L (by omega) hP hconv)

/-- The certificate carried by the exact lattice-determined Spin scale. -/
theorem cliffordSpinCandidateRawFiniteScaleOfLattice_certificate
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n)
    {P : ℝ} (hP : 0 < P)
    (hconv : massLocalInverseProductTendsTo L P) :
    L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawDifferentialVolumeProductCertificate
      (cliffordSpinCandidateRawFiniteScaleOfLattice L hn hP hconv) :=
  Classical.choose_spec
    (RationalQuadraticSpaceMatrix.exists_cliffordSpinCandidateRawDifferentialVolumeProductCertificate_of_rankAtLeastTwo
      L (by omega) hP hconv)

/-- The actual raw Spin--SO datum attached to the same literal lattice datum
and inverse-product limit used by the final mass-formula path. -/
noncomputable def cliffordSpinCandidateRawOnoTamagawaDataOfLattice
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)] (hn : 3 ≤ n)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P)
    (hconv : massLocalInverseProductTendsTo L P) :
    L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData := by
  let finiteScale :=
    cliffordSpinCandidateRawFiniteScaleOfLattice L hn hP hconv
  exact
    { specialOrthogonalData :=
        L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasurableWeilMeasureData
          inst hP
      specialOrthogonalFiniteScale :=
        L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume P
      spinFiniteScale := finiteScale
      spinData :=
        L.rationalQuadraticSpaceMatrix.fullAdelicCliffordSpinCandidateRawDifferentialMeasurableWeilData
          finiteScale
      specialOrthogonalRaw :=
        L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasurableWeilMeasureData_isRawInvariantDifferentialWithScale
          inst hP hconv
      spinRaw :=
        L.rationalQuadraticSpaceMatrix.fullAdelicCliffordSpinCandidateRawDifferentialMeasurableWeilData_isRawWithScale
          finiteScale
          (cliffordSpinCandidateRawFiniteScaleOfLattice_certificate
            L hn hP hconv) }

@[simp] theorem
    cliffordSpinCandidateRawOnoTamagawaDataOfLattice_specialOrthogonalData
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)] (hn : 3 ≤ n)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P)
    (hconv : massLocalInverseProductTendsTo L P) :
    (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
      L hn inst hP hconv).specialOrthogonalData =
      L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasurableWeilMeasureData
        inst hP := rfl

@[simp] theorem
    cliffordSpinCandidateRawOnoTamagawaDataOfLattice_specialOrthogonalFiniteScale
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)] (hn : 3 ≤ n)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P)
    (hconv : massLocalInverseProductTendsTo L P) :
    (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
      L hn inst hP hconv).specialOrthogonalFiniteScale =
      L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume P := rfl

@[simp] theorem
    cliffordSpinCandidateRawOnoTamagawaDataOfLattice_spinFiniteScale
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)] (hn : 3 ≤ n)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P)
    (hconv : massLocalInverseProductTendsTo L P) :
    (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
      L hn inst hP hconv).spinFiniteScale =
      cliffordSpinCandidateRawFiniteScaleOfLattice L hn hP hconv := rfl

@[simp] theorem
    cliffordSpinCandidateRawOnoTamagawaDataOfLattice_spinData
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)] (hn : 3 ≤ n)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P)
    (hconv : massLocalInverseProductTendsTo L P) :
    (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
      L hn inst hP hconv).spinData =
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordSpinCandidateRawDifferentialMeasurableWeilData
        (cliffordSpinCandidateRawFiniteScaleOfLattice L hn hP hconv) := rfl

end PositiveDefiniteIntegralLattice
