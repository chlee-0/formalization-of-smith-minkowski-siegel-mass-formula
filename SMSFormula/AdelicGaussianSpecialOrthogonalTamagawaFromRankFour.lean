import SMSFormula.AdelicGaussianCapstoneIntegralAssembly
import SMSFormula.RationalCliffordGeneralSpinRelativeUnitCutoff
import SMSFormula.RationalCliffordSpinCandidateRawQuotientVolumePositive

/-!
# `τ(SO) = 2` in every rank `≥ 4` from the rank-four Spin base case

The relative comparison `τ(SO) = 2 · τ(Spin)` holds for the exact lattice raw datum in every rank
`≥ 3` (`cliffordSpinCandidateRawOnoTamagawaDataOfLattice_isOnoRelativeComparison`). With the rank
induction `spinTamagawaNumberENNReal_eq_one_of_rankFour`, the raw `SO` differential datum
has Tamagawa number two in every rank `≥ 4`, given only `τ(Spin) = 1` in rank four. With the
rank-three base case as well (`RankThreeSpinTamagawaOne`), the lattice-level `τ(SO) = 2` holds in
every rank `≥ 3` (`..._eq_two_of_lowRankSpin`), which
`RationalSpecialOrthogonalTamagawaNumberFromSpin` uses. Nothing is chosen.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

/-- The rank-three Spin base case: `τ(Spin) = 1` for the exact raw datum of every rank-three
lattice. -/
def RankThreeSpinTamagawaOne : Prop :=
  ∀ (L : PositiveDefiniteIntegralLattice 3) (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    (P : ℝ) (hP : 0 < P) (hconv : massLocalInverseProductTendsTo L P),
    (cliffordSpinCandidateRawOnoTamagawaDataOfLattice L le_rfl inst hP hconv).spinTamagawaNumberENNReal
      = 1

/-- The rank-four Spin base case: `τ(Spin) = 1` for the exact raw datum of every rank-four lattice. -/
def RankFourSpinTamagawaOne : Prop :=
  ∀ (L : PositiveDefiniteIntegralLattice 4) (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    (P : ℝ) (hP : 0 < P) (hconv : massLocalInverseProductTendsTo L P),
    (cliffordSpinCandidateRawOnoTamagawaDataOfLattice L (by omega) inst hP hconv).spinTamagawaNumberENNReal
      = 1

end PositiveDefiniteIntegralLattice

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

open RationalQuadraticSpaceMatrix

/-- `τ(SO) = 2` in every rank `≥ 4`, given `τ(Spin) = 1` in rank four (relative comparison and
the rank induction). -/
theorem rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasurableWeilMeasureData_tamagawaNumberENNReal_eq_two_of_rankFour
    (h4 : RankFourSpinTamagawaOne)
    (k : ℕ) (L : PositiveDefiniteIntegralLattice (k + 4)) (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P) (hconv : massLocalInverseProductTendsTo L P) :
    (L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasurableWeilMeasureData
      inst hP).tamagawaNumberENNReal = 2 := by
  have hrel := L.cliffordSpinCandidateRawOnoTamagawaDataOfLattice_isOnoRelativeComparison
    (by omega) inst hP hconv
  have h := (cliffordSpinCandidateRawOnoTamagawaDataOfLattice L (by omega) inst hP hconv)
    |>.specialOrthogonalTamagawaNumberENNReal_eq_two_mul_spin_of_onoRelativeComparison hrel
  rw [spinTamagawaNumberENNReal_eq_one_of_rankFour h4 k L inst P hP hconv, mul_one] at h
  exact h

/-- `τ(SO) = 2` in every rank `≥ 3` from the rank-three and rank-four Spin base cases
(relative comparison and the rank induction). -/
theorem rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasurableWeilMeasureData_tamagawaNumberENNReal_eq_two_of_lowRankSpin
    (h3 : RankThreeSpinTamagawaOne) (h4 : RankFourSpinTamagawaOne)
    {n : ℕ} (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)] (hn : 3 ≤ n)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P) (hconv : massLocalInverseProductTendsTo L P) :
    (L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasurableWeilMeasureData
      inst hP).tamagawaNumberENNReal = 2 := by
  rcases Nat.eq_or_lt_of_le hn with h3n | h4n
  · subst h3n
    have hrel := L.cliffordSpinCandidateRawOnoTamagawaDataOfLattice_isOnoRelativeComparison
      le_rfl inst hP hconv
    have h := (cliffordSpinCandidateRawOnoTamagawaDataOfLattice L le_rfl inst hP hconv)
      |>.specialOrthogonalTamagawaNumberENNReal_eq_two_mul_spin_of_onoRelativeComparison hrel
    rw [h3 L inst P hP hconv, mul_one] at h
    exact h
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
    exact rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasurableWeilMeasureData_tamagawaNumberENNReal_eq_two_of_rankFour
      h4 k L inst hP hconv

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
