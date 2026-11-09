import SMSFormula.RationalCliffordSpinCandidateCanonicalRightQuotient

/-!
# Uniqueness of the raw Clifford--Spin normalization

The raw finite scale attached to a fixed rational quadratic-space matrix is
forced by its convergence certificate: two certified scales have equal
inverses by uniqueness of limits and hence are equal.  It follows that any
two raw Ono data on the same matrix have literally equal Spin ambient
measures.  Exact fundamental-domain uniqueness then identifies their quotient
measures and their Spin Tamagawa numbers.

This removes dependence on the choice of raw datum while keeping the rational
coordinate presentation fixed.  It does not compare rationally isometric
matrix presentations, choose a complement lattice, or assert that the common
Spin Tamagawa number is one.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open MeasureTheory
open scoped ENNReal NNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} {V : RationalQuadraticSpaceMatrix n}

namespace CliffordSpinCandidateRawDifferentialVolumeProductCertificate

/-- On a fixed rational matrix presentation, convergence of the inverse
integral-volume products determines the certified finite scale uniquely. -/
theorem finiteScale_eq
    {c d : ℝ≥0}
    (C : V.CliffordSpinCandidateRawDifferentialVolumeProductCertificate c)
    (E : V.CliffordSpinCandidateRawDifferentialVolumeProductCertificate d) :
    c = d := by
  have hinv : (c : ℝ≥0∞)⁻¹ = (d : ℝ≥0∞)⁻¹ :=
    tendsto_nhds_unique C.inverseVolumeProduct_tendsto
      E.inverseVolumeProduct_tendsto
  have hcoe : (c : ℝ≥0∞) = (d : ℝ≥0∞) := by
    simpa only [inv_inv] using congrArg Inv.inv hinv
  exact ENNReal.coe_injective hcoe

end CliffordSpinCandidateRawDifferentialVolumeProductCertificate

namespace CliffordSpinCandidateRawOnoTamagawaData

/-- The Spin finite scale is independent of the supplied raw Ono datum on a
fixed rational quadratic-space matrix. -/
theorem spinFiniteScale_eq
    (D E : V.CliffordSpinCandidateRawOnoTamagawaData) :
    D.spinFiniteScale = E.spinFiniteScale :=
  D.spinRaw.volumeProductCertificate.finiteScale_eq
    E.spinRaw.volumeProductCertificate

/-- Rawness and scale uniqueness force equality of the two Spin ambient
measures, regardless of the special-orthogonal fields in the data. -/
theorem spinData_adelicMeasure_eq
    (D E : V.CliffordSpinCandidateRawOnoTamagawaData) :
    D.spinData.adelicMeasure = E.spinData.adelicMeasure := by
  rw [D.spinRaw.adelicMeasure_eq, E.spinRaw.adelicMeasure_eq,
    D.spinFiniteScale_eq E]

/-- The exact Spin fundamental domain forces equality of the corresponding
raw quotient measures once their ambient measures agree. -/
theorem spinData_quotientMeasure_eq
    (D E : V.CliffordSpinCandidateRawOnoTamagawaData) :
    D.spinData.quotientMeasure = E.spinData.quotientMeasure := by
  rw [D.spinData.quotientMeasure_eq_fundamentalDomain,
    E.spinData.quotientMeasure_eq_fundamentalDomain,
    D.spinData_adelicMeasure_eq E]

/-- The raw Spin Tamagawa number depends only on the fixed rational matrix
presentation, not on which certified raw Ono datum supplies it. -/
theorem spinTamagawaNumberENNReal_eq
    (D E : V.CliffordSpinCandidateRawOnoTamagawaData) :
    D.spinTamagawaNumberENNReal = E.spinTamagawaNumberENNReal := by
  unfold spinTamagawaNumberENNReal
    CliffordSpinCandidateMeasurableWeilMeasureData.quotientVolumeENNReal
  rw [D.spinData_quotientMeasure_eq E]

end CliffordSpinCandidateRawOnoTamagawaData
end RationalQuadraticSpaceMatrix
