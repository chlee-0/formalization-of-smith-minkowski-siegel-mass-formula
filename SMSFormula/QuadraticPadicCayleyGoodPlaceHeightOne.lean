import SMSFormula.QuadraticPadicCayleyGoodPlaceLedger
import SMSFormula.RationalSpecialOrthogonalIntegralLocalFactorNormalization

/-! The good-place ledger in the height-one SO volumes. At a height-one prime
`v` with residue prime `p`, the integral subgroup `padicIntegralSpecialSubgroup`
of `SO(V)(ℚ_p)` is the adelic integral local factor
`heightOnePadicSpecialOrthogonalIntegralSubgroup V v`, and the SO differential
Haar is the `padicInvariantDifferentialGroupMeasure`. Hence the ledger masses
are the integral local volumes `heightOnePadicSpecialOrthogonalIntegralVolume`,
and at every non-exceptional prime

`vol_{V⊕⟨a⟩,v} / vol_{W,v} = |r| · ν(ℤ_p) · λ(X_a(ℤ_p))`.

The GSpin horizontal integral volumes and their central factors are not
compared here. No chart or normalization is chosen. -/
noncomputable section
open MeasureTheory Matrix PositiveDefiniteIntegralLattice Metric Set Filter QuadraticMap
open scoped Matrix.Norms.Operator ENNReal NNReal Topology

namespace RationalQuadraticSpaceMatrix

local instance heightOneLedgerPrimeFact (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

variable {m : ℕ}

/-- The integral subgroup is the height-one integral local factor. -/
theorem padicIntegralSpecialSubgroup_eq_heightOne (V : RationalQuadraticSpaceMatrix m)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    (padicIntegralSpecialSubgroup
        (V.pairingMatrix.map (algebraMap ℚ ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])) :
      Set (V.HeightOnePadicSpecialOrthogonalGroup v)) =
      (V.heightOnePadicSpecialOrthogonalIntegralSubgroup v : Set (V.HeightOnePadicSpecialOrthogonalGroup v)) := by
  ext g
  change _ ↔ g ∈ V.heightOnePadicSpecialOrthogonalIntegralSubgroup v
  rw [V.mem_heightOnePadicSpecialOrthogonalIntegralSubgroup_iff_padic]
  rfl

/-- The ledger masses are the integral local volumes. -/
theorem padicIntegral_measure_eq_heightOneIntegralVolume (V : RationalQuadraticSpaceMatrix m)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    padicCayleySpecialOrthogonalDifferentialMeasure (Rat.HeightOneSpectrum.primesEquiv v).1 m
        V.pairingMatrix V.form_det_ne_zero
        (padicIntegralSpecialSubgroup
          (V.pairingMatrix.map (algebraMap ℚ ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]))) =
      V.heightOnePadicSpecialOrthogonalIntegralVolume v := by
  rw [heightOnePadicSpecialOrthogonalIntegralVolume, padicInvariantDifferentialGroupMeasure]
  congr 1
  exact V.padicIntegralSpecialSubgroup_eq_heightOne v

variable {n : ℕ} (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)

section Ledger

local instance hoPadicMeasurableSpace (p : ℕ) [Fact p.Prime] : MeasurableSpace ℚ_[p] := borel _
local instance hoPadicBorelSpace (p : ℕ) [Fact p.Prime] : BorelSpace ℚ_[p] := ⟨rfl⟩

/-- Height-one ledger: at every height-one prime whose residue prime is outside the
explicit finite exceptional set, the integral local volumes satisfy
`vol_{V⊕⟨a⟩,v} / vol_{W,v} = |r| ν(ℤ_p) λ(X_a(ℤ_p))`. -/
theorem heightOneIntegralVolume_div_eq_ledger_of_notMem (hn : 1 ≤ n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hp : (Rat.HeightOneSpectrum.primesEquiv v).1 ∉ W.goodPlaceExceptionalPrimes a ha)
    (ν : Measure ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) [ν.IsAddHaarMeasure]
    (point : ℕ → Fin (n+1) → ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])
    (hpoint : ∀ i, (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] (point i) ≠ 0)
    (tH : ∀ i, Measure (((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]).anisotropicOrthogonal (point i)))
    [∀ i, (tH i).IsAddHaarMeasure]
    (hcover : {y | (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] y ≠ 0} ⊆
      ⋃ i, ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]).padicSquareBranchAtlasRegion
          (Rat.HeightOneSpectrum.primesEquiv v).1 point hpoint i) :
    (W.nonisotropicLastExtension a ha).heightOnePadicSpecialOrthogonalIntegralVolume v /
        W.heightOnePadicSpecialOrthogonalIntegralVolume v =
      ((‖W.lastOrbitGaugeRatio a ha ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]‖₊ : ℝ≥0∞) *
          ν (closedBall 0 1)) *
        ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm
            ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]).padicSquareBranchAtlasGlue
          (Rat.HeightOneSpectrum.primesEquiv v).1 point hpoint tH ν
          (Padic.unitHaar (Rat.HeightOneSpectrum.primesEquiv v).1 (Fin (n+1)))
          (algebraMap ℚ ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] a) {y | ‖y.1‖ ≤ 1} := by
  rw [← padicIntegral_measure_eq_heightOneIntegralVolume,
    ← padicIntegral_measure_eq_heightOneIntegralVolume]
  exact W.padicIntegral_measure_div_eq_ledger_of_notMem (Rat.HeightOneSpectrum.primesEquiv v).1
    a ha ν hn hp point hpoint tH hcover

end Ledger

end RationalQuadraticSpaceMatrix
