import SMSFormula.AdelicSpinDiagonalBlockMeasureAssembly
import SMSFormula.AdelicGaussianDiagonalBlockBootstrap

/-!
# The diagonal product formula from local block measure data

`DiagonalSpinProductFormula` (τ(Spin⟨a,b,c,abc⟩) = τ(Spin⟨a,b,c⟩)²) is reduced to the local block
measure data `DiagonalBlockLocalMeasureData` of the ternary diagonal space: the p-adic local
identities with constants `c_v`, the matching of integral loci off a finite set, the real
total-mass relation with constant `c_∞`, and the product formula `c_∞ ∏ c_v = 1`.  The Tamagawa
numbers of arbitrary certified data are the canonical raw quotient volumes (raw
normalization uniqueness); the block lattice is the nonisotropic last extension of the ternary
lattice (same Gram matrix).
-/

noncomputable section

open MeasureTheory PositiveDefiniteIntegralLattice Matrix
open scoped ENNReal NNReal

namespace RationalQuadraticSpaceMatrix

set_option backward.isDefEq.respectTransparency false in
/-- The Spin Tamagawa number of certified data is the canonical raw quotient volume at its scale. -/
theorem CliffordSpinCandidateRawOnoTamagawaData.spinTamagawaNumberENNReal_eq_rawQuotientVolume {n : ℕ}
    {V : RationalQuadraticSpaceMatrix n} (D : V.CliffordSpinCandidateRawOnoTamagawaData) :
    D.spinTamagawaNumberENNReal =
      (V.fullAdelicCliffordSpinCandidateRawDifferentialMeasurableWeilData D.spinFiniteScale).quotientVolumeENNReal := by
  rw [fullAdelicCliffordSpinCandidateRawDifferentialQuotientVolume_eq_domainMass]
  unfold CliffordSpinCandidateRawOnoTamagawaData.spinTamagawaNumberENNReal
  rw [CliffordSpinCandidateMeasurableWeilMeasureData.quotientVolumeENNReal_eq,
    D.spinData.quotientMeasure_eq_fundamentalDomain,
    leftQuotientFundamentalDomainMeasure_univ_map_mspace
      (Gamma := V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup)
      (μG := D.spinData.adelicMeasure)
      (F := V.fullAdelicCliffordSpinCandidateMeasurableFundamentalDomain) rfl,
    D.spinRaw.adelicMeasure_eq]

section Local

local instance diagonalLocalDataPrimeFact (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

variable (T : RationalQuadraticSpaceMatrix 3) {f : Fin 3 → ℚ} (hT : T.pairingMatrix = diagonal f)
  (hδ : f 0 * f 1 * f 2 ≠ 0)

/-- The local block measure data of a diagonal ternary space: local identities at every finite place
with constants `c_v` (one off a finite set `S₀`), matching integral loci off `S₀`, the real
total-mass relation with constant `c_∞`, and the product formula `c_∞ ∏_{v ∈ S₀} c_v = 1`. -/
def DiagonalBlockLocalMeasureData : Prop :=
  ∃ (S₀ : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) (c : IsDedekindDomain.HeightOneSpectrum ℤ → ℝ≥0)
    (cInf : ℝ≥0), (∀ v, c v ≠ 0) ∧ (∀ v ∉ S₀, c v = 1) ∧
    (∀ v, Measure.map (T.diagonalBlockLocalEquiv hT hδ v)
        ((T.heightOnePadicCliffordSpinCandidateChartGluedGroupMeasure v).prod
          (T.heightOnePadicCliffordSpinCandidateChartGluedGroupMeasure v)) =
      (c v : ℝ≥0∞) •
        (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).heightOnePadicCliffordSpinCandidateChartGluedGroupMeasure v) ∧
    (∀ v ∉ S₀, ∀ a b : T.HeightOnePadicCliffordSpinCandidateGroup v,
      (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).HeightOnePadicCliffordSpinCandidateIsIntegral v
          (T.diagonalBlockLocalEquiv hT hδ v (a, b)) ↔
        T.HeightOnePadicCliffordSpinCandidateIsIntegral v a ∧ T.HeightOnePadicCliffordSpinCandidateIsIntegral v b) ∧
    (T.realCliffordSpinCandidateChartGluedMeasure Set.univ * T.realCliffordSpinCandidateChartGluedMeasure Set.univ =
      (cInf : ℝ≥0∞) * (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).realCliffordSpinCandidateChartGluedMeasure Set.univ) ∧
    (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).realCliffordSpinCandidateChartGluedMeasure Set.univ ≠ 0 ∧
    (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).realCliffordSpinCandidateChartGluedMeasure Set.univ ≠ ⊤ ∧
    (cInf : ℝ≥0∞) * ∏ v ∈ S₀, (c v : ℝ≥0∞) = 1

/-- The block product formula from the local block measure data, for arbitrary certified data. -/
theorem spinTamagawaNumberENNReal_block_eq_mul_of_local {V : RationalQuadraticSpaceMatrix 4}
    (hV : V = T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ) (hloc : T.DiagonalBlockLocalMeasureData hT hδ)
    (DT : T.CliffordSpinCandidateRawOnoTamagawaData) (DV : V.CliffordSpinCandidateRawOnoTamagawaData) :
    DV.spinTamagawaNumberENNReal = DT.spinTamagawaNumberENNReal * DT.spinTamagawaNumberENNReal := by
  subst hV
  obtain ⟨S₀, c, cInf, hc0, hc1, HL, HK, HR, hR0, hRtop, Hprod⟩ := hloc
  rw [DV.spinTamagawaNumberENNReal_eq_rawQuotientVolume, DT.spinTamagawaNumberENNReal_eq_rawQuotientVolume]
  exact T.diagonalBlock_quotientVolume_eq_mul_of_map hT hδ _ _
    (T.map_diagonalBlock_rawDifferentialGroupMeasure_of_local hT hδ DT.spinRaw.volumeProductCertificate
      DV.spinRaw.volumeProductCertificate S₀ c cInf hc0 hc1 HL HK HR hR0 hRtop Hprod)

end Local

theorem eq_of_pairingMatrix_eq {n : ℕ} {V W : RationalQuadraticSpaceMatrix n} (h : V.pairingMatrix = W.pairingMatrix) : V = W := by
  cases V
  cases W
  simp only at h
  subst h
  rfl

end RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice

open RationalQuadraticSpaceMatrix

theorem diagLattice3_pairingMatrix {a b c : ℤ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (diagLattice3 ha hb hc).rationalQuadraticSpaceMatrix.pairingMatrix = diagonal ![(a : ℚ), b, c] := by
  rw [rationalQuadraticSpaceMatrix_pairingMatrix, rationalFormMatrix, diagLattice3, ofPosDiagonal,
    diagonal_map (map_zero _)]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem diagLattice3_blockConstant_ne_zero {a b c : ℤ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (![(a : ℚ), b, c] 0) * (![(a : ℚ), b, c] 1) * (![(a : ℚ), b, c] 2) ≠ 0 := by
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  have : (0 : ℚ) < a := by exact_mod_cast ha
  have : (0 : ℚ) < b := by exact_mod_cast hb
  have : (0 : ℚ) < c := by exact_mod_cast hc
  positivity

theorem blockLattice_eq_nonisotropicLastExtension {a b c : ℤ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (blockLattice ha hb hc).rationalQuadraticSpaceMatrix =
      (diagLattice3 ha hb hc).rationalQuadraticSpaceMatrix.nonisotropicLastExtension
        ((![(a : ℚ), b, c] 0) * (![(a : ℚ), b, c] 1) * (![(a : ℚ), b, c] 2))
        (diagLattice3_blockConstant_ne_zero ha hb hc) := by
  apply RationalQuadraticSpaceMatrix.eq_of_pairingMatrix_eq
  rw [(diagLattice3 ha hb hc).rationalQuadraticSpaceMatrix.nonisotropicLastExtension_pairingMatrix_eq_diagonal
    (diagLattice3_pairingMatrix ha hb hc), rationalQuadraticSpaceMatrix_pairingMatrix, rationalFormMatrix, blockLattice,
    ofPosDiagonal, diagonal_map (map_zero _)]
  congr 1
  funext i
  fin_cases i <;> simp [diagonalBlockWeights]

/-- The diagonal product formula from the local block measure data of every positive diagonal
ternary lattice. -/
theorem diagonalSpinProductFormula_of_local
    (hloc : ∀ (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c),
      (diagLattice3 ha hb hc).rationalQuadraticSpaceMatrix.DiagonalBlockLocalMeasureData
        (diagLattice3_pairingMatrix ha hb hc) (diagLattice3_blockConstant_ne_zero ha hb hc)) :
    DiagonalSpinProductFormula := by
  intro a b c ha hb hc instT PT hPT hT instU PU hPU hU
  exact (diagLattice3 ha hb hc).rationalQuadraticSpaceMatrix.spinTamagawaNumberENNReal_block_eq_mul_of_local
    (diagLattice3_pairingMatrix ha hb hc) (diagLattice3_blockConstant_ne_zero ha hb hc)
    (blockLattice_eq_nonisotropicLastExtension ha hb hc) (hloc a b c ha hb hc) _ _

end PositiveDefiniteIntegralLattice
