import SMSFormula.AdelicGaussianRankFourSpinFromRankThree
import SMSFormula.RationalLatticeQuaternionComplementSimilarity
import SMSFormula.RationalQuadraticIsometrySpinCandidateCrossWitnessCoefficient
import SMSFormula.RationalCliffordSpinCandidateRawQuotientVolumePositive
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# The quaternion bootstrap for the rank-three Spin base case

The two structural inputs are stated as explicit propositions (not axioms; nothing here assumes them):

* `TernarySpinSimilarityInvariance`: `τ(Spin_{kT}) = τ(Spin_T)` for integral scalings of ternary lattices;
* `QuaternionSpinProductFormula`: for the quaternion lattice `U` of a diagonalization `T ⊗ ℚ ≅ ⟨a, b, c⟩`,
  `τ(Spin_U) = τ(Spin_T)²` (the measure-level form of `Spin(U) ≅ SL₁(D) × SL₁(D)`).

`rankThreeSpinTamagawaOne_of_similarity_of_productFormula`: together they give `RankThreeSpinTamagawaOne`.
Proof: every anisotropic complement of `U` is isometric to some `k T` (`exists_quaternionLattice_complement_isometry_smul`),
so by isometry invariance and similarity its Spin volume is `t = τ(Spin_T)`; the rank-four common-complement theorem
gives `τ(Spin_U) = t`; with `τ(Spin_U) = t²` and `0 < t < ∞` this forces `t = 1`.
Hence, with `rankFourSpinTamagawaOne_of_rankThree`, the headline mass formula in every rank `≥ 3` follows from the two
structural inputs.
-/

noncomputable section

open scoped ENNReal
open QuadraticMap

namespace PositiveDefiniteIntegralLattice

/-- Similarity invariance of the Spin Tamagawa number for integral scalings of ternary lattices. -/
def TernarySpinSimilarityInvariance : Prop :=
  ∀ (T : PositiveDefiniteIntegralLattice 3) (k : ℕ) (hk : 0 < k)
    (instT : Fintype T.ConcreteProperRationalDoubleCosetSet) (PT : ℝ) (hPT : 0 < PT)
    (hT : massLocalInverseProductTendsTo T PT)
    (instk : Fintype (T.smulLattice k hk).ConcreteProperRationalDoubleCosetSet) (Pk : ℝ) (hPk : 0 < Pk)
    (hk' : massLocalInverseProductTendsTo (T.smulLattice k hk) Pk),
    (cliffordSpinCandidateRawOnoTamagawaDataOfLattice (T.smulLattice k hk) le_rfl instk hPk hk').spinTamagawaNumberENNReal
      = (cliffordSpinCandidateRawOnoTamagawaDataOfLattice T le_rfl instT hPT hT).spinTamagawaNumberENNReal

/-- The quaternion product formula `τ(Spin_U) = τ(Spin_T)²` for the quaternion lattice of a diagonalization. -/
def QuaternionSpinProductFormula : Prop :=
  ∀ (T : PositiveDefiniteIntegralLattice 3) {a b c : ℚ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c),
    T.rationalQuadraticSpaceMatrix.quadraticForm.IsometryEquiv (weightedSumSquares ℚ ![a, b, c]) →
    ∀ (instT : Fintype T.ConcreteProperRationalDoubleCosetSet) (PT : ℝ) (hPT : 0 < PT)
      (hT : massLocalInverseProductTendsTo T PT)
      (instU : Fintype (quaternionLattice ha hb hc).ConcreteProperRationalDoubleCosetSet) (PU : ℝ) (hPU : 0 < PU)
      (hU : massLocalInverseProductTendsTo (quaternionLattice ha hb hc) PU),
      (cliffordSpinCandidateRawOnoTamagawaDataOfLattice (quaternionLattice ha hb hc) (by norm_num) instU hPU
          hU).spinTamagawaNumberENNReal =
        (cliffordSpinCandidateRawOnoTamagawaDataOfLattice T le_rfl instT hPT hT).spinTamagawaNumberENNReal *
          (cliffordSpinCandidateRawOnoTamagawaDataOfLattice T le_rfl instT hPT hT).spinTamagawaNumberENNReal

/-! ## Similarity invariance follows from the product formula -/

/-- `k · ⟨a, b, c⟩ = ⟨ka, kb, kc⟩`. -/
theorem smul_weightedSumSquares_three (k a b c : ℚ) :
    k • weightedSumSquares ℚ ![a, b, c] = weightedSumSquares ℚ ![k * a, k * b, k * c] := by
  ext v
  simp only [QuadraticMap.smul_apply, weightedSumSquares_apply, Fin.sum_univ_three, smul_eq_mul,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

/-- The quaternion lattices of `⟨a, b, c⟩` and `⟨ka, kb, kc⟩` are rationally isometric. -/
theorem nonempty_quaternionLattice_smul_isometryEquiv {a b c : ℚ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    {k : ℚ} (hk : 0 < k) :
    Nonempty ((quaternionLattice (mul_pos hk ha) (mul_pos hk hb)
        (mul_pos hk hc)).rationalQuadraticSpaceMatrix.quadraticForm.IsometryEquiv
      (quaternionLattice ha hb hc).rationalQuadraticSpaceMatrix.quadraticForm) := by
  obtain ⟨e₁⟩ := nonempty_ofPosRatDiagonal_isometryEquiv _
    (quaternionWeights_pos (mul_pos hk ha) (mul_pos hk hb) (mul_pos hk hc))
  obtain ⟨e₂⟩ := nonempty_ofPosRatDiagonal_isometryEquiv _ (quaternionWeights_pos ha hb hc)
  have hw : (![1, k * a * (k * b), k * a * (k * c), k * a * (k * a) * (k * b) * (k * c)] : Fin 4 → ℚ) =
      fun i ↦ (![1, a * b, a * c, a * a * b * c] : Fin 4 → ℚ) i * (![1, k, k, k * k] : Fin 4 → ℚ) i ^ 2 := by
    funext i
    fin_cases i <;> simp <;> ring
  have hm : ∀ i, (![1, k, k, k * k] : Fin 4 → ℚ) i ≠ 0 := by
    intro i
    fin_cases i <;> simp [hk.ne']
  have e₃ := weightedSumSquaresSqScaleIsometry (![1, a * b, a * c, a * a * b * c] : Fin 4 → ℚ)
    ![1, k, k, k * k] hm
  rw [← hw] at e₃
  exact ⟨(e₁.trans e₃).trans e₂.symm⟩

/-- The product formula implies similarity invariance: `τ(Spin_{kT})² = τ(Spin_U) = τ(Spin_T)²`, since the
quaternion lattices of `T` and `kT` are isometric. -/
theorem ternarySpinSimilarityInvariance_of_productFormula (hprod : QuaternionSpinProductFormula) :
    TernarySpinSimilarityInvariance := by
  intro T k hk instT PT hPT hT instk Pk hPk hk'
  obtain ⟨w, hw, ⟨eT⟩⟩ := RationalQuadraticSpaceMatrix.exists_pos_weightedSumSquares_isometryEquiv
    T.rationalQuadraticSpaceMatrix.quadraticForm fun x hx ↦
      T.rationalQuadraticSpaceMatrix_nativeRationalQuadraticForm_pos hx
  have hw' : w = ![w 0, w 1, w 2] := by
    funext i
    fin_cases i <;> rfl
  rw [hw'] at eT
  have hkq : (0 : ℚ) < k := by exact_mod_cast hk
  -- the diagonalization of `kT`
  have ekT : (T.smulLattice k hk).rationalQuadraticSpaceMatrix.quadraticForm.IsometryEquiv
      (weightedSumSquares ℚ ![(k : ℚ) * w 0, (k : ℚ) * w 1, (k : ℚ) * w 2]) := by
    rw [smulLattice_quadraticForm, ← smul_weightedSumSquares_three]
    exact eT.smulForm (k : ℚ)
  set U := quaternionLattice (hw 0) (hw 1) (hw 2) with hUdef
  set U' := quaternionLattice (mul_pos hkq (hw 0)) (mul_pos hkq (hw 1)) (mul_pos hkq (hw 2)) with hU'def
  let instU : Fintype U.ConcreteProperRationalDoubleCosetSet := U.concreteProperRationalDoubleCosetSetFintype
  let instU' : Fintype U'.ConcreteProperRationalDoubleCosetSet := U'.concreteProperRationalDoubleCosetSetFintype
  obtain ⟨PU, hPU, hU⟩ := U.exists_pos_massLocalInverseProductTendsTo (by norm_num)
  obtain ⟨PU', hPU', hU'⟩ := U'.exists_pos_massLocalInverseProductTendsTo (by norm_num)
  have h1 := hprod T (hw 0) (hw 1) (hw 2) eT instT PT hPT hT instU PU hPU hU
  have h2 := hprod (T.smulLattice k hk) (mul_pos hkq (hw 0)) (mul_pos hkq (hw 1)) (mul_pos hkq (hw 2)) ekT
    instk Pk hPk hk' instU' PU' hPU' hU'
  obtain ⟨eU⟩ := nonempty_quaternionLattice_smul_isometryEquiv (hw 0) (hw 1) (hw 2) hkq
  have h3 := RationalQuadraticSpaceMatrix.spinTamagawaNumberENNReal_eq_of_rationalIsometry _ _ eU
    (by norm_num) (cliffordSpinCandidateRawOnoTamagawaDataOfLattice U' (by norm_num) instU' hPU' hU')
    (cliffordSpinCandidateRawOnoTamagawaDataOfLattice U (by norm_num) instU hPU hU)
  rw [h2, h1] at h3
  rw [← _root_.sq, ← _root_.sq, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast] at h3
  exact (ENNReal.rpow_left_injective (by norm_num : ((2 : ℕ) : ℝ) ≠ 0)) h3

end PositiveDefiniteIntegralLattice
