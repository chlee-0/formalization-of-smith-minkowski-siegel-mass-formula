import SMSFormula.RationalCliffordGeneralSpinHorizontalRestrictedPrincipalBlockTransition

/-!
# Coherent horizontal GSpin restricted-family block cylinders

The unnormalized horizontal principal-block measure acquires the finite product
of newly unrestricted integral volumes when the exceptional set is enlarged.
This file fixes one normalization relative to the empty exceptional block: the
measure on `S` is multiplied by the inverse product of the local integral
volumes at the places added beyond that baseline.

These globally specified weights, rather than a transition-dependent
reciprocal, make the block measures comap literally along every inclusion.
All products remain finite.  No Euler product, genuine finite-adelic transport,
ambient Haar measure, or quotient disintegration is constructed here.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

local instance horizontalRestrictedCoherenceDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

/-! ## Baseline-relative inverse-volume weights -/

/-- Places made exceptional by `S` beyond the fixed bad-place baseline. -/
private def horizontalCoherentNewPlaces
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Finset (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  V.cliffordGeneralSpinHorizontalExceptionalPlaces S \
    V.cliffordGeneralSpinHorizontalExceptionalPlaces ∅

/-- The finite baseline-relative inverse-volume weight of the `S` cylinder. -/
def cliffordGeneralSpinHorizontalRestrictedBlockWeight
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) : ℝ≥0∞ :=
  ∏ v ∈ horizontalCoherentNewPlaces V S,
    (V.padicCliffordGeneralSpinHorizontalIntegralVolume v)⁻¹

/-- The transition volume as a double finite-set product. -/
theorem cliffordGeneralSpinHorizontalTransitionVolume_eq_prod_sdiff
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.cliffordGeneralSpinHorizontalTransitionVolume S T =
      ∏ v ∈ V.cliffordGeneralSpinHorizontalExceptionalPlaces T \
          V.cliffordGeneralSpinHorizontalExceptionalPlaces S,
        V.padicCliffordGeneralSpinHorizontalIntegralVolume v := by
  unfold cliffordGeneralSpinHorizontalTransitionVolume
  exact
    (Finset.prod_subtype
      (V.cliffordGeneralSpinHorizontalExceptionalPlaces T \
        V.cliffordGeneralSpinHorizontalExceptionalPlaces S)
      (fun _ ↦ Iff.rfl)
      (fun v ↦ V.padicCliffordGeneralSpinHorizontalIntegralVolume v)).symm

/-- Every globally specified block weight is nonzero. -/
theorem cliffordGeneralSpinHorizontalRestrictedBlockWeight_ne_zero
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.cliffordGeneralSpinHorizontalRestrictedBlockWeight S ≠ 0 := by
  unfold cliffordGeneralSpinHorizontalRestrictedBlockWeight
  exact Finset.prod_ne_zero_iff.mpr fun v _ ↦
    ENNReal.inv_ne_zero.mpr
      (V.padicCliffordGeneralSpinHorizontalIntegralVolume_ne_top v)

/-- Every globally specified block weight is finite. -/
theorem cliffordGeneralSpinHorizontalRestrictedBlockWeight_ne_top
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.cliffordGeneralSpinHorizontalRestrictedBlockWeight S ≠ ⊤ := by
  unfold cliffordGeneralSpinHorizontalRestrictedBlockWeight
  exact ENNReal.prod_ne_top fun v hv ↦
    ENNReal.inv_ne_top.mpr
      (V.padicCliffordGeneralSpinHorizontalIntegralVolume_ne_zero ∅
        ⟨v, by
          have hv' := (Finset.mem_sdiff.mp hv).2
          simpa [cliffordGeneralSpinHorizontalExceptionalPlaces] using hv'⟩)

/-- The empty exceptional block is the normalization baseline. -/
@[simp]
theorem cliffordGeneralSpinHorizontalRestrictedBlockWeight_empty
    (V : RationalQuadraticSpaceMatrix n) :
    V.cliffordGeneralSpinHorizontalRestrictedBlockWeight ∅ = 1 := by
  simp [cliffordGeneralSpinHorizontalRestrictedBlockWeight,
    horizontalCoherentNewPlaces]

private theorem horizontalCoherentNewPlaces_mono
    (V : RationalQuadraticSpaceMatrix n)
    {S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hST : S ⊆ T) :
    horizontalCoherentNewPlaces V S ⊆ horizontalCoherentNewPlaces V T := by
  intro v hv
  exact Finset.mem_sdiff.mpr
    ⟨V.cliffordGeneralSpinHorizontalExceptionalPlaces_mono hST
        (Finset.mem_sdiff.mp hv).1,
      (Finset.mem_sdiff.mp hv).2⟩

private theorem horizontalCoherentNewPlaces_sdiff
    (V : RationalQuadraticSpaceMatrix n)
    {S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)} :
    horizontalCoherentNewPlaces V T \ horizontalCoherentNewPlaces V S =
      V.cliffordGeneralSpinHorizontalExceptionalPlaces T \
        V.cliffordGeneralSpinHorizontalExceptionalPlaces S := by
  ext v
  have hbase :
      V.cliffordGeneralSpinHorizontalExceptionalPlaces ∅ ⊆
        V.cliffordGeneralSpinHorizontalExceptionalPlaces S :=
    V.cliffordGeneralSpinHorizontalExceptionalPlaces_mono
      (Finset.empty_subset S)
  simp only [horizontalCoherentNewPlaces, Finset.mem_sdiff]
  constructor
  · rintro ⟨⟨hvT, hv0⟩, hvS⟩
    exact ⟨hvT, fun hv ↦ hvS ⟨hv, hv0⟩⟩
  · rintro ⟨hvT, hvS⟩
    exact ⟨⟨hvT, fun hv0 ↦ hvS (hbase hv0)⟩, fun h ↦ hvS h.1⟩

private theorem horizontalProdInvVolume_mul_prodVolume
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (U : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hgood : ∀ v ∈ U,
      v ∉ V.cliffordGeneralSpinHorizontalExceptionalPlaces S) :
    (∏ v ∈ U,
        (V.padicCliffordGeneralSpinHorizontalIntegralVolume v)⁻¹) *
      ∏ v ∈ U,
        V.padicCliffordGeneralSpinHorizontalIntegralVolume v = 1 := by
  classical
  induction U using Finset.induction_on with
  | empty => simp
  | @insert v U hv ih =>
      have hvGood := hgood v (Finset.mem_insert_self v U)
      have hUGood : ∀ w ∈ U,
          w ∉ V.cliffordGeneralSpinHorizontalExceptionalPlaces S :=
        fun w hw ↦ hgood w (Finset.mem_insert_of_mem hw)
      simp only [Finset.prod_insert hv]
      calc
        ((V.padicCliffordGeneralSpinHorizontalIntegralVolume v)⁻¹ *
              ∏ w ∈ U,
                (V.padicCliffordGeneralSpinHorizontalIntegralVolume w)⁻¹) *
            (V.padicCliffordGeneralSpinHorizontalIntegralVolume v *
              ∏ w ∈ U,
                V.padicCliffordGeneralSpinHorizontalIntegralVolume w) =
          ((V.padicCliffordGeneralSpinHorizontalIntegralVolume v)⁻¹ *
              V.padicCliffordGeneralSpinHorizontalIntegralVolume v) *
            ((∏ w ∈ U,
                (V.padicCliffordGeneralSpinHorizontalIntegralVolume w)⁻¹) *
              ∏ w ∈ U,
                V.padicCliffordGeneralSpinHorizontalIntegralVolume w) := by
                  ac_rfl
        _ = 1 := by
          rw [ENNReal.inv_mul_cancel
            (V.padicCliffordGeneralSpinHorizontalIntegralVolume_ne_zero S
              ⟨v, hvGood⟩)
            (V.padicCliffordGeneralSpinHorizontalIntegralVolume_ne_top v),
            ih hUGood, one_mul]

/-- Enlarging the exceptional set divides the global weight by the exact
transition volume. -/
theorem cliffordGeneralSpinHorizontalRestrictedBlockWeight_mul_transitionVolume
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    V.cliffordGeneralSpinHorizontalRestrictedBlockWeight T *
        V.cliffordGeneralSpinHorizontalTransitionVolume S T =
      V.cliffordGeneralSpinHorizontalRestrictedBlockWeight S := by
  classical
  let A := horizontalCoherentNewPlaces V S
  let B := horizontalCoherentNewPlaces V T
  have hAB : A ⊆ B := horizontalCoherentNewPlaces_mono V hST
  have hdiff : B \ A =
      V.cliffordGeneralSpinHorizontalExceptionalPlaces T \
        V.cliffordGeneralSpinHorizontalExceptionalPlaces S :=
    horizontalCoherentNewPlaces_sdiff V
  unfold cliffordGeneralSpinHorizontalRestrictedBlockWeight
  rw [V.cliffordGeneralSpinHorizontalTransitionVolume_eq_prod_sdiff,
    ← hdiff, ← Finset.prod_sdiff hAB]
  calc
    ((∏ v ∈ B \ A,
        (V.padicCliffordGeneralSpinHorizontalIntegralVolume v)⁻¹) *
          ∏ v ∈ A,
            (V.padicCliffordGeneralSpinHorizontalIntegralVolume v)⁻¹) *
        ∏ v ∈ B \ A,
          V.padicCliffordGeneralSpinHorizontalIntegralVolume v =
      ((∏ v ∈ B \ A,
          (V.padicCliffordGeneralSpinHorizontalIntegralVolume v)⁻¹) *
        ∏ v ∈ B \ A,
          V.padicCliffordGeneralSpinHorizontalIntegralVolume v) *
          ∏ v ∈ A,
            (V.padicCliffordGeneralSpinHorizontalIntegralVolume v)⁻¹ := by
              ac_rfl
    _ = ∏ v ∈ A,
          (V.padicCliffordGeneralSpinHorizontalIntegralVolume v)⁻¹ := by
      rw [horizontalProdInvVolume_mul_prodVolume V S (B \ A), one_mul]
      intro v hv
      rw [hdiff] at hv
      exact (Finset.mem_sdiff.mp hv).2

/-! ## Coherent restricted-family cylinders -/

/-- The horizontal restricted-family block cylinder with its single global
baseline-relative normalization. -/
def cliffordGeneralSpinHorizontalCoherentRestrictedPrincipalBlockMeasure
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure (V.CliffordGeneralSpinHorizontalRestrictedPrincipalBlock S) :=
  V.cliffordGeneralSpinHorizontalRestrictedBlockWeight S •
    V.cliffordGeneralSpinHorizontalRestrictedPrincipalBlockMeasure S

/-- The globally normalized block cylinders comap literally along every
principal-block transition. -/
theorem cliffordGeneralSpinHorizontalCoherentRestrictedPrincipalBlockMeasure_comap
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    (V.cliffordGeneralSpinHorizontalCoherentRestrictedPrincipalBlockMeasure T).comap
        (V.cliffordGeneralSpinHorizontalRestrictedPrincipalBlockTransition S T hST) =
      V.cliffordGeneralSpinHorizontalCoherentRestrictedPrincipalBlockMeasure S := by
  unfold cliffordGeneralSpinHorizontalCoherentRestrictedPrincipalBlockMeasure
  rw [Measure.comap_smul,
    V.cliffordGeneralSpinHorizontalRestrictedPrincipalBlockMeasure_comap_transition
      S T hST,
    smul_smul,
    V.cliffordGeneralSpinHorizontalRestrictedBlockWeight_mul_transitionVolume S T hST]

end RationalQuadraticSpaceMatrix
