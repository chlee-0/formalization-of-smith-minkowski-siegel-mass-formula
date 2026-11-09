import SMSFormula.RationalCliffordSpinCandidateFiniteAdelicMixedPrincipalBlockCylinderTransition

/-!
# Coherent scaling of finite-adelic mixed principal-block cylinders

The direct mixed-block cylinders have an exact transition scalar: enlarging
the exceptional set from `S` to `T` introduces the product of the integral
local volumes on the newly exceptional normalized places.  This module
multiplies the cylinder on `S` by the inverse product of the integral local
volumes added beyond the fixed normalized empty-block baseline.

The resulting cylinders comap literally along every direct block embedding.
The local volumes and the unscaled transition scalar remain explicit.  No
measure or topology is transported through the restricted-family block
equivalence, and no global finite-adelic measure is constructed.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

local instance cliffordSpinCandidateCoherentBlockCylinderDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance cliffordSpinCandidateCoherentBlockCylinderPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance cliffordSpinCandidateCoherentBlockCylinderGroupMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    MeasurableSpace (V.HeightOnePadicCliffordSpinCandidateGroup v) :=
  borel _

local instance cliffordSpinCandidateCoherentBlockCylinderGroupBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace (V.HeightOnePadicCliffordSpinCandidateGroup v) :=
  ⟨rfl⟩

local instance cliffordSpinCandidateCoherentBlockCylinderGroupSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    SecondCountableTopology
      (V.HeightOnePadicCliffordSpinCandidateGroup v) :=
  inferInstance

local instance cliffordSpinCandidateCoherentBlockCylinderLocalFactorSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    SecondCountableTopology
      (V.FiniteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactor S v) :=
  TopologicalSpace.Subtype.secondCountableTopology _

local instance cliffordSpinCandidateCoherentBlockCylinderLocalFactorBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace
      (V.FiniteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactor S v) :=
  Subtype.borelSpace _

local instance cliffordSpinCandidateCoherentBlockCylinderMixedSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlock S) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance cliffordSpinCandidateCoherentBlockCylinderMixedBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlock S) :=
  Pi.borelSpace

/-! ## Inverse-volume block weights -/

/-- The places added by `S` beyond the fixed normalized empty-block
exceptional set. -/
private def coherentNewPlaces
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Finset (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  V.cliffordSpinCandidateAdmissibleExceptionalPlaces S \
    V.cliffordSpinCandidateAdmissibleExceptionalPlaces ∅

/-- The coherent weight is the product of inverse integral volumes only at
places added beyond the fixed normalized empty-block baseline. -/
def finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) : ℝ≥0∞ :=
  ∏ v ∈ coherentNewPlaces V S,
    (V.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume v)⁻¹

/-- Every transition volume is nonzero: its places are good for the smaller
normalized block. -/
theorem finiteAdelicCliffordSpinCandidateAdmissibleTransitionVolume_ne_zero
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.finiteAdelicCliffordSpinCandidateAdmissibleTransitionVolume S T ≠ 0 := by
  rw [V.finiteAdelicCliffordSpinCandidateAdmissibleTransitionVolume_eq_prod_sdiff]
  exact Finset.prod_ne_zero_iff.mpr fun v hv =>
    V.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume_ne_zero
      S ⟨v, (Finset.mem_sdiff.mp hv).2⟩

/-- Every transition volume is finite. -/
theorem finiteAdelicCliffordSpinCandidateAdmissibleTransitionVolume_ne_top
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.finiteAdelicCliffordSpinCandidateAdmissibleTransitionVolume S T ≠ ⊤ := by
  rw [V.finiteAdelicCliffordSpinCandidateAdmissibleTransitionVolume_eq_prod_sdiff]
  exact ENNReal.prod_ne_top fun v _ =>
    V.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume_ne_top v

/-- Every coherent block weight is nonzero. -/
theorem finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight_ne_zero
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight S ≠ 0 := by
  unfold finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight
  exact Finset.prod_ne_zero_iff.mpr fun v _ =>
    ENNReal.inv_ne_zero.mpr
      (V.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume_ne_top v)

/-- Every coherent block weight is finite. -/
theorem finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight_ne_top
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight S ≠ ⊤ := by
  unfold finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight
  exact ENNReal.prod_ne_top fun v hv =>
    ENNReal.inv_ne_top.mpr
      (V.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume_ne_zero
        ∅ ⟨v, (Finset.mem_sdiff.mp hv).2⟩)

/-- On a finite set of places good for `S`, inverse local volumes cancel the
corresponding local volumes. -/
private theorem prod_inv_integralVolume_mul_prod_integralVolume
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (U : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hgood : ∀ v ∈ U, v ∉ V.cliffordSpinCandidateAdmissibleExceptionalPlaces S) :
    (∏ v ∈ U,
        (V.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume v)⁻¹) *
      ∏ v ∈ U,
        V.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume v =
      1 := by
  classical
  induction U using Finset.induction_on with
  | empty => simp
  | @insert v U hv ih =>
      have hvGood := hgood v (Finset.mem_insert_self v U)
      have hUGood : ∀ w ∈ U,
          w ∉ V.cliffordSpinCandidateAdmissibleExceptionalPlaces S :=
        fun w hw => hgood w (Finset.mem_insert_of_mem hw)
      simp only [Finset.prod_insert hv]
      calc
        ((V.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume v)⁻¹ *
              ∏ w ∈ U,
                (V.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume w)⁻¹) *
            (V.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume v *
              ∏ w ∈ U,
                V.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume w) =
          ((V.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume v)⁻¹ *
              V.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume v) *
            ((∏ w ∈ U,
                (V.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume w)⁻¹) *
              ∏ w ∈ U,
                V.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume w) := by
                  ac_rfl
        _ = 1 := by
          rw [ENNReal.inv_mul_cancel
            (V.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume_ne_zero
              S ⟨v, hvGood⟩)
            (V.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume_ne_top v),
            ih hUGood, one_mul]

/-- Enlarging the raw exceptional set enlarges the baseline-relative
normalized exceptional set. -/
private theorem coherentNewPlaces_mono
    (V : RationalQuadraticSpaceMatrix n)
    {S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hST : S ⊆ T) :
    coherentNewPlaces V S ⊆ coherentNewPlaces V T := by
  intro v hv
  exact Finset.mem_sdiff.mpr
    ⟨V.cliffordSpinCandidateAdmissibleExceptionalPlaces_mono hST
        (Finset.mem_sdiff.mp hv).1,
      (Finset.mem_sdiff.mp hv).2⟩

/-- The places added between two normalized blocks are exactly the difference
of their two baseline-relative new-place sets. -/
private theorem coherentNewPlaces_sdiff
    (V : RationalQuadraticSpaceMatrix n)
    {S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)} :
    coherentNewPlaces V T \ coherentNewPlaces V S =
      V.cliffordSpinCandidateAdmissibleExceptionalPlaces T \
        V.cliffordSpinCandidateAdmissibleExceptionalPlaces S := by
  ext v
  have hbase :
      V.cliffordSpinCandidateAdmissibleExceptionalPlaces ∅ ⊆
        V.cliffordSpinCandidateAdmissibleExceptionalPlaces S :=
    V.cliffordSpinCandidateAdmissibleExceptionalPlaces_mono (Finset.empty_subset S)
  simp only [coherentNewPlaces, Finset.mem_sdiff]
  constructor
  · rintro ⟨⟨hvT, hv0⟩, hvS⟩
    exact ⟨hvT, fun hv => hvS ⟨hv, hv0⟩⟩
  · rintro ⟨hvT, hvS⟩
    exact ⟨⟨hvT, fun hv0 => hvS (hbase hv0)⟩, fun h => hvS h.1⟩

/-- Enlarging the exceptional set divides the coherent weight by exactly the
normalized transition volume. -/
theorem finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight_mul_transitionVolume
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    V.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight T *
        V.finiteAdelicCliffordSpinCandidateAdmissibleTransitionVolume S T =
      V.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight S := by
  classical
  let A := coherentNewPlaces V S
  let B := coherentNewPlaces V T
  have hAB : A ⊆ B := coherentNewPlaces_mono V hST
  have hdiff : B \ A =
      V.cliffordSpinCandidateAdmissibleExceptionalPlaces T \
        V.cliffordSpinCandidateAdmissibleExceptionalPlaces S :=
    coherentNewPlaces_sdiff V
  unfold finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight
  rw [V.finiteAdelicCliffordSpinCandidateAdmissibleTransitionVolume_eq_prod_sdiff,
    ← hdiff, ← Finset.prod_sdiff hAB]
  calc
    ((∏ v ∈ B \ A,
        (V.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume v)⁻¹) *
          ∏ v ∈ A,
            (V.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume v)⁻¹) *
        ∏ v ∈ B \ A,
          V.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume v =
      ((∏ v ∈ B \ A,
          (V.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume v)⁻¹) *
        ∏ v ∈ B \ A,
          V.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume v) *
          ∏ v ∈ A,
            (V.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume v)⁻¹ := by
              ac_rfl
    _ = ∏ v ∈ A,
          (V.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume v)⁻¹ := by
      rw [prod_inv_integralVolume_mul_prod_integralVolume V S (B \ A), one_mul]
      intro v hv
      rw [hdiff] at hv
      exact (Finset.mem_sdiff.mp hv).2

/-! ## Coherent scaled cylinders -/

/-- The direct mixed-block cylinder scaled by the inverse product of the
integral local volumes added beyond the fixed empty-block baseline. -/
def finiteAdelicCliffordSpinCandidateAdmissibleCoherentMixedPrincipalBlockCylinderMeasure
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure (V.FiniteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlock S) :=
  V.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight S •
    V.finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockCylinderMeasure S

/-- The coherent weight of the empty block is one. -/
@[simp]
theorem
    finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight_empty
    (V : RationalQuadraticSpaceMatrix n) :
    V.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight ∅ = 1 := by
  simp [finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight, coherentNewPlaces]

/-- Scaling does not alter the normalized empty-block cylinder.  Its mass is
the product of the fixed bad-place Haar masses, which is not asserted to be
one. -/
@[simp]
theorem
    finiteAdelicCliffordSpinCandidateAdmissibleCoherentMixedPrincipalBlockCylinderMeasure_empty
    (V : RationalQuadraticSpaceMatrix n) :
    V.finiteAdelicCliffordSpinCandidateAdmissibleCoherentMixedPrincipalBlockCylinderMeasure
        ∅ =
      V.finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockCylinderMeasure ∅ := by
  simp [finiteAdelicCliffordSpinCandidateAdmissibleCoherentMixedPrincipalBlockCylinderMeasure]

/-- The scaled direct block cylinders comap exactly along block embeddings. -/
theorem
    finiteAdelicCliffordSpinCandidateAdmissibleCoherentMixedPrincipalBlockCylinderMeasure_comap
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    (V.finiteAdelicCliffordSpinCandidateAdmissibleCoherentMixedPrincipalBlockCylinderMeasure
        T).comap
        (V.finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockTransitionEmbeddingHom
          S T hST) =
      V.finiteAdelicCliffordSpinCandidateAdmissibleCoherentMixedPrincipalBlockCylinderMeasure
        S := by
  unfold
    finiteAdelicCliffordSpinCandidateAdmissibleCoherentMixedPrincipalBlockCylinderMeasure
  rw [Measure.comap_smul]
  rw [
    V.finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockCylinderMeasure_comap_transition
      S T hST,
    smul_smul,
    V.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight_mul_transitionVolume S T hST]

end RationalQuadraticSpaceMatrix
