import SMSFormula.RationalSpecialOrthogonalFiniteAdelicMixedPrincipalBlockCylinderTransition

/-!
# Coherent scaling of finite-adelic mixed principal-block cylinders

The direct mixed-block cylinders have an exact transition scalar: enlarging
the exceptional set from `S` to `T` introduces the product of the integral
local volumes on `T \ S`.  This module multiplies the cylinder on `S` by the
inverse product of the integral local volumes on `S`.

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

local instance coherentBlockCylinderDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance coherentBlockCylinderPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance coherentBlockCylinderGroupMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    MeasurableSpace (V.HeightOnePadicSpecialOrthogonalGroup v) :=
  borel _

local instance coherentBlockCylinderGroupBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace (V.HeightOnePadicSpecialOrthogonalGroup v) :=
  ⟨rfl⟩

local instance coherentBlockCylinderGroupSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    SecondCountableTopology
      (V.HeightOnePadicSpecialOrthogonalGroup v) :=
  PositiveDefiniteIntegralLattice.padicCayleySpecialOrthogonalGroup_secondCountable
    V.pairingMatrix (Rat.HeightOneSpectrum.primesEquiv v).1

local instance coherentBlockCylinderLocalFactorSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    SecondCountableTopology
      (V.FiniteAdelicSpecialOrthogonalPrincipalBlockLocalFactor S v) :=
  TopologicalSpace.Subtype.secondCountableTopology _

local instance coherentBlockCylinderLocalFactorBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace
      (V.FiniteAdelicSpecialOrthogonalPrincipalBlockLocalFactor S v) :=
  Subtype.borelSpace _

local instance coherentBlockCylinderMixedSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (V.FiniteAdelicSpecialOrthogonalMixedPrincipalBlock S) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance coherentBlockCylinderMixedBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (V.FiniteAdelicSpecialOrthogonalMixedPrincipalBlock S) :=
  Pi.borelSpace

/-! ## Inverse-volume block weights -/

/-- The literal inverse-volume weight attached to a finite exceptional set. -/
def finiteAdelicSpecialOrthogonalBlockWeight
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) : ℝ≥0∞ :=
  ∏ v ∈ S, (V.heightOnePadicSpecialOrthogonalIntegralVolume v)⁻¹

/-- The block weight is the inverse of the product of the literal local
integral volumes. -/
theorem finiteAdelicSpecialOrthogonalBlockWeight_eq_inv_prod
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.finiteAdelicSpecialOrthogonalBlockWeight S =
      (∏ v ∈ S,
        V.heightOnePadicSpecialOrthogonalIntegralVolume v)⁻¹ := by
  classical
  unfold finiteAdelicSpecialOrthogonalBlockWeight
  induction S using Finset.induction_on with
  | empty =>
      simp
  | @insert v S hv ih =>
      simp only [Finset.prod_insert hv]
      rw [
        ENNReal.mul_inv
          (Or.inl
            (V.heightOnePadicSpecialOrthogonalIntegralVolume_ne_zero v))
          (Or.inl
            (V.heightOnePadicSpecialOrthogonalIntegralVolume_ne_top v)),
        ih]

/-- Every inverse-volume block weight is nonzero. -/
theorem finiteAdelicSpecialOrthogonalBlockWeight_ne_zero
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.finiteAdelicSpecialOrthogonalBlockWeight S ≠ 0 := by
  unfold finiteAdelicSpecialOrthogonalBlockWeight
  exact Finset.prod_ne_zero_iff.mpr fun v _hv =>
    ENNReal.inv_ne_zero.mpr
      (V.heightOnePadicSpecialOrthogonalIntegralVolume_ne_top v)

/-- Every inverse-volume block weight is finite. -/
theorem finiteAdelicSpecialOrthogonalBlockWeight_ne_top
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.finiteAdelicSpecialOrthogonalBlockWeight S ≠ ⊤ := by
  unfold finiteAdelicSpecialOrthogonalBlockWeight
  exact ENNReal.prod_ne_top fun v _hv =>
    ENNReal.inv_ne_top.mpr
      (V.heightOnePadicSpecialOrthogonalIntegralVolume_ne_zero v)

/-- The finite product of local integral volumes on a transition set is
nonzero. -/
theorem finiteAdelicSpecialOrthogonalTransitionVolume_ne_zero
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.finiteAdelicSpecialOrthogonalTransitionVolume S T ≠ 0 := by
  rw [V.finiteAdelicSpecialOrthogonalTransitionVolume_eq_prod_sdiff]
  exact Finset.prod_ne_zero_iff.mpr fun v _hv =>
    V.heightOnePadicSpecialOrthogonalIntegralVolume_ne_zero v

/-- The finite product of local integral volumes on a transition set is
finite. -/
theorem finiteAdelicSpecialOrthogonalTransitionVolume_ne_top
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.finiteAdelicSpecialOrthogonalTransitionVolume S T ≠ ⊤ := by
  rw [V.finiteAdelicSpecialOrthogonalTransitionVolume_eq_prod_sdiff]
  exact ENNReal.prod_ne_top fun v _hv =>
    V.heightOnePadicSpecialOrthogonalIntegralVolume_ne_top v

/-- On every finite place set, the product of the inverse local integral
volumes cancels the product of the local integral volumes. -/
private theorem prod_inv_integralVolume_mul_prod_integralVolume
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    (∏ v ∈ S,
        (V.heightOnePadicSpecialOrthogonalIntegralVolume v)⁻¹) *
      ∏ v ∈ S,
        V.heightOnePadicSpecialOrthogonalIntegralVolume v =
      1 := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp
  | @insert v S hv ih =>
      simp only [Finset.prod_insert hv]
      calc
        ((V.heightOnePadicSpecialOrthogonalIntegralVolume v)⁻¹ *
              ∏ w ∈ S,
                (V.heightOnePadicSpecialOrthogonalIntegralVolume w)⁻¹) *
            (V.heightOnePadicSpecialOrthogonalIntegralVolume v *
              ∏ w ∈ S,
                V.heightOnePadicSpecialOrthogonalIntegralVolume w) =
          ((V.heightOnePadicSpecialOrthogonalIntegralVolume v)⁻¹ *
              V.heightOnePadicSpecialOrthogonalIntegralVolume v) *
            ((∏ w ∈ S,
                (V.heightOnePadicSpecialOrthogonalIntegralVolume w)⁻¹) *
              ∏ w ∈ S,
                V.heightOnePadicSpecialOrthogonalIntegralVolume w) := by
                  ac_rfl
        _ = 1 := by
          rw [
            ENNReal.inv_mul_cancel
              (V.heightOnePadicSpecialOrthogonalIntegralVolume_ne_zero v)
              (V.heightOnePadicSpecialOrthogonalIntegralVolume_ne_top v),
            ih,
            one_mul]

/-- Enlarging the exceptional set divides the block weight by exactly the
literal transition volume. -/
theorem finiteAdelicSpecialOrthogonalBlockWeight_mul_transitionVolume
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    V.finiteAdelicSpecialOrthogonalBlockWeight T *
        V.finiteAdelicSpecialOrthogonalTransitionVolume S T =
      V.finiteAdelicSpecialOrthogonalBlockWeight S := by
  classical
  unfold finiteAdelicSpecialOrthogonalBlockWeight
  rw [
    V.finiteAdelicSpecialOrthogonalTransitionVolume_eq_prod_sdiff,
    ← Finset.prod_sdiff hST]
  calc
    ((∏ v ∈ T \ S,
        (V.heightOnePadicSpecialOrthogonalIntegralVolume v)⁻¹) *
          ∏ v ∈ S,
            (V.heightOnePadicSpecialOrthogonalIntegralVolume v)⁻¹) *
        ∏ v ∈ T \ S,
          V.heightOnePadicSpecialOrthogonalIntegralVolume v =
      ((∏ v ∈ T \ S,
          (V.heightOnePadicSpecialOrthogonalIntegralVolume v)⁻¹) *
        ∏ v ∈ T \ S,
          V.heightOnePadicSpecialOrthogonalIntegralVolume v) *
          ∏ v ∈ S,
            (V.heightOnePadicSpecialOrthogonalIntegralVolume v)⁻¹ := by
              ac_rfl
    _ = ∏ v ∈ S,
          (V.heightOnePadicSpecialOrthogonalIntegralVolume v)⁻¹ := by
      rw [prod_inv_integralVolume_mul_prod_integralVolume, one_mul]

/-! ## Coherent scaled cylinders -/

/-- The direct mixed-block cylinder scaled by the inverse product of the
integral local volumes at its exceptional places. -/
def finiteAdelicSpecialOrthogonalCoherentMixedPrincipalBlockCylinderMeasure
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure (V.FiniteAdelicSpecialOrthogonalMixedPrincipalBlock S) :=
  V.finiteAdelicSpecialOrthogonalBlockWeight S •
    V.finiteAdelicSpecialOrthogonalMixedPrincipalBlockCylinderMeasure S

/-- The coherent direct cylinder on the empty exceptional block has total
mass one. -/
@[simp]
theorem
    finiteAdelicSpecialOrthogonalCoherentMixedPrincipalBlockCylinderMeasure_empty_univ
    (V : RationalQuadraticSpaceMatrix n) :
    V.finiteAdelicSpecialOrthogonalCoherentMixedPrincipalBlockCylinderMeasure
        ∅ Set.univ = 1 := by
  rw [finiteAdelicSpecialOrthogonalCoherentMixedPrincipalBlockCylinderMeasure,
    Measure.smul_apply,
    V.finiteAdelicSpecialOrthogonalMixedPrincipalBlockCylinderMeasure_empty_univ]
  simp [finiteAdelicSpecialOrthogonalBlockWeight]

/-- The scaled direct block cylinders comap exactly along block embeddings. -/
theorem
    finiteAdelicSpecialOrthogonalCoherentMixedPrincipalBlockCylinderMeasure_comap
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    (V.finiteAdelicSpecialOrthogonalCoherentMixedPrincipalBlockCylinderMeasure
        T).comap
        (V.finiteAdelicSpecialOrthogonalMixedPrincipalBlockTransitionEmbeddingHom
          S T hST) =
      V.finiteAdelicSpecialOrthogonalCoherentMixedPrincipalBlockCylinderMeasure
        S := by
  unfold
    finiteAdelicSpecialOrthogonalCoherentMixedPrincipalBlockCylinderMeasure
  rw [Measure.comap_smul]
  rw [
    V.finiteAdelicSpecialOrthogonalMixedPrincipalBlockCylinderMeasure_comap_transition
      S T hST,
    smul_smul,
    V.finiteAdelicSpecialOrthogonalBlockWeight_mul_transitionVolume S T hST]

end RationalQuadraticSpaceMatrix
