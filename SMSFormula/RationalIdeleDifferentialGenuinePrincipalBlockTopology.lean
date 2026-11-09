import SMSFormula.RationalIdeleDifferentialExceptionalTailTransition
import SMSFormula.RationalCliffordGeneralSpinFiniteAdelicLocalEvaluation

/-!
# Fixed-block topology for differential rational finite ideles

For a finite exceptional set `S`, assemble the unrestricted coordinates in
`S` and the integral-unit coordinates outside `S` into a unit of the
rational finite-adele ring.  Both the value and inverse are assembled through
the principal restricted product attached to the complement of `S`; this
makes the fixed-block inverse continuous without asserting any global product
topology for finite ideles.

The resulting source/genuine-block equivalence is a homeomorphism and keeps
every local component unchanged.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open scoped RestrictedProduct

namespace RationalQuadraticSpaceMatrix

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 2400000

local instance rationalIdeleGenuineBlockDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance rationalIdeleGenuineBlockPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance rationalIdeleGenuineBlockLocalMeasurableSpace
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    MeasurableSpace ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ :=
  borel _

local instance rationalIdeleGenuineBlockLocalBorelSpace
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ :=
  ⟨rfl⟩

local instance rationalIdeleGenuineBlockFiniteMeasurableSpace :
    MeasurableSpace RationalFiniteAdeleˣ :=
  borel _

local instance rationalIdeleGenuineBlockFiniteBorelSpace :
    BorelSpace RationalFiniteAdeleˣ :=
  ⟨rfl⟩

/-! ## Local family and genuine block -/

/-- The local unit selected by an exceptional/tail source point. -/
def rationalIdeleDifferentialExceptionalTailLocalUnit
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (z : RationalIdeleDifferentialExceptionalProduct S ×
      RationalIdeleDifferentialIntegralTail S)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ :=
  if hv : v ∈ S then z.1 ⟨v, hv⟩ else (z.2 ⟨v, hv⟩).1

@[simp]
theorem rationalIdeleDifferentialExceptionalTailLocalUnit_of_mem
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (z : RationalIdeleDifferentialExceptionalProduct S ×
      RationalIdeleDifferentialIntegralTail S)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) (hv : v ∈ S) :
    rationalIdeleDifferentialExceptionalTailLocalUnit S z v = z.1 ⟨v, hv⟩ := by
  simp [rationalIdeleDifferentialExceptionalTailLocalUnit, hv]

@[simp]
theorem rationalIdeleDifferentialExceptionalTailLocalUnit_of_notMem
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (z : RationalIdeleDifferentialExceptionalProduct S ×
      RationalIdeleDifferentialIntegralTail S)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) (hv : v ∉ S) :
    rationalIdeleDifferentialExceptionalTailLocalUnit S z v =
      (z.2 ⟨v, hv⟩).1 := by
  simp [rationalIdeleDifferentialExceptionalTailLocalUnit, hv]

/-- A finite idele lies in the `S` principal block when all local components
outside `S` are integral units. -/
def IsRationalIdeleDifferentialGenuinePrincipalBlock
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (a : RationalFiniteAdeleˣ) : Prop :=
  ∀ v, v ∉ S → finiteAdelicUnitHeightOneComponentHom v a ∈
    padicIntegralUnitsSubgroup (Rat.HeightOneSpectrum.primesEquiv v).1

/-- The literal fixed principal block inside genuine rational finite ideles. -/
abbrev RationalIdeleDifferentialGenuinePrincipalBlock
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :=
  {a : RationalFiniteAdeleˣ //
    IsRationalIdeleDifferentialGenuinePrincipalBlock S a}

/-! ## Principal restricted products for value and inverse -/

private abbrev RationalIdeleDifferentialPrincipalAdele
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :=
  Πʳ v : IsDedekindDomain.HeightOneSpectrum ℤ,
    [v.adicCompletion ℚ, v.adicCompletionIntegers ℚ]_[
      Filter.principal
        {v : IsDedekindDomain.HeightOneSpectrum ℤ | v ∉ S}]

private theorem cofinite_le_rationalIdeleDifferentialPrincipal_compl
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Filter.cofinite ≤ Filter.principal
      {v : IsDedekindDomain.HeightOneSpectrum ℤ | v ∉ S} := by
  rw [Filter.le_principal_iff]
  exact S.eventually_cofinite_notMem

private noncomputable def rationalIdeleDifferentialSourceValuePrincipalAdele
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (z : RationalIdeleDifferentialExceptionalProduct S ×
      RationalIdeleDifferentialIntegralTail S) :
    RationalIdeleDifferentialPrincipalAdele S :=
  ⟨fun v ↦ (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm
      (rationalIdeleDifferentialExceptionalTailLocalUnit S z v :
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]),
    by
      rw [Filter.eventually_principal]
      intro v hv
      apply (mem_adicCompletionIntegers_iff_padic v _).2
      have hmem := (z.2 ⟨v, hv⟩).2
      rw [mem_padicIntegralUnitsSubgroup_iff] at hmem
      change
        (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v)
            ((Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm
              (rationalIdeleDifferentialExceptionalTailLocalUnit S z v :
                ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])) ∈
          PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v).1
      rw [(Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).apply_symm_apply]
      rw [rationalIdeleDifferentialExceptionalTailLocalUnit_of_notMem
        S z v hv]
      exact hmem.1⟩

private noncomputable def rationalIdeleDifferentialSourceInversePrincipalAdele
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (z : RationalIdeleDifferentialExceptionalProduct S ×
      RationalIdeleDifferentialIntegralTail S) :
    RationalIdeleDifferentialPrincipalAdele S :=
  ⟨fun v ↦ (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm
      (((rationalIdeleDifferentialExceptionalTailLocalUnit S z v)⁻¹ :
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ) :
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]),
    by
      rw [Filter.eventually_principal]
      intro v hv
      apply (mem_adicCompletionIntegers_iff_padic v _).2
      have hmem := (z.2 ⟨v, hv⟩).2
      rw [mem_padicIntegralUnitsSubgroup_iff] at hmem
      change
        (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v)
            ((Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm
              (((rationalIdeleDifferentialExceptionalTailLocalUnit S z v)⁻¹ :
                ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ) :
                  ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])) ∈
          PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v).1
      rw [(Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).apply_symm_apply]
      rw [rationalIdeleDifferentialExceptionalTailLocalUnit_of_notMem
        S z v hv]
      exact hmem.2⟩

private noncomputable def rationalIdeleDifferentialSourceValueAdele
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (z : RationalIdeleDifferentialExceptionalProduct S ×
      RationalIdeleDifferentialIntegralTail S) : RationalFiniteAdele :=
  RestrictedProduct.inclusion
    (fun v : IsDedekindDomain.HeightOneSpectrum ℤ ↦ v.adicCompletion ℚ)
    (fun v : IsDedekindDomain.HeightOneSpectrum ℤ ↦
      v.adicCompletionIntegers ℚ)
    (cofinite_le_rationalIdeleDifferentialPrincipal_compl S)
    (rationalIdeleDifferentialSourceValuePrincipalAdele S z)

private noncomputable def rationalIdeleDifferentialSourceInverseAdele
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (z : RationalIdeleDifferentialExceptionalProduct S ×
      RationalIdeleDifferentialIntegralTail S) : RationalFiniteAdele :=
  RestrictedProduct.inclusion
    (fun v : IsDedekindDomain.HeightOneSpectrum ℤ ↦ v.adicCompletion ℚ)
    (fun v : IsDedekindDomain.HeightOneSpectrum ℤ ↦
      v.adicCompletionIntegers ℚ)
    (cofinite_le_rationalIdeleDifferentialPrincipal_compl S)
    (rationalIdeleDifferentialSourceInversePrincipalAdele S z)

/-! ## Assembly and component formulas -/

/-- Assemble a direct exceptional/tail point into a genuine finite idele. -/
noncomputable def rationalIdeleDifferentialExceptionalTailToFiniteIdele
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (z : RationalIdeleDifferentialExceptionalProduct S ×
      RationalIdeleDifferentialIntegralTail S) : RationalFiniteAdeleˣ := by
  refine ⟨rationalIdeleDifferentialSourceValueAdele S z,
    rationalIdeleDifferentialSourceInverseAdele S z, ?_, ?_⟩
  · ext v
    simp only [rationalIdeleDifferentialSourceValueAdele,
      rationalIdeleDifferentialSourceInverseAdele,
      rationalIdeleDifferentialSourceValuePrincipalAdele,
      rationalIdeleDifferentialSourceInversePrincipalAdele]
    change
      (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm
          (rationalIdeleDifferentialExceptionalTailLocalUnit S z v :
            ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) *
        (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm
          (((rationalIdeleDifferentialExceptionalTailLocalUnit S z v)⁻¹ :
            ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ) :
              ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) = 1
    rw [← map_mul]
    simp
  · ext v
    simp only [rationalIdeleDifferentialSourceValueAdele,
      rationalIdeleDifferentialSourceInverseAdele,
      rationalIdeleDifferentialSourceValuePrincipalAdele,
      rationalIdeleDifferentialSourceInversePrincipalAdele]
    change
      (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm
          (((rationalIdeleDifferentialExceptionalTailLocalUnit S z v)⁻¹ :
            ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ) :
              ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) *
        (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm
          (rationalIdeleDifferentialExceptionalTailLocalUnit S z v :
            ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) = 1
    rw [← map_mul]
    simp

@[simp]
theorem finiteAdelicUnitHeightOneComponent_exceptionalTailToFiniteIdele
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (z : RationalIdeleDifferentialExceptionalProduct S ×
      RationalIdeleDifferentialIntegralTail S)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    finiteAdelicUnitHeightOneComponentHom v
        (rationalIdeleDifferentialExceptionalTailToFiniteIdele S z) =
      rationalIdeleDifferentialExceptionalTailLocalUnit S z v := by
  apply Units.ext
  exact (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).apply_symm_apply _

/-- Assembly lands in the genuine fixed principal block. -/
noncomputable def rationalIdeleDifferentialExceptionalTailToGenuinePrincipalBlock
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    (RationalIdeleDifferentialExceptionalProduct S ×
      RationalIdeleDifferentialIntegralTail S) →
      RationalIdeleDifferentialGenuinePrincipalBlock S :=
  fun z ↦ ⟨rationalIdeleDifferentialExceptionalTailToFiniteIdele S z, by
    intro v hv
    rw [finiteAdelicUnitHeightOneComponent_exceptionalTailToFiniteIdele]
    rw [rationalIdeleDifferentialExceptionalTailLocalUnit_of_notMem S z v hv]
    exact (z.2 ⟨v, hv⟩).2⟩

@[simp]
theorem exceptionalTailToGenuinePrincipalBlock_component
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (z : RationalIdeleDifferentialExceptionalProduct S ×
      RationalIdeleDifferentialIntegralTail S)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    finiteAdelicUnitHeightOneComponentHom v
        (rationalIdeleDifferentialExceptionalTailToGenuinePrincipalBlock S z).1 =
      rationalIdeleDifferentialExceptionalTailLocalUnit S z v :=
  finiteAdelicUnitHeightOneComponent_exceptionalTailToFiniteIdele S z v

/-! ## Extraction and algebraic equivalence -/

/-- Extract exceptional coordinates and the integral complement tail from a
genuine fixed-block finite idele. -/
def rationalIdeleDifferentialGenuinePrincipalBlockToExceptionalTail
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    RationalIdeleDifferentialGenuinePrincipalBlock S →
      RationalIdeleDifferentialExceptionalProduct S ×
        RationalIdeleDifferentialIntegralTail S :=
  fun a ↦
    (fun v ↦ finiteAdelicUnitHeightOneComponentHom v.1 a.1,
    fun v ↦ ⟨finiteAdelicUnitHeightOneComponentHom v.1 a.1,
      a.2 v.1 v.2⟩)

/-- Direct coordinates and the genuine principal block are algebraically
equivalent. -/
noncomputable def rationalIdeleDifferentialExceptionalTailGenuinePrincipalBlockEquiv
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    (RationalIdeleDifferentialExceptionalProduct S ×
        RationalIdeleDifferentialIntegralTail S) ≃
      RationalIdeleDifferentialGenuinePrincipalBlock S where
  toFun := rationalIdeleDifferentialExceptionalTailToGenuinePrincipalBlock S
  invFun := rationalIdeleDifferentialGenuinePrincipalBlockToExceptionalTail S
  left_inv := by
    intro z
    apply Prod.ext
    · funext v
      rw [rationalIdeleDifferentialGenuinePrincipalBlockToExceptionalTail]
      simp [rationalIdeleDifferentialExceptionalTailLocalUnit, v.2]
    · funext v
      apply Subtype.ext
      rw [rationalIdeleDifferentialGenuinePrincipalBlockToExceptionalTail]
      simp [rationalIdeleDifferentialExceptionalTailLocalUnit, v.2]
  right_inv := by
    intro a
    apply Subtype.ext
    apply Units.ext
    ext v
    apply (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).injective
    have hcomponent :=
      exceptionalTailToGenuinePrincipalBlock_component S
        (rationalIdeleDifferentialGenuinePrincipalBlockToExceptionalTail S a) v
    have hlocal :
        rationalIdeleDifferentialExceptionalTailLocalUnit S
            (rationalIdeleDifferentialGenuinePrincipalBlockToExceptionalTail S a) v =
          finiteAdelicUnitHeightOneComponentHom v a.1 := by
      by_cases hv : v ∈ S
      · simp [rationalIdeleDifferentialExceptionalTailLocalUnit, hv,
          rationalIdeleDifferentialGenuinePrincipalBlockToExceptionalTail]
      · simp [rationalIdeleDifferentialExceptionalTailLocalUnit, hv,
          rationalIdeleDifferentialGenuinePrincipalBlockToExceptionalTail]
    change
      ((finiteAdelicUnitHeightOneComponentHom v
        (rationalIdeleDifferentialExceptionalTailToGenuinePrincipalBlock S
          (rationalIdeleDifferentialGenuinePrincipalBlockToExceptionalTail S a)).1 :
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ) :
            ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) =
        ((finiteAdelicUnitHeightOneComponentHom v a.1 :
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ) :
            ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])
    exact congrArg Units.val (hcomponent.trans hlocal)

/-! ## Continuity -/

private theorem continuous_rationalIdeleDifferentialExceptionalTailLocalUnit
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Continuous (fun z : RationalIdeleDifferentialExceptionalProduct S ×
      RationalIdeleDifferentialIntegralTail S ↦
        rationalIdeleDifferentialExceptionalTailLocalUnit S z v) := by
  by_cases hv : v ∈ S
  · simpa [rationalIdeleDifferentialExceptionalTailLocalUnit, hv] using
      (continuous_apply (⟨v, hv⟩ : {v // v ∈ S})).comp continuous_fst
  · simpa [rationalIdeleDifferentialExceptionalTailLocalUnit, hv] using
      continuous_subtype_val.comp
        ((continuous_apply (⟨v, hv⟩ : {v // v ∉ S})).comp continuous_snd)

private theorem continuous_rationalIdeleDifferentialSourceValuePrincipalAdele
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Continuous (rationalIdeleDifferentialSourceValuePrincipalAdele S) := by
  apply RestrictedProduct.continuous_rng_of_principal.mpr
  apply continuous_pi
  intro v
  exact (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm.continuous.comp
    (Units.continuous_val.comp
      (continuous_rationalIdeleDifferentialExceptionalTailLocalUnit S v))

private theorem continuous_rationalIdeleDifferentialSourceInversePrincipalAdele
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Continuous (rationalIdeleDifferentialSourceInversePrincipalAdele S) := by
  apply RestrictedProduct.continuous_rng_of_principal.mpr
  apply continuous_pi
  intro v
  exact (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm.continuous.comp
    (Units.continuous_val.comp
      (continuous_inv.comp
        (continuous_rationalIdeleDifferentialExceptionalTailLocalUnit S v)))

private theorem continuous_rationalIdeleDifferentialSourceValueAdele
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Continuous (rationalIdeleDifferentialSourceValueAdele S) :=
  (RestrictedProduct.continuous_inclusion
    (cofinite_le_rationalIdeleDifferentialPrincipal_compl S)).comp
      (continuous_rationalIdeleDifferentialSourceValuePrincipalAdele S)

private theorem continuous_rationalIdeleDifferentialSourceInverseAdele
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Continuous (rationalIdeleDifferentialSourceInverseAdele S) :=
  (RestrictedProduct.continuous_inclusion
    (cofinite_le_rationalIdeleDifferentialPrincipal_compl S)).comp
      (continuous_rationalIdeleDifferentialSourceInversePrincipalAdele S)

private theorem
    continuous_rationalIdeleDifferentialExceptionalTailToFiniteIdele
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Continuous (rationalIdeleDifferentialExceptionalTailToFiniteIdele S) := by
  rw [Units.continuous_iff]
  constructor
  · exact continuous_rationalIdeleDifferentialSourceValueAdele S
  · exact continuous_rationalIdeleDifferentialSourceInverseAdele S

private theorem continuous_finiteAdelicUnitHeightOneComponent
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Continuous (finiteAdelicUnitHeightOneComponentHom v) := by
  rw [Units.continuous_iff]
  constructor
  · exact (continuous_finiteAdelicCliffordGeneralSpinHeightOneAlgHom v).comp
      Units.continuous_val
  · exact (continuous_finiteAdelicCliffordGeneralSpinHeightOneAlgHom v).comp
      (Units.continuous_val.comp continuous_inv)

private theorem
    continuous_rationalIdeleDifferentialExceptionalTailToGenuinePrincipalBlock
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Continuous
      (rationalIdeleDifferentialExceptionalTailToGenuinePrincipalBlock S) := by
  apply Continuous.subtype_mk
  exact continuous_rationalIdeleDifferentialExceptionalTailToFiniteIdele S

private theorem
    continuous_rationalIdeleDifferentialGenuinePrincipalBlockToExceptionalTail
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Continuous
      (rationalIdeleDifferentialGenuinePrincipalBlockToExceptionalTail S) := by
  apply Continuous.prodMk
  · exact continuous_pi fun v ↦
      (continuous_finiteAdelicUnitHeightOneComponent v.1).comp
        continuous_subtype_val
  · apply continuous_pi
    intro v
    apply Continuous.subtype_mk
    exact (continuous_finiteAdelicUnitHeightOneComponent v.1).comp
      continuous_subtype_val

/-- The direct exceptional/tail source is homeomorphic to the literal fixed
principal block in genuine rational finite ideles. -/
noncomputable def
    rationalIdeleDifferentialExceptionalTailGenuinePrincipalBlockHomeomorph
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    (RationalIdeleDifferentialExceptionalProduct S ×
        RationalIdeleDifferentialIntegralTail S) ≃ₜ
      RationalIdeleDifferentialGenuinePrincipalBlock S where
  toEquiv := rationalIdeleDifferentialExceptionalTailGenuinePrincipalBlockEquiv S
  continuous_toFun :=
    continuous_rationalIdeleDifferentialExceptionalTailToGenuinePrincipalBlock S
  continuous_invFun :=
    continuous_rationalIdeleDifferentialGenuinePrincipalBlockToExceptionalTail S

end RationalQuadraticSpaceMatrix
