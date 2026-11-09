import SMSFormula.RationalCliffordGeneralSpinHorizontalRestrictedPrincipalBlockCoherence
import SMSFormula.RationalCliffordGeneralSpinFiniteAdelicLocalCompactness

/-!
# Fixed-block topology for horizontal finite-adelic GSpin

The complete equivalence between intrinsic finite-adelic `GSpin` points and
cofinally integral local families is algebraic only.  On a fixed horizontal
principal block, however, reverse assembly is continuous: every required
finite-adele coordinate factors through the principal restricted product whose
filter is the complement of that block's finite exceptional set.

This file constructs the genuine intrinsic block, proves that simultaneous
local evaluation and fixed-block assembly are inverse homeomorphisms, and
therefore supplies the measurable bridge needed for later measure transport.
It does not transport a measure, glue blocks, or introduce an ambient Haar
scalar.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open scoped Matrix RestrictedProduct

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 2400000

local instance horizontalGenuineTopologyPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

/-! ## Genuine block and the algebraic fixed-block equivalence -/

/-- Intrinsic finite-adelic `GSpin` points whose evaluated local family lies
in the horizontal `S` principal block. -/
abbrev CliffordGeneralSpinHorizontalGenuinePrincipalBlock
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :=
  {x : V.FiniteAdelicCliffordGeneralSpinGroup //
    V.IsCliffordGeneralSpinHorizontalPrincipalRestrictedFamily S
      (V.finiteAdelicCliffordGeneralSpinRestrictedFamilyMap x)}

/-- Simultaneous local evaluation from the genuine block to the corresponding
restricted-family block. -/
def cliffordGeneralSpinHorizontalGenuineToRestrictedPrincipalBlock
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.CliffordGeneralSpinHorizontalGenuinePrincipalBlock S →
      V.CliffordGeneralSpinHorizontalRestrictedPrincipalBlock S :=
  fun x ↦ ⟨V.finiteAdelicCliffordGeneralSpinRestrictedFamilyMap x.1, x.2⟩

/-- Fixed-block reverse assembly into the intrinsic finite-adelic group. -/
def cliffordGeneralSpinHorizontalRestrictedToGenuinePrincipalBlock
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.CliffordGeneralSpinHorizontalRestrictedPrincipalBlock S →
      V.CliffordGeneralSpinHorizontalGenuinePrincipalBlock S :=
  fun g ↦ by
    refine ⟨V.finiteAdelicCliffordGeneralSpinRestrictedFamilyAssembly g.1, ?_⟩
    have hmap :
        V.finiteAdelicCliffordGeneralSpinRestrictedFamilyMap
            (V.finiteAdelicCliffordGeneralSpinRestrictedFamilyAssembly g.1) =
          g.1 := by
      apply Subtype.ext
      exact V.finiteAdelicCliffordGeneralSpinHeightOneComponents_assembly g.1
    rw [hmap]
    exact g.2

/-- The genuine and restricted-family horizontal blocks are algebraically
equivalent before topology is considered. -/
def cliffordGeneralSpinHorizontalGenuineRestrictedPrincipalBlockEquiv
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.CliffordGeneralSpinHorizontalGenuinePrincipalBlock S ≃
      V.CliffordGeneralSpinHorizontalRestrictedPrincipalBlock S where
  toFun := V.cliffordGeneralSpinHorizontalGenuineToRestrictedPrincipalBlock S
  invFun := V.cliffordGeneralSpinHorizontalRestrictedToGenuinePrincipalBlock S
  left_inv := by
    intro x
    apply Subtype.ext
    exact V.finiteAdelicCliffordGeneralSpinRestrictedFamilyAssembly_components x.1
  right_inv := by
    intro g
    apply Subtype.ext
    apply Subtype.ext
    exact V.finiteAdelicCliffordGeneralSpinHeightOneComponents_assembly g.1

/-- Forward simultaneous local evaluation is continuous on every genuine
block. -/
theorem continuous_cliffordGeneralSpinHorizontalGenuineToRestrictedPrincipalBlock
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Continuous
      (V.cliffordGeneralSpinHorizontalGenuineToRestrictedPrincipalBlock S) := by
  apply Continuous.subtype_mk
  exact V.continuous_finiteAdelicCliffordGeneralSpinRestrictedFamilyMap.comp
    continuous_subtype_val

/-! ## Fixed principal restricted products -/

private abbrev HorizontalGSpinPrincipalAdele
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :=
  Πʳ v : IsDedekindDomain.HeightOneSpectrum ℤ,
    [v.adicCompletion ℚ, v.adicCompletionIntegers ℚ]_[
      Filter.principal
        {v : IsDedekindDomain.HeightOneSpectrum ℤ |
          v ∉ V.cliffordGeneralSpinHorizontalExceptionalPlaces S}]

private theorem cofinite_le_horizontalGSpinPrincipal_compl
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Filter.cofinite ≤ Filter.principal
      {v : IsDedekindDomain.HeightOneSpectrum ℤ |
        v ∉ V.cliffordGeneralSpinHorizontalExceptionalPlaces S} := by
  rw [Filter.le_principal_iff]
  exact (V.cliffordGeneralSpinHorizontalExceptionalPlaces S)
    |>.eventually_cofinite_notMem

private noncomputable def horizontalRestrictedBlockCliffordCoordinate
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (g : V.CliffordGeneralSpinHorizontalRestrictedPrincipalBlock S)
    (s : Finset (Fin n)) : V.HorizontalGSpinPrincipalAdele S :=
  ⟨fun v ↦
      (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm
        ((V.cliffordCoordinateBaseChangeBasis
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]).repr
            ((g.1.1 v).cliffordUnit : V.cliffordCoordinateBaseChangeAlgebra
              ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) s),
    by
      rw [Filter.eventually_principal]
      intro v hv
      apply (mem_adicCompletionIntegers_iff_padic v _).2
      simpa using (g.2 v hv).1 s⟩

private noncomputable def horizontalRestrictedBlockSimilitudeCoordinate
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (g : V.CliffordGeneralSpinHorizontalRestrictedPrincipalBlock S) :
    V.HorizontalGSpinPrincipalAdele S :=
  ⟨fun v ↦
      (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm
        ((g.1.1 v).similitude :
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]),
    by
      rw [Filter.eventually_principal]
      intro v hv
      apply (mem_adicCompletionIntegers_iff_padic v _).2
      simpa using ((mem_padicIntegralUnitsSubgroup_iff _ _).1
        (g.2 v hv).2.2.1).1⟩

private noncomputable def horizontalRestrictedBlockInverseSimilitudeCoordinate
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (g : V.CliffordGeneralSpinHorizontalRestrictedPrincipalBlock S) :
    V.HorizontalGSpinPrincipalAdele S :=
  ⟨fun v ↦
      (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm
        (((g.1.1 v).similitude⁻¹ :
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ) :
            ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]),
    by
      rw [Filter.eventually_principal]
      intro v hv
      apply (mem_adicCompletionIntegers_iff_padic v _).2
      simpa using ((mem_padicIntegralUnitsSubgroup_iff _ _).1
        (g.2 v hv).2.2.1).2⟩

private noncomputable def horizontalRestrictedBlockMatrixCoordinate
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (g : V.CliffordGeneralSpinHorizontalRestrictedPrincipalBlock S)
    (i j : Fin n) : V.HorizontalGSpinPrincipalAdele S :=
  ⟨fun v ↦
      (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm
        ((g.1.1 v).matrixGroup.1.1.1 i j),
    by
      rw [Filter.eventually_principal]
      intro v hv
      apply (mem_adicCompletionIntegers_iff_padic v _).2
      simpa using ((V.mem_padicSpecialOrthogonalIntegralSubgroup_iff _ _).1
        (g.2 v hv).2.2.2).1 i j⟩

private noncomputable def horizontalRestrictedBlockInverseMatrixCoordinate
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (g : V.CliffordGeneralSpinHorizontalRestrictedPrincipalBlock S)
    (i j : Fin n) : V.HorizontalGSpinPrincipalAdele S :=
  ⟨fun v ↦
      (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm
        (((g.1.1 v).matrixGroup.1.1⁻¹).1 i j),
    by
      rw [Filter.eventually_principal]
      intro v hv
      apply (mem_adicCompletionIntegers_iff_padic v _).2
      simpa using ((V.mem_padicSpecialOrthogonalIntegralSubgroup_iff _ _).1
        (g.2 v hv).2.2.2).2 i j⟩

/-! ## Continuity of principal-product coordinates -/

private theorem continuous_horizontalRestrictedBlockCliffordCoordinate
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (s : Finset (Fin n)) :
    Continuous (fun g ↦ V.horizontalRestrictedBlockCliffordCoordinate S g s) := by
  apply RestrictedProduct.continuous_rng_of_principal.mpr
  apply continuous_pi
  intro v
  exact
    (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm.continuous.comp
      ((V.continuous_cliffordGeneralSpinCliffordCoordinate
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] s).comp
          ((continuous_apply v).comp
            (continuous_subtype_val.comp continuous_subtype_val)))

private theorem continuous_horizontalRestrictedBlockSimilitudeCoordinate
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Continuous (fun g ↦ V.horizontalRestrictedBlockSimilitudeCoordinate S g) := by
  apply RestrictedProduct.continuous_rng_of_principal.mpr
  apply continuous_pi
  intro v
  exact
    (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm.continuous.comp
      (Units.continuous_val.comp
        ((V.continuous_cliffordGeneralSpinSimilitude
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]).comp
            ((continuous_apply v).comp
              (continuous_subtype_val.comp continuous_subtype_val))))

private theorem continuous_horizontalRestrictedBlockInverseSimilitudeCoordinate
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Continuous
      (fun g ↦ V.horizontalRestrictedBlockInverseSimilitudeCoordinate S g) := by
  apply RestrictedProduct.continuous_rng_of_principal.mpr
  apply continuous_pi
  intro v
  have hsim : Continuous (fun
      g : V.CliffordGeneralSpinHorizontalRestrictedPrincipalBlock S ↦
        (g.1.1 v).similitude) :=
    (V.continuous_cliffordGeneralSpinSimilitude
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]).comp
        ((continuous_apply v).comp
          (continuous_subtype_val.comp continuous_subtype_val))
  exact
    (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm.continuous.comp
      (Units.continuous_val.comp (continuous_inv.comp hsim))

private theorem continuous_horizontalRestrictedBlockMatrixCoordinate
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (i j : Fin n) :
    Continuous (fun g ↦ V.horizontalRestrictedBlockMatrixCoordinate S g i j) := by
  apply RestrictedProduct.continuous_rng_of_principal.mpr
  apply continuous_pi
  intro v
  exact
    (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm.continuous.comp
      ((V.continuous_cliffordGeneralSpinMatrixCoordinate
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] i j).comp
          ((continuous_apply v).comp
            (continuous_subtype_val.comp continuous_subtype_val)))

private theorem continuous_horizontalRestrictedBlockInverseMatrixCoordinate
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (i j : Fin n) :
    Continuous
      (fun g ↦ V.horizontalRestrictedBlockInverseMatrixCoordinate S g i j) := by
  apply RestrictedProduct.continuous_rng_of_principal.mpr
  apply continuous_pi
  intro v
  exact
    (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm.continuous.comp
      ((V.continuous_cliffordGeneralSpinInvMatrixCoordinate
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] i j).comp
          ((continuous_apply v).comp
            (continuous_subtype_val.comp continuous_subtype_val)))

/-! ## Continuity after inclusion into the finite adeles -/

private theorem continuous_restrictedFamilyCliffordCoordinate_horizontalBlock
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (s : Finset (Fin n)) :
    Continuous (fun g : V.CliffordGeneralSpinHorizontalRestrictedPrincipalBlock S ↦
      V.finiteAdelicCliffordGeneralSpinRestrictedFamilyCliffordCoordinate
        g.1 s) := by
  let R := fun v : IsDedekindDomain.HeightOneSpectrum ℤ ↦ v.adicCompletion ℚ
  let A : (v : IsDedekindDomain.HeightOneSpectrum ℤ) → Set (R v) :=
    fun v ↦ v.adicCompletionIntegers ℚ
  let hS := V.cofinite_le_horizontalGSpinPrincipal_compl S
  let inclusion : V.HorizontalGSpinPrincipalAdele S → RationalFiniteAdele :=
    RestrictedProduct.inclusion R A hS
  have h := (RestrictedProduct.continuous_inclusion hS).comp
    (V.continuous_horizontalRestrictedBlockCliffordCoordinate S s)
  apply h.congr
  intro g
  ext v
  rfl

private theorem continuous_restrictedFamilySimilitude_horizontalBlock
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Continuous (fun g : V.CliffordGeneralSpinHorizontalRestrictedPrincipalBlock S ↦
      V.finiteAdelicCliffordGeneralSpinRestrictedFamilySimilitude g.1) := by
  let R := fun v : IsDedekindDomain.HeightOneSpectrum ℤ ↦ v.adicCompletion ℚ
  let A : (v : IsDedekindDomain.HeightOneSpectrum ℤ) → Set (R v) :=
    fun v ↦ v.adicCompletionIntegers ℚ
  let hS := V.cofinite_le_horizontalGSpinPrincipal_compl S
  let inclusion : V.HorizontalGSpinPrincipalAdele S → RationalFiniteAdele :=
    RestrictedProduct.inclusion R A hS
  have h := (RestrictedProduct.continuous_inclusion hS).comp
    (V.continuous_horizontalRestrictedBlockSimilitudeCoordinate S)
  apply h.congr
  intro g
  ext v
  rfl

private theorem continuous_restrictedFamilyInverseSimilitude_horizontalBlock
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Continuous (fun g : V.CliffordGeneralSpinHorizontalRestrictedPrincipalBlock S ↦
      V.finiteAdelicCliffordGeneralSpinRestrictedFamilyInverseSimilitude g.1) := by
  let R := fun v : IsDedekindDomain.HeightOneSpectrum ℤ ↦ v.adicCompletion ℚ
  let A : (v : IsDedekindDomain.HeightOneSpectrum ℤ) → Set (R v) :=
    fun v ↦ v.adicCompletionIntegers ℚ
  let hS := V.cofinite_le_horizontalGSpinPrincipal_compl S
  let inclusion : V.HorizontalGSpinPrincipalAdele S → RationalFiniteAdele :=
    RestrictedProduct.inclusion R A hS
  have h := (RestrictedProduct.continuous_inclusion hS).comp
    (V.continuous_horizontalRestrictedBlockInverseSimilitudeCoordinate S)
  apply h.congr
  intro g
  ext v
  rfl

private theorem continuous_restrictedFamilySimilitudeUnit_horizontalBlock
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Continuous (fun g : V.CliffordGeneralSpinHorizontalRestrictedPrincipalBlock S ↦
      V.finiteAdelicCliffordGeneralSpinRestrictedFamilySimilitudeUnit g.1) := by
  apply Units.continuous_iff.mpr
  constructor
  · exact V.continuous_restrictedFamilySimilitude_horizontalBlock S
  · exact V.continuous_restrictedFamilyInverseSimilitude_horizontalBlock S

private theorem continuous_restrictedFamilyMatrixCoordinate_horizontalBlock
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (i j : Fin n) :
    Continuous (fun g : V.CliffordGeneralSpinHorizontalRestrictedPrincipalBlock S ↦
      V.finiteAdelicSpecialOrthogonalRestrictedFamilyMatrixEntry
        (V.finiteAdelicCliffordGeneralSpinRestrictedFamilySOFamily g.1) i j) := by
  let R := fun v : IsDedekindDomain.HeightOneSpectrum ℤ ↦ v.adicCompletion ℚ
  let A : (v : IsDedekindDomain.HeightOneSpectrum ℤ) → Set (R v) :=
    fun v ↦ v.adicCompletionIntegers ℚ
  let hS := V.cofinite_le_horizontalGSpinPrincipal_compl S
  let inclusion : V.HorizontalGSpinPrincipalAdele S → RationalFiniteAdele :=
    RestrictedProduct.inclusion R A hS
  have h := (RestrictedProduct.continuous_inclusion hS).comp
    (V.continuous_horizontalRestrictedBlockMatrixCoordinate S i j)
  apply h.congr
  intro g
  ext v
  rfl

private theorem continuous_restrictedFamilyInverseMatrixCoordinate_horizontalBlock
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (i j : Fin n) :
    Continuous (fun g : V.CliffordGeneralSpinHorizontalRestrictedPrincipalBlock S ↦
      V.finiteAdelicSpecialOrthogonalRestrictedFamilyInverseMatrixEntry
        (V.finiteAdelicCliffordGeneralSpinRestrictedFamilySOFamily g.1) i j) := by
  let R := fun v : IsDedekindDomain.HeightOneSpectrum ℤ ↦ v.adicCompletion ℚ
  let A : (v : IsDedekindDomain.HeightOneSpectrum ℤ) → Set (R v) :=
    fun v ↦ v.adicCompletionIntegers ℚ
  let hS := V.cofinite_le_horizontalGSpinPrincipal_compl S
  let inclusion : V.HorizontalGSpinPrincipalAdele S → RationalFiniteAdele :=
    RestrictedProduct.inclusion R A hS
  have h := (RestrictedProduct.continuous_inclusion hS).comp
    (V.continuous_horizontalRestrictedBlockInverseMatrixCoordinate S i j)
  apply h.congr
  intro g
  ext v
  rfl

private theorem continuous_restrictedFamilySO_horizontalBlock
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Continuous (fun g : V.CliffordGeneralSpinHorizontalRestrictedPrincipalBlock S ↦
      V.finiteAdelicCliffordGeneralSpinRestrictedFamilySO g.1) := by
  apply continuous_induced_rng.mpr
  apply continuous_induced_rng.mpr
  apply Units.continuous_iff.mpr
  constructor
  · apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact V.continuous_restrictedFamilyMatrixCoordinate_horizontalBlock S i j
  · apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact V.continuous_restrictedFamilyInverseMatrixCoordinate_horizontalBlock S i j

/-! ## Reverse continuity and the fixed-block homeomorphism -/

/-- Reverse assembly is continuous on every fixed horizontal principal block. -/
theorem continuous_cliffordGeneralSpinHorizontalRestrictedToGenuinePrincipalBlock
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Continuous
      (V.cliffordGeneralSpinHorizontalRestrictedToGenuinePrincipalBlock S) := by
  apply Continuous.subtype_mk
  apply continuous_induced_rng.mpr
  apply Continuous.prodMk
  · apply Continuous.prodMk
    · apply continuous_pi
      intro s
      have h := V.continuous_restrictedFamilyCliffordCoordinate_horizontalBlock S s
      apply h.congr
      intro g
      have hz :=
        V.finiteAdelicCliffordGeneralSpinRestrictedFamilyAssembly_closedCoordinate g.1
      simpa [cliffordGeneralSpinClosedCoordinateMap,
        finiteAdelicCliffordGeneralSpinRestrictedFamilyClosedCoordinate] using
          (congrArg (fun z ↦ z.1.1.1 s) hz).symm
    · have h := V.continuous_restrictedFamilySimilitudeUnit_horizontalBlock S
      apply h.congr
      intro g
      have hz :=
        V.finiteAdelicCliffordGeneralSpinRestrictedFamilyAssembly_closedCoordinate g.1
      simpa [cliffordGeneralSpinClosedCoordinateMap,
        finiteAdelicCliffordGeneralSpinRestrictedFamilyClosedCoordinate] using
          (congrArg (fun z ↦ z.1.2) hz).symm
  · apply Continuous.prodMk
    · have hSO := V.continuous_restrictedFamilySO_horizontalBlock S
      have hmatrix : Continuous (fun
          g : V.CliffordGeneralSpinHorizontalRestrictedPrincipalBlock S ↦
          (V.finiteAdelicCliffordGeneralSpinRestrictedFamilySO g.1).1.1.1) :=
        Units.continuous_val.comp
          (continuous_subtype_val.comp (continuous_subtype_val.comp hSO))
      apply hmatrix.congr
      intro g
      have hz :=
        V.finiteAdelicCliffordGeneralSpinRestrictedFamilyAssembly_closedCoordinate g.1
      simpa [cliffordGeneralSpinClosedCoordinateMap,
        finiteAdelicCliffordGeneralSpinRestrictedFamilyClosedCoordinate] using
          (congrArg (fun z ↦ z.2.1.1.1) hz).symm
    · have hSO := V.continuous_restrictedFamilySO_horizontalBlock S
      have hinv : Continuous (fun
          g : V.CliffordGeneralSpinHorizontalRestrictedPrincipalBlock S ↦
          ((V.finiteAdelicCliffordGeneralSpinRestrictedFamilySO g.1).1.1⁻¹).1) :=
        Units.continuous_val.comp
          (continuous_inv.comp
            (continuous_subtype_val.comp (continuous_subtype_val.comp hSO)))
      apply hinv.congr
      intro g
      have hz :=
        V.finiteAdelicCliffordGeneralSpinRestrictedFamilyAssembly_closedCoordinate g.1
      simpa [cliffordGeneralSpinClosedCoordinateMap,
        finiteAdelicCliffordGeneralSpinRestrictedFamilyClosedCoordinate] using
          (congrArg (fun z ↦ (z.2.1.1⁻¹).1) hz).symm

/-- On a fixed horizontal principal block, simultaneous local evaluation is a
homeomorphism from the genuine intrinsic carrier to the restricted family. -/
noncomputable def cliffordGeneralSpinHorizontalGenuineRestrictedPrincipalBlockHomeomorph
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.CliffordGeneralSpinHorizontalGenuinePrincipalBlock S ≃ₜ
      V.CliffordGeneralSpinHorizontalRestrictedPrincipalBlock S where
  toEquiv := V.cliffordGeneralSpinHorizontalGenuineRestrictedPrincipalBlockEquiv S
  continuous_toFun :=
    V.continuous_cliffordGeneralSpinHorizontalGenuineToRestrictedPrincipalBlock S
  continuous_invFun :=
    V.continuous_cliffordGeneralSpinHorizontalRestrictedToGenuinePrincipalBlock S

end RationalQuadraticSpaceMatrix
