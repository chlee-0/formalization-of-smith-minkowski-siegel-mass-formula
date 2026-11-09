import SMSFormula.RationalCliffordGeneralSpinHorizontalGenuinePrincipalBlockInclusion

/-!
# Open horizontal principal blocks in finite-adelic GSpin

The fixed-block topology constructed earlier does not by itself show that a
genuine block is measurably embedded in the ambient intrinsic finite-adelic
`GSpin` group.  Here we identify block membership with the literal finite-
coordinate condition that the Clifford, inverse-Clifford, similitude,
inverse-similitude, matrix, and inverse-matrix coordinates are integral away
from the displayed finite exceptional set.  The standard restricted-product
topology then makes this locus open.

This is a topology statement only.  No measure normalization, Haar uniqueness,
or quotient comparison is used.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open scoped Matrix RestrictedProduct

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

set_option synthInstance.maxHeartbeats 600000
set_option maxHeartbeats 1200000

local instance horizontalGenuineBlockOpenPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance horizontalGenuineBlockOpenDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

/-- The six finite-coordinate integrality conditions needed by intrinsic
finite-adelic `GSpin`. -/
def IsFiniteAdelicCliffordGeneralSpinIntegralOutside
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (x : V.FiniteAdelicCliffordGeneralSpinGroup) : Prop :=
  (∀ s, finiteAdeleNonintegralPlaces
      ((V.cliffordCoordinateBaseChangeBasis RationalFiniteAdele).repr
        (x.cliffordUnit :
          V.cliffordCoordinateBaseChangeAlgebra RationalFiniteAdele) s) ⊆ S) ∧
  (∀ s, finiteAdeleNonintegralPlaces
      ((V.cliffordCoordinateBaseChangeBasis RationalFiniteAdele).repr
        (((x⁻¹).cliffordUnit :
          (V.cliffordCoordinateBaseChangeAlgebra RationalFiniteAdele)ˣ) :
            V.cliffordCoordinateBaseChangeAlgebra RationalFiniteAdele) s) ⊆ S) ∧
  finiteAdeleNonintegralPlaces
      ((x.similitude : RationalFiniteAdeleˣ) : RationalFiniteAdele) ⊆ S ∧
  finiteAdeleNonintegralPlaces
      (((x.similitude⁻¹ : RationalFiniteAdeleˣ)) : RationalFiniteAdele) ⊆ S ∧
  (∀ i j, finiteAdeleNonintegralPlaces (x.matrixGroup.1.1.1 i j) ⊆ S) ∧
  (∀ i j, finiteAdeleNonintegralPlaces ((x.matrixGroup.1.1⁻¹).1 i j) ⊆ S)

private theorem isOpen_finiteAdeleNonintegralPlaces_subset_gspin
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    IsOpen
      {a : RationalFiniteAdele | finiteAdeleNonintegralPlaces a ⊆ S} := by
  have hopen :
      IsOpen
        {a : RationalFiniteAdele |
          ∀ v, v ∉ S → a v ∈ v.adicCompletionIntegers ℚ} :=
    RestrictedProduct.isOpen_forall_imp_mem
      (fun _v ↦ Valued.isOpen_valuationSubring _)
  convert hopen using 1
  ext a
  constructor
  · intro ha v hvS
    by_contra hnot
    exact hvS (ha ((mem_finiteAdeleNonintegralPlaces_iff a v).2 hnot))
  · intro ha v hv
    by_contra hvS
    exact
      ((mem_finiteAdeleNonintegralPlaces_iff a v).1 hv)
        (ha v hvS)

private theorem finiteAdeleNonintegralPlaces_subset_iff_padic
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (a : RationalFiniteAdele) :
    finiteAdeleNonintegralPlaces a ⊆ S ↔
      ∀ v, v ∉ S →
        Rat.HeightOneSpectrum.adicCompletion.padicEquiv v (a v) ∈
          PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v).1 := by
  constructor
  · intro ha v hv
    apply (mem_adicCompletionIntegers_iff_padic v _).1
    by_contra hnot
    exact hv (ha ((mem_finiteAdeleNonintegralPlaces_iff a v).2 hnot))
  · intro ha v hv
    by_contra hvS
    exact ((mem_finiteAdeleNonintegralPlaces_iff a v).1 hv)
      ((mem_adicCompletionIntegers_iff_padic v _).2 (ha v hvS))

/-- Global finite-coordinate integrality is exactly placewise integrality of
the evaluated intrinsic `GSpin` point. -/
theorem isFiniteAdelicCliffordGeneralSpinIntegralOutside_iff
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (x : V.FiniteAdelicCliffordGeneralSpinGroup) :
    V.IsFiniteAdelicCliffordGeneralSpinIntegralOutside S x ↔
      ∀ v, v ∉ S →
        V.PadicCliffordGeneralSpinIsIntegral
          (Rat.HeightOneSpectrum.primesEquiv v).1
          (V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v x) := by
  constructor
  · rintro ⟨hc, hci, hnu, hnui, hm, hmi⟩ v hv
    unfold PadicCliffordGeneralSpinIsIntegral
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro s
      have hs :=
        (finiteAdeleNonintegralPlaces_subset_iff_padic S _).1 (hc s) v hv
      simpa [finiteAdelicCliffordGeneralSpinHeightOneComponentHom,
        finiteAdelicCliffordGeneralSpinHeightOneAlgHom_apply,
        V.cliffordCoordinateBaseChangeBasis_repr_map] using hs
    · intro s
      have hs :=
        (finiteAdeleNonintegralPlaces_subset_iff_padic S _).1 (hci s) v hv
      change (V.cliffordCoordinateBaseChangeBasis
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]).repr
          (((V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v x)⁻¹).cliffordUnit :
            V.cliffordCoordinateBaseChangeAlgebra
              ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) s ∈ PadicInt.subring _
      rw [← (V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v).map_inv]
      simpa [finiteAdelicCliffordGeneralSpinHeightOneComponentHom,
        finiteAdelicCliffordGeneralSpinHeightOneAlgHom_apply,
        V.cliffordCoordinateBaseChangeBasis_repr_map] using hs
    · rw [mem_padicIntegralUnitsSubgroup_iff]
      constructor
      · have hs :=
          (finiteAdeleNonintegralPlaces_subset_iff_padic S _).1 hnu v hv
        simpa [finiteAdelicCliffordGeneralSpinHeightOneComponentHom,
          finiteAdelicCliffordGeneralSpinHeightOneAlgHom_apply] using hs
      · have hs :=
          (finiteAdeleNonintegralPlaces_subset_iff_padic S _).1 hnui v hv
        change
          (((V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v x)⁻¹).similitude :
            ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) ∈ PadicInt.subring _
        rw [← (V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v).map_inv]
        change finiteAdelicCliffordGeneralSpinHeightOneAlgHom v
            (((x.similitude⁻¹ : RationalFiniteAdeleˣ) : RationalFiniteAdele)) ∈
          PadicInt.subring _
        exact hs
    · rw [V.mem_padicSpecialOrthogonalIntegralSubgroup_iff]
      constructor
      · intro i j
        have hs :=
          (finiteAdeleNonintegralPlaces_subset_iff_padic S _).1 (hm i j) v hv
        simpa [finiteAdelicCliffordGeneralSpinHeightOneComponentHom,
          finiteAdelicCliffordGeneralSpinHeightOneAlgHom_apply] using hs
      · intro i j
        have hs :=
          (finiteAdeleNonintegralPlaces_subset_iff_padic S _).1 (hmi i j) v hv
        change
          ((V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v x)⁻¹).matrixGroup.1.1.1
            i j ∈ PadicInt.subring _
        rw [← (V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v).map_inv]
        change finiteAdelicCliffordGeneralSpinHeightOneAlgHom v
            ((x.matrixGroup.1.1⁻¹).1 i j) ∈ PadicInt.subring _
        exact hs
  · intro hx
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro s
      apply (finiteAdeleNonintegralPlaces_subset_iff_padic S _).2
      intro v hv
      have hs := (hx v hv).1 s
      simpa [finiteAdelicCliffordGeneralSpinHeightOneComponentHom,
        finiteAdelicCliffordGeneralSpinHeightOneAlgHom_apply,
        V.cliffordCoordinateBaseChangeBasis_repr_map] using hs
    · intro s
      apply (finiteAdeleNonintegralPlaces_subset_iff_padic S _).2
      intro v hv
      have hs := (hx v hv).2.1 s
      change (V.cliffordCoordinateBaseChangeBasis
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]).repr
          (((V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v x)⁻¹).cliffordUnit :
            V.cliffordCoordinateBaseChangeAlgebra
              ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) s ∈ PadicInt.subring _ at hs
      rw [← (V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v).map_inv] at hs
      simpa [finiteAdelicCliffordGeneralSpinHeightOneComponentHom,
        finiteAdelicCliffordGeneralSpinHeightOneAlgHom_apply,
        V.cliffordCoordinateBaseChangeBasis_repr_map] using hs
    · apply (finiteAdeleNonintegralPlaces_subset_iff_padic S _).2
      intro v hv
      have hs := ((mem_padicIntegralUnitsSubgroup_iff _ _).1 (hx v hv).2.2.1).1
      simpa [finiteAdelicCliffordGeneralSpinHeightOneComponentHom,
        finiteAdelicCliffordGeneralSpinHeightOneAlgHom_apply] using hs
    · apply (finiteAdeleNonintegralPlaces_subset_iff_padic S _).2
      intro v hv
      have hs := ((mem_padicIntegralUnitsSubgroup_iff _ _).1 (hx v hv).2.2.1).2
      change
        (((V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v x)⁻¹).similitude :
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) ∈ PadicInt.subring _ at hs
      rw [← (V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v).map_inv] at hs
      change finiteAdelicCliffordGeneralSpinHeightOneAlgHom v
          (((x.similitude⁻¹ : RationalFiniteAdeleˣ) : RationalFiniteAdele)) ∈
        PadicInt.subring _ at hs
      exact hs
    · intro i j
      apply (finiteAdeleNonintegralPlaces_subset_iff_padic S _).2
      intro v hv
      have hs := ((V.mem_padicSpecialOrthogonalIntegralSubgroup_iff _ _).1
        (hx v hv).2.2.2).1 i j
      simpa [finiteAdelicCliffordGeneralSpinHeightOneComponentHom,
        finiteAdelicCliffordGeneralSpinHeightOneAlgHom_apply] using hs
    · intro i j
      apply (finiteAdeleNonintegralPlaces_subset_iff_padic S _).2
      intro v hv
      have hs := ((V.mem_padicSpecialOrthogonalIntegralSubgroup_iff _ _).1
        (hx v hv).2.2.2).2 i j
      change
        ((V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v x)⁻¹).matrixGroup.1.1.1
          i j ∈ PadicInt.subring _ at hs
      rw [← (V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v).map_inv] at hs
      change finiteAdelicCliffordGeneralSpinHeightOneAlgHom v
          ((x.matrixGroup.1.1⁻¹).1 i j) ∈ PadicInt.subring _ at hs
      exact hs

/-- The literal global coordinate-integrality condition is open in the
intrinsic finite-adelic `GSpin` topology. -/
theorem isOpen_isFiniteAdelicCliffordGeneralSpinIntegralOutside
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    IsOpen
      {x : V.FiniteAdelicCliffordGeneralSpinGroup |
        V.IsFiniteAdelicCliffordGeneralSpinIntegralOutside S x} := by
  unfold IsFiniteAdelicCliffordGeneralSpinIntegralOutside
  apply IsOpen.inter
  · have h : IsOpen
      (⋂ s, {x : V.FiniteAdelicCliffordGeneralSpinGroup |
        finiteAdeleNonintegralPlaces
          ((V.cliffordCoordinateBaseChangeBasis RationalFiniteAdele).repr
            (x.cliffordUnit :
              V.cliffordCoordinateBaseChangeAlgebra RationalFiniteAdele) s) ⊆ S}) :=
      isOpen_iInter_of_finite fun s ↦
      (isOpen_finiteAdeleNonintegralPlaces_subset_gspin S).preimage
        (V.continuous_cliffordGeneralSpinCliffordCoordinate
          RationalFiniteAdele s)
    convert h using 1
    ext x
    change (∀ s, finiteAdeleNonintegralPlaces
      ((V.cliffordCoordinateBaseChangeBasis RationalFiniteAdele).repr
        (x.cliffordUnit :
          V.cliffordCoordinateBaseChangeAlgebra RationalFiniteAdele) s) ⊆ S) ↔ _
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
  · apply IsOpen.inter
    · have h : IsOpen
        (⋂ s, {x : V.FiniteAdelicCliffordGeneralSpinGroup |
          finiteAdeleNonintegralPlaces
            ((V.cliffordCoordinateBaseChangeBasis RationalFiniteAdele).repr
              (((x⁻¹).cliffordUnit :
                (V.cliffordCoordinateBaseChangeAlgebra RationalFiniteAdele)ˣ) :
                  V.cliffordCoordinateBaseChangeAlgebra RationalFiniteAdele) s) ⊆ S}) :=
        isOpen_iInter_of_finite fun s ↦
        (isOpen_finiteAdeleNonintegralPlaces_subset_gspin S).preimage
          ((V.continuous_cliffordGeneralSpinCliffordCoordinate
            RationalFiniteAdele s).comp continuous_inv)
      convert h using 1
      ext x
      change (∀ s, finiteAdeleNonintegralPlaces
        ((V.cliffordCoordinateBaseChangeBasis RationalFiniteAdele).repr
          (((x⁻¹).cliffordUnit :
            (V.cliffordCoordinateBaseChangeAlgebra RationalFiniteAdele)ˣ) :
              V.cliffordCoordinateBaseChangeAlgebra RationalFiniteAdele) s) ⊆ S) ↔ _
      simp only [Set.mem_iInter, Set.mem_setOf_eq]
    · apply IsOpen.inter
      · exact (isOpen_finiteAdeleNonintegralPlaces_subset_gspin S).preimage
          (Units.continuous_val.comp
            (V.continuous_cliffordGeneralSpinSimilitude RationalFiniteAdele))
      · apply IsOpen.inter
        · exact (isOpen_finiteAdeleNonintegralPlaces_subset_gspin S).preimage
            (Units.continuous_val.comp
              (continuous_inv.comp
                (V.continuous_cliffordGeneralSpinSimilitude
                  RationalFiniteAdele)))
        · apply IsOpen.inter
          · have h : IsOpen
              (⋂ i, ⋂ j, {x : V.FiniteAdelicCliffordGeneralSpinGroup |
                finiteAdeleNonintegralPlaces
                  (x.matrixGroup.1.1.1 i j) ⊆ S}) := by
              apply isOpen_iInter_of_finite
              intro i
              apply isOpen_iInter_of_finite
              intro j
              exact (isOpen_finiteAdeleNonintegralPlaces_subset_gspin S).preimage
                (V.continuous_cliffordGeneralSpinMatrixCoordinate
                  RationalFiniteAdele i j)
            convert h using 1
            ext x
            change (∀ i j, finiteAdeleNonintegralPlaces
              (x.matrixGroup.1.1.1 i j) ⊆ S) ↔ _
            simp only [Set.mem_iInter, Set.mem_setOf_eq]
          · have h : IsOpen
              (⋂ i, ⋂ j, {x : V.FiniteAdelicCliffordGeneralSpinGroup |
                finiteAdeleNonintegralPlaces
                  ((x.matrixGroup.1.1⁻¹).1 i j) ⊆ S}) := by
              apply isOpen_iInter_of_finite
              intro i
              apply isOpen_iInter_of_finite
              intro j
              exact (isOpen_finiteAdeleNonintegralPlaces_subset_gspin S).preimage
                (V.continuous_cliffordGeneralSpinInvMatrixCoordinate
                  RationalFiniteAdele i j)
            convert h using 1
            ext x
            change (∀ i j, finiteAdeleNonintegralPlaces
              ((x.matrixGroup.1.1⁻¹).1 i j) ⊆ S) ↔ _
            simp only [Set.mem_iInter, Set.mem_setOf_eq]

/-- Every genuine horizontal principal block is open in the ambient intrinsic
finite-adelic `GSpin` group. -/
theorem isOpen_cliffordGeneralSpinHorizontalGenuinePrincipalBlock
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    IsOpen
      {x : V.FiniteAdelicCliffordGeneralSpinGroup |
        V.IsCliffordGeneralSpinHorizontalPrincipalRestrictedFamily S
          (V.finiteAdelicCliffordGeneralSpinRestrictedFamilyMap x)} := by
  let E := S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  rw [show
      {x : V.FiniteAdelicCliffordGeneralSpinGroup |
        V.IsCliffordGeneralSpinHorizontalPrincipalRestrictedFamily S
          (V.finiteAdelicCliffordGeneralSpinRestrictedFamilyMap x)} =
        {x : V.FiniteAdelicCliffordGeneralSpinGroup |
          V.IsFiniteAdelicCliffordGeneralSpinIntegralOutside E x} by
      ext x
      change (
        ∀ v, v ∉ E →
          V.PadicCliffordGeneralSpinIsIntegral
            (Rat.HeightOneSpectrum.primesEquiv v).1
            (V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v x)) ↔ _
      exact (V.isFiniteAdelicCliffordGeneralSpinIntegralOutside_iff E x).symm]
  exact V.isOpen_isFiniteAdelicCliffordGeneralSpinIntegralOutside E

end RationalQuadraticSpaceMatrix
