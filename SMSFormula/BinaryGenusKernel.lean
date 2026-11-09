import SMSFormula.BinaryLocalClass

/-!
# The actual binary genus as a local norm kernel coset

A positive real scalar square root removes the original real-place clause
at equal primitive discriminant. The actual proper genus is then the coset
of the simultaneous finite-place Picard kernel. Its equality with the class
square subgroup remains a separate principal-genus theorem.
-/

namespace PositiveDefiniteIntegralLattice

open BinaryNormIdeal

/-- Positive definiteness gives an actual determinant-one real isometry at
equal primitive discriminant. Original contents need not agree. -/
theorem exists_binaryPrimitivePolynomialOver_real_proper_isometry
    (K L : PositiveDefiniteIntegralLattice 2)
    (hD : L.binaryPrimitiveDiscriminant=K.binaryPrimitiveDiscriminant) :
    ∃ e : (K.binaryPrimitivePolynomialOver ℝ).IsometryEquiv (L.binaryPrimitivePolynomialOver ℝ),
      (LinearMap.toMatrix' e.toLinearEquiv.toLinearMap).det=1 := by
  let a : ℝ := ((K.pairingMatrix 0 0/(K.binaryContent : ℤ) : ℤ) : ℝ)
  let b : ℝ := ((L.pairingMatrix 0 0/(L.binaryContent : ℤ) : ℤ) : ℝ)
  have ha : 0<a := by
    dsimp only [a]
    exact_mod_cast K.binaryPrimitivePolynomial_leading_pos
  have hb : 0<b := by
    dsimp only [b]
    exact_mod_cast L.binaryPrimitivePolynomial_leading_pos
  let u : ℝˣ := Units.mk0 a (ne_of_gt ha)
  let t : ℝˣ := Units.mk0 b (ne_of_gt hb)
  have hv : K.binaryPrimitivePolynomialOver ℝ ![1,0]=(u : ℝ) := by
    simp [binaryPrimitivePolynomialOver_apply,u,a]
  have hw : L.binaryPrimitivePolynomialOver ℝ ![1,0]=(t : ℝ) := by
    simp [binaryPrimitivePolynomialOver_apply,t,b]
  apply (binaryPrimitivePolynomialOver_proper_isometry_iff_norm_unit K L hD ![1,0] ![1,0] u t hv hw).mpr
  have hr : 0<a/b := div_pos ha hb
  let s : ℝˣ := Units.mk0 (Real.sqrt (a/b)) (ne_of_gt (Real.sqrt_pos.mpr hr))
  refine ⟨Units.map (algebraMap ℝ (DiscriminantAlgebra ℝ K.binaryPrimitiveDiscriminant)) s,?_⟩
  change a=b*_
  simp only [Units.coe_map]
  simp [s,QuadraticAlgebra.norm_def,← pow_two,Real.sq_sqrt hr.le]
  field_simp

/-- The original real polynomial-isometry clause is automatic at equal D. -/
theorem nonempty_binaryPrimitivePolynomialOver_real_isometry_of_discriminant
    (K L : PositiveDefiniteIntegralLattice 2)
    (hD : L.binaryPrimitiveDiscriminant=K.binaryPrimitiveDiscriminant) :
    Nonempty ((K.binaryPrimitivePolynomialOver ℝ).IsometryEquiv (L.binaryPrimitivePolynomialOver ℝ)) := by
  obtain ⟨e,_⟩ := K.exists_binaryPrimitivePolynomialOver_real_proper_isometry L hD
  exact ⟨e⟩

/-- The original genus is exactly the simultaneous finite-place kernel
fiber at fixed actual content and discriminant. No real certificate is needed. -/
theorem isSameGenus_iff_binaryIdealLocalNormKernel_mem (K L : PositiveDefiniteIntegralLattice 2)
    (hg : L.binaryContent=K.binaryContent)
    (hD : L.binaryPrimitiveDiscriminant=K.binaryPrimitiveDiscriminant) :
    letI := K.binaryDiscriminantOrder_isDomain
    K.IsSameGenus L ↔
      L.binaryIdealClassAt K.binaryPrimitiveDiscriminant hD*
        (K.binaryIdealClassAt K.binaryPrimitiveDiscriminant rfl)⁻¹ ∈ K.binaryIdealLocalNormKernel := by
  letI := K.binaryDiscriminantOrder_isDomain
  rw [K.isSameGenus_iff_binaryIdealLocalNormKernel L hg hD]
  exact and_iff_left (K.nonempty_binaryPrimitivePolynomialOver_real_isometry_of_discriminant L hD)

/-- The exact coset in the existing arbitrary-order Picard group. -/
def binaryIdealKernelCoset (K : PositiveDefiniteIntegralLattice 2) :
    letI := K.binaryDiscriminantOrder_isDomain
    Set (ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant)) := by
  letI := K.binaryDiscriminantOrder_isDomain
  exact {xi | xi*(K.binaryIdealClassAt K.binaryPrimitiveDiscriminant rfl)⁻¹ ∈ K.binaryIdealLocalNormKernel}

/-- The image of the original proper genus is the full simultaneous-kernel
coset. This does not identify that kernel with the class-square subgroup. -/
theorem binaryProperGenusIdealClass_range_eq_kernelCoset (K : PositiveDefiniteIntegralLattice 2) :
    letI := K.binaryDiscriminantOrder_isDomain
    Set.range (K.binaryProperGenusIdealClass)=K.binaryIdealKernelCoset := by
  letI := K.binaryDiscriminantOrder_isDomain
  ext xi
  constructor
  · rintro ⟨C,rfl⟩
    let L := properGenusClassRepresentative K C
    have hgen := properGenusClassRepresentative_isSameGenus K C
    exact (K.isSameGenus_iff_binaryIdealLocalNormKernel_mem L hgen.binaryContent_eq.symm
      hgen.binaryPrimitiveDiscriminant_eq.symm).mp hgen
  · intro hxi
    obtain ⟨L,hg,hD,hclass⟩ := K.exists_lattice_of_binaryIdealClass xi
    have hgen : K.IsSameGenus L :=
      (K.isSameGenus_iff_binaryIdealLocalNormKernel_mem L hg hD).mpr (by rw [hclass]; exact hxi)
    let C : K.properGenus := ⟨L.properGlobalIsometryClass,⟨L,hgen,rfl⟩⟩
    refine ⟨C,?_⟩
    exact (K.binaryProperGenusIdealClass_eq_of_representative C L hgen rfl).trans hclass

/-- Translate the ideal-class image to the simultaneous kernel.
The proper-genus carrier is unchanged. -/
noncomputable def binaryProperGenusKernelEquiv (K : PositiveDefiniteIntegralLattice 2) :
    letI := K.binaryDiscriminantOrder_isDomain
    K.properGenus ≃ K.binaryIdealLocalNormKernel := by
  letI := K.binaryDiscriminantOrder_isDomain
  let c := K.binaryIdealClassAt K.binaryPrimitiveDiscriminant rfl
  let f : K.properGenus → K.binaryIdealLocalNormKernel := fun C =>
    ⟨K.binaryProperGenusIdealClass C*c⁻¹,by
      have hh : K.binaryProperGenusIdealClass C ∈ Set.range K.binaryProperGenusIdealClass := ⟨C,rfl⟩
      rw [K.binaryProperGenusIdealClass_range_eq_kernelCoset] at hh
      exact hh⟩
  apply Equiv.ofBijective f
  constructor
  · intro C C' hh
    apply K.binaryProperGenusIdealClass_injective
    have he := congrArg (fun x : K.binaryIdealLocalNormKernel => x.val*c) hh
    simpa only [f,inv_mul_cancel_right] using he
  · intro t
    have ht : t.val*c ∈ K.binaryIdealKernelCoset := by
      change (t.val*c)*c⁻¹ ∈ K.binaryIdealLocalNormKernel
      simpa only [mul_inv_cancel_right] using t.property
    rw [← K.binaryProperGenusIdealClass_range_eq_kernelCoset] at ht
    obtain ⟨C,hC⟩ := ht
    refine ⟨C,Subtype.ext ?_⟩
    change K.binaryProperGenusIdealClass C*c⁻¹=t.val
    rw [hC,mul_inv_cancel_right]

/-- The simultaneous kernel is finite, by the original proper genus.
No finiteness of the full Picard group is assumed. -/
theorem finite_binaryIdealLocalNormKernel (K : PositiveDefiniteIntegralLattice 2) :
    letI := K.binaryDiscriminantOrder_isDomain
    Finite K.binaryIdealLocalNormKernel := by
  letI := K.binaryDiscriminantOrder_isDomain
  exact Finite.of_injective K.binaryProperGenusKernelEquiv.symm K.binaryProperGenusKernelEquiv.symm.injective

/-- The actual proper-genus count equals the simultaneous-kernel count. -/
theorem card_binaryIdealLocalNormKernel (K : PositiveDefiniteIntegralLattice 2) :
    letI := K.binaryDiscriminantOrder_isDomain
    Nat.card K.binaryIdealLocalNormKernel=Fintype.card K.properGenus := by
  letI := K.binaryDiscriminantOrder_isDomain
  rw [Nat.card_congr K.binaryProperGenusKernelEquiv.symm]
  exact Nat.card_eq_fintype_card

/-- The original ordinary full-O mass is the simultaneous-kernel count
 divided by 2*w_D, using the unchanged aggregate proper/full comparison. -/
theorem ordinaryGenusMass_eq_card_binaryIdealLocalNormKernel_div_two_normOneUnits
    (K : PositiveDefiniteIntegralLattice 2) :
    letI := K.binaryDiscriminantOrder_isDomain
    K.ordinaryGenusMass=
      (Nat.card K.binaryIdealLocalNormKernel : ℚ)/
        (2*(Nat.card (DiscriminantNormOneUnits K.binaryPrimitiveDiscriminant) : ℚ)) := by
  letI := K.binaryDiscriminantOrder_isDomain
  rw [K.card_binaryIdealLocalNormKernel]
  exact K.ordinaryGenusMass_eq_card_properGenus_div_two_discriminantNormOneUnits

end PositiveDefiniteIntegralLattice

#assert_standard_axioms PositiveDefiniteIntegralLattice.exists_binaryPrimitivePolynomialOver_real_proper_isometry
#assert_standard_axioms PositiveDefiniteIntegralLattice.nonempty_binaryPrimitivePolynomialOver_real_isometry_of_discriminant
#assert_standard_axioms PositiveDefiniteIntegralLattice.isSameGenus_iff_binaryIdealLocalNormKernel_mem
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryIdealKernelCoset
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryProperGenusIdealClass_range_eq_kernelCoset
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryProperGenusKernelEquiv
#assert_standard_axioms PositiveDefiniteIntegralLattice.finite_binaryIdealLocalNormKernel
#assert_standard_axioms PositiveDefiniteIntegralLattice.card_binaryIdealLocalNormKernel
#assert_standard_axioms PositiveDefiniteIntegralLattice.ordinaryGenusMass_eq_card_binaryIdealLocalNormKernel_div_two_normOneUnits
