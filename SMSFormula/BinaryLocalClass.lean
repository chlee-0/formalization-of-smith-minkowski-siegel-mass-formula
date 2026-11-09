import SMSFormula.BinaryLocalIdeal

/-!
# Actual local order-unit norm classes

The quotient uses units of the actual quadratic order, including at 2 and
conductor primes. The quadratic algebra is allowed to split.
-/

namespace BinaryNormIdeal

/-- Norm on units of the actual scalar-extended discriminant order. -/
def orderUnitNorm (R : Type*) [CommRing R] (D : ℤ) :
    (DiscriminantAlgebra R D)ˣ →* Rˣ :=
  Units.map QuadraticAlgebra.norm

/-- Norms of actual order units, with no maximal-order replacement. -/
def orderUnitNormSubgroup (R : Type*) [CommRing R] (D : ℤ) : Subgroup Rˣ :=
  (orderUnitNorm R D).range

abbrev OrderUnitNormQuotient (R : Type*) [CommRing R] (D : ℤ) :=
  Rˣ ⧸ orderUnitNormSubgroup R D

/-- The actual local unit-norm quotient map. -/
def orderUnitNormQuotientMap (R : Type*) [CommRing R] (D : ℤ) :
    Rˣ →* OrderUnitNormQuotient R D :=
  QuotientGroup.mk' (orderUnitNormSubgroup R D)

/-- Quotient equality gives an explicit order-unit witness. -/
lemma orderUnitNormQuotientMap_eq_iff (R : Type*) [CommRing R] (D : ℤ) (u t : Rˣ) :
    orderUnitNormQuotientMap R D u=orderUnitNormQuotientMap R D t ↔
      ∃ z : (DiscriminantAlgebra R D)ˣ, (u : R)=(t : R)*z.val.norm := by
  constructor
  · intro h
    obtain ⟨w,⟨z,rfl⟩,he⟩ := (QuotientGroup.mk'_eq_mk' (orderUnitNormSubgroup R D)).mp h.symm
    exact ⟨z,congrArg Units.val he.symm⟩
  · rintro ⟨z,hz⟩
    symm
    apply (QuotientGroup.mk'_eq_mk' (orderUnitNormSubgroup R D)).mpr
    refine ⟨orderUnitNorm R D z,⟨z,rfl⟩,?_⟩
    exact Units.ext hz.symm

/-- Squares of scalar units are norms of actual order units. -/
lemma orderUnitNormQuotientMap_sq (R : Type*) [CommRing R] (D : ℤ) (u : Rˣ) :
    orderUnitNormQuotientMap R D (u*u)=1 := by
  rw [← map_one (orderUnitNormQuotientMap R D)]
  apply (orderUnitNormQuotientMap_eq_iff _ _ _ _).mpr
  refine ⟨Units.map (algebraMap R (DiscriminantAlgebra R D)) u,?_⟩
  simp [QuadraticAlgebra.norm_def]

/-- The actual local quotient has exponent at most two. -/
lemma orderUnitNormQuotient_sq (R : Type*) [CommRing R] (D : ℤ)
    (q : OrderUnitNormQuotient R D) : q*q=1 := by
  obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective (orderUnitNormSubgroup R D) q
  exact (map_mul (orderUnitNormQuotientMap R D) u u).symm.trans
    (orderUnitNormQuotientMap_sq R D u)

end BinaryNormIdeal

namespace PositiveDefiniteIntegralLattice

open BinaryNormIdeal

/-- A represented p-adic unit, used only to choose a quotient representative. -/
noncomputable def binaryPadicRepresentedUnit (L : PositiveDefiniteIntegralLattice 2)
    (p : ℕ) [Fact (Nat.Prime p)] : ℤ_[p]ˣ :=
  Classical.choose (show ∃ u : ℤ_[p]ˣ, ∃ v, L.binaryPrimitivePolynomialOver ℤ_[p] v=(u : ℤ_[p]) from by
    obtain ⟨v,u,hv⟩ := L.binaryPrimitivePolynomialOver_padic_exists_unit p
    exact ⟨u,v,hv.symm⟩)

lemma binaryPadicRepresentedUnit_spec (L : PositiveDefiniteIntegralLattice 2)
    (p : ℕ) [Fact (Nat.Prime p)] :
    ∃ v, L.binaryPrimitivePolynomialOver ℤ_[p] v=(L.binaryPadicRepresentedUnit p : ℤ_[p]) :=
  Classical.choose_spec (show ∃ u : ℤ_[p]ˣ, ∃ v, L.binaryPrimitivePolynomialOver ℤ_[p] v=(u : ℤ_[p]) from by
    obtain ⟨v,u,hv⟩ := L.binaryPrimitivePolynomialOver_padic_exists_unit p
    exact ⟨u,v,hv.symm⟩)

/-- The quotient class of the unit values in the specified actual order. -/
noncomputable def binaryLocalNormClassAt (L : PositiveDefiniteIntegralLattice 2) (D : ℤ)
    (_hD : L.binaryPrimitiveDiscriminant=D) (p : ℕ) [Fact (Nat.Prime p)] :
    OrderUnitNormQuotient ℤ_[p] D :=
  orderUnitNormQuotientMap ℤ_[p] D (L.binaryPadicRepresentedUnit p)

/-- The local class equals the class of any chosen represented unit. -/
theorem binaryLocalNormClassAt_eq (L : PositiveDefiniteIntegralLattice 2) (D : ℤ)
    (hD : L.binaryPrimitiveDiscriminant=D) (p : ℕ) [Fact (Nat.Prime p)]
    (v : Fin 2 → ℤ_[p]) (u : ℤ_[p]ˣ) (hv : L.binaryPrimitivePolynomialOver ℤ_[p] v=(u : ℤ_[p])) :
    L.binaryLocalNormClassAt D hD p=orderUnitNormQuotientMap ℤ_[p] D u := by
  subst D
  obtain ⟨w,hw⟩ := L.binaryPadicRepresentedUnit_spec p
  apply (orderUnitNormQuotientMap_eq_iff _ _ _ _).mpr
  exact (L.binaryPrimitivePolynomialOver_unit_values_iff v u (L.binaryPadicRepresentedUnit p) hv).mp ⟨w,hw⟩

/-- Equality of local quotient classes is the existing actual norm predicate. -/
theorem binaryLocalNormClassAt_eq_iff (K L : PositiveDefiniteIntegralLattice 2)
    (D : ℤ) (hK : K.binaryPrimitiveDiscriminant=D) (hL : L.binaryPrimitiveDiscriminant=D)
    (p : ℕ) [Fact (Nat.Prime p)] :
    K.binaryLocalNormClassAt D hK p=L.binaryLocalNormClassAt D hL p ↔
      K.binaryLocalUnitNormCondition L ℤ_[p] := by
  subst D
  constructor
  · intro h
    obtain ⟨v,hv⟩ := K.binaryPadicRepresentedUnit_spec p
    obtain ⟨w,hw⟩ := L.binaryPadicRepresentedUnit_spec p
    exact ⟨v,w,K.binaryPadicRepresentedUnit p,L.binaryPadicRepresentedUnit p,hv,hw,
      (orderUnitNormQuotientMap_eq_iff _ _ _ _).mp h⟩
  · rintro ⟨v,w,u,t,hv,hw,hz⟩
    rw [K.binaryLocalNormClassAt_eq _ rfl p v u hv,L.binaryLocalNormClassAt_eq _ hL p w t hw]
    exact (orderUnitNormQuotientMap_eq_iff _ _ _ _).mpr hz

/-- Multiplication of actual ideal classes gives multiplication of quotient
classes in any fixed common order. No genus assertion is used. -/
theorem binaryLocalNormClassAt_mul (K L M : PositiveDefiniteIntegralLattice 2)
    (D : ℤ) (hK : K.binaryPrimitiveDiscriminant=D)
    (hL : L.binaryPrimitiveDiscriminant=D) (hM : M.binaryPrimitiveDiscriminant=D)
    [IsDomain (DiscriminantOrder D)]
    (hclass : binaryIdealClassAt K D hK*binaryIdealClassAt L D hL=binaryIdealClassAt M D hM)
    (p : ℕ) [Fact (Nat.Prime p)] :
    K.binaryLocalNormClassAt D hK p*L.binaryLocalNormClassAt D hL p=
      M.binaryLocalNormClassAt D hM p := by
  subst D
  obtain ⟨v,hv⟩ := K.binaryPadicRepresentedUnit_spec p
  obtain ⟨w,hw⟩ := L.binaryPadicRepresentedUnit_spec p
  obtain ⟨x,hx⟩ := M.binaryPadicRepresentedUnit_spec p
  have he := K.exists_binaryLocalNormProduct_unit L M hL hM hclass p v w x
    (K.binaryPadicRepresentedUnit p) (L.binaryPadicRepresentedUnit p) (M.binaryPadicRepresentedUnit p) hv hw hx
  change orderUnitNormQuotientMap _ _ _*orderUnitNormQuotientMap _ _ _=_
  rw [← map_mul]
  exact (orderUnitNormQuotientMap_eq_iff _ _ _ _).mpr he

/-- Equal actual classes at fixed content give equal local quotient classes. -/
theorem binaryLocalNormClassAt_eq_of_class_eq (K L : PositiveDefiniteIntegralLattice 2)
    (hg : K.binaryContent=L.binaryContent) (D : ℤ)
    (hK : K.binaryPrimitiveDiscriminant=D) (hL : L.binaryPrimitiveDiscriminant=D)
    [IsDomain (DiscriminantOrder D)]
    (hc : binaryIdealClassAt K D hK=binaryIdealClassAt L D hL)
    (p : ℕ) [Fact (Nat.Prime p)] :
    K.binaryLocalNormClassAt D hK p=L.binaryLocalNormClassAt D hL p := by
  have hp := (binaryIdealClassAt_eq_iff_isProperGlobalIsometry K L hg D hK hL).mp hc.symm
  have hgen := isSameGenus_of_isGlobalIsometry (isGlobalIsometry_of_isProperGlobalIsometry hp)
  exact (binaryLocalNormClassAt_eq_iff K L D hK hL p).mpr
    (((isSameGenus_iff_binaryLocalUnitNormCondition K L).mp hgen).2.2.1 p)

/-- A fixed-content actual lattice realizing an arbitrary canonical class. -/
noncomputable def binaryIdealClassLattice (K : PositiveDefiniteIntegralLattice 2)
    (xi : letI := K.binaryDiscriminantOrder_isDomain
      ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant)) : PositiveDefiniteIntegralLattice 2 :=
  Classical.choose (K.exists_lattice_of_binaryIdealClass xi)

lemma binaryIdealClassLattice_content (K : PositiveDefiniteIntegralLattice 2)
    (xi : letI := K.binaryDiscriminantOrder_isDomain
      ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant)) :
    (K.binaryIdealClassLattice xi).binaryContent=K.binaryContent :=
  (Classical.choose_spec (K.exists_lattice_of_binaryIdealClass xi)).1

lemma binaryIdealClassLattice_discriminant (K : PositiveDefiniteIntegralLattice 2)
    (xi : letI := K.binaryDiscriminantOrder_isDomain
      ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant)) :
    (K.binaryIdealClassLattice xi).binaryPrimitiveDiscriminant=K.binaryPrimitiveDiscriminant :=
  Classical.choose (Classical.choose_spec (K.exists_lattice_of_binaryIdealClass xi)).2

lemma binaryIdealClassLattice_class (K : PositiveDefiniteIntegralLattice 2)
    (xi : letI := K.binaryDiscriminantOrder_isDomain
      ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant)) :
    letI := K.binaryDiscriminantOrder_isDomain
    binaryIdealClassAt (K.binaryIdealClassLattice xi) K.binaryPrimitiveDiscriminant
      (K.binaryIdealClassLattice_discriminant xi)=xi :=
  Classical.choose_spec (Classical.choose_spec (K.exists_lattice_of_binaryIdealClass xi)).2

/-- Local norm class of an arbitrary canonical ideal class, using an actual
fixed-content lattice representative. -/
noncomputable def binaryIdealLocalNormClass (K : PositiveDefiniteIntegralLattice 2)
    (p : ℕ) [Fact (Nat.Prime p)]
    (xi : letI := K.binaryDiscriminantOrder_isDomain
      ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant)) :
    OrderUnitNormQuotient ℤ_[p] K.binaryPrimitiveDiscriminant :=
  (K.binaryIdealClassLattice xi).binaryLocalNormClassAt K.binaryPrimitiveDiscriminant
    (K.binaryIdealClassLattice_discriminant xi) p

/-- Evaluation is independent of the chosen actual fixed-content lattice. -/
theorem binaryIdealLocalNormClass_spec (K L : PositiveDefiniteIntegralLattice 2)
    (hg : L.binaryContent=K.binaryContent)
    (hD : L.binaryPrimitiveDiscriminant=K.binaryPrimitiveDiscriminant)
    (p : ℕ) [Fact (Nat.Prime p)] :
    letI := K.binaryDiscriminantOrder_isDomain
    K.binaryIdealLocalNormClass p (L.binaryIdealClassAt K.binaryPrimitiveDiscriminant hD)=
      L.binaryLocalNormClassAt K.binaryPrimitiveDiscriminant hD p := by
  letI := K.binaryDiscriminantOrder_isDomain
  exact binaryLocalNormClassAt_eq_of_class_eq _ L
    ((K.binaryIdealClassLattice_content _).trans hg.symm) _
    (K.binaryIdealClassLattice_discriminant _) hD (K.binaryIdealClassLattice_class _) p

/-- The representative-independent class function preserves actual Picard
multiplication. This uses norms of units of the original local order. -/
theorem binaryIdealLocalNormClass_mul (K : PositiveDefiniteIntegralLattice 2)
    (p : ℕ) [Fact (Nat.Prime p)]
    (xi eta : letI := K.binaryDiscriminantOrder_isDomain
      ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant)) :
    letI := K.binaryDiscriminantOrder_isDomain
    K.binaryIdealLocalNormClass p (xi*eta)=K.binaryIdealLocalNormClass p xi*K.binaryIdealLocalNormClass p eta := by
  letI := K.binaryDiscriminantOrder_isDomain
  symm
  apply binaryLocalNormClassAt_mul _ _ _ _
    (K.binaryIdealClassLattice_discriminant xi)
    (K.binaryIdealClassLattice_discriminant eta)
    (K.binaryIdealClassLattice_discriminant (xi*eta))
  rw [K.binaryIdealClassLattice_class,K.binaryIdealClassLattice_class,K.binaryIdealClassLattice_class]

/-- The actual arbitrary-order Picard group homomorphism to local unit norms.
No field, maximal-order or odd-conductor premise is added. -/
noncomputable def binaryIdealLocalNormHom (K : PositiveDefiniteIntegralLattice 2)
    (p : ℕ) [Fact (Nat.Prime p)] :
    letI := K.binaryDiscriminantOrder_isDomain
    ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant) →*
      OrderUnitNormQuotient ℤ_[p] K.binaryPrimitiveDiscriminant := by
  letI := K.binaryDiscriminantOrder_isDomain
  refine { toFun := K.binaryIdealLocalNormClass p
           map_one' := ?_
           map_mul' := K.binaryIdealLocalNormClass_mul p }
  have hh := K.binaryIdealLocalNormClass_mul p 1 1
  simp only [one_mul] at hh
  exact hh.trans (orderUnitNormQuotient_sq ℤ_[p] K.binaryPrimitiveDiscriminant _)

/-- The homomorphism has its prescribed value on every actual lattice at
the original content and discriminant. -/
theorem binaryIdealLocalNormHom_apply (K L : PositiveDefiniteIntegralLattice 2)
    (hg : L.binaryContent=K.binaryContent)
    (hD : L.binaryPrimitiveDiscriminant=K.binaryPrimitiveDiscriminant)
    (p : ℕ) [Fact (Nat.Prime p)]
    (v : Fin 2 → ℤ_[p]) (u : ℤ_[p]ˣ) (hv : L.binaryPrimitivePolynomialOver ℤ_[p] v=(u : ℤ_[p])) :
    letI := K.binaryDiscriminantOrder_isDomain
    K.binaryIdealLocalNormHom p (L.binaryIdealClassAt K.binaryPrimitiveDiscriminant hD)=
      orderUnitNormQuotientMap ℤ_[p] K.binaryPrimitiveDiscriminant u := by
  exact (K.binaryIdealLocalNormClass_spec L hg hD p).trans
    (L.binaryLocalNormClassAt_eq _ hD p v u hv)

/-- The original genus is detected by the local Picard homomorphisms and
the original real-place condition, at fixed actual content and discriminant. -/
theorem isSameGenus_iff_binaryIdealLocalNormHom_eq (K L : PositiveDefiniteIntegralLattice 2)
    (hg : L.binaryContent=K.binaryContent)
    (hD : L.binaryPrimitiveDiscriminant=K.binaryPrimitiveDiscriminant) :
    letI := K.binaryDiscriminantOrder_isDomain
    K.IsSameGenus L ↔
      (∀ (p : ℕ) [Fact (Nat.Prime p)],
        K.binaryIdealLocalNormHom p (L.binaryIdealClassAt K.binaryPrimitiveDiscriminant hD)=
          K.binaryIdealLocalNormHom p (K.binaryIdealClassAt K.binaryPrimitiveDiscriminant rfl)) ∧
      Nonempty ((K.binaryPrimitivePolynomialOver ℝ).IsometryEquiv
        (L.binaryPrimitivePolynomialOver ℝ)) := by
  letI := K.binaryDiscriminantOrder_isDomain
  have he (p : ℕ) [Fact (Nat.Prime p)] :
      K.binaryLocalUnitNormCondition L ℤ_[p] ↔
        K.binaryIdealLocalNormHom p (L.binaryIdealClassAt K.binaryPrimitiveDiscriminant hD)=
          K.binaryIdealLocalNormHom p (K.binaryIdealClassAt K.binaryPrimitiveDiscriminant rfl) := by
    change _ ↔ K.binaryIdealLocalNormClass p _=K.binaryIdealLocalNormClass p _
    rw [K.binaryIdealLocalNormClass_spec L hg hD p,K.binaryIdealLocalNormClass_spec K rfl rfl p]
    exact (binaryLocalNormClassAt_eq_iff K L _ rfl hD p).symm.trans eq_comm
  rw [isSameGenus_iff_binaryLocalUnitNormCondition]
  constructor
  · rintro ⟨_,_,hf,hr⟩
    exact ⟨fun p hp => (he p).mp (hf p),hr⟩
  · rintro ⟨hf,hr⟩
    exact ⟨hg.symm,hD,fun p hp => (he p).mpr (hf p),hr⟩

/-- The simultaneous finite-place kernel in the existing arbitrary-order
Picard group. Its equality with squares is a separate principal-genus task. -/
noncomputable def binaryIdealLocalNormKernel (K : PositiveDefiniteIntegralLattice 2) :
    letI := K.binaryDiscriminantOrder_isDomain
    Subgroup (ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant)) := by
  letI := K.binaryDiscriminantOrder_isDomain
  exact {
    carrier := {xi | ∀ (p : ℕ) [Fact (Nat.Prime p)], K.binaryIdealLocalNormHom p xi=1}
    one_mem' := fun p hp => map_one _
    mul_mem' := fun hx hy p hp => by
      rw [map_mul,hx p,hy p]
      exact one_mul (1 : OrderUnitNormQuotient ℤ_[p] K.binaryPrimitiveDiscriminant)
    inv_mem' := fun hx p hp => by rw [map_inv,hx p,inv_one] }

/-- Actual class squares belong to every finite-place norm kernel. -/
theorem square_mem_binaryIdealLocalNormKernel (K : PositiveDefiniteIntegralLattice 2)
    (xi : letI := K.binaryDiscriminantOrder_isDomain
      ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant)) :
    letI := K.binaryDiscriminantOrder_isDomain
    xi*xi ∈ K.binaryIdealLocalNormKernel := by
  letI := K.binaryDiscriminantOrder_isDomain
  intro p hp
  rw [map_mul]
  exact orderUnitNormQuotient_sq _ _ _

/-- The original genus is the simultaneous-kernel fiber, with the original
real clause. No assertion that this kernel equals squares is assumed. -/
theorem isSameGenus_iff_binaryIdealLocalNormKernel (K L : PositiveDefiniteIntegralLattice 2)
    (hg : L.binaryContent=K.binaryContent)
    (hD : L.binaryPrimitiveDiscriminant=K.binaryPrimitiveDiscriminant) :
    letI := K.binaryDiscriminantOrder_isDomain
    K.IsSameGenus L ↔
      L.binaryIdealClassAt K.binaryPrimitiveDiscriminant hD*
        (K.binaryIdealClassAt K.binaryPrimitiveDiscriminant rfl)⁻¹ ∈ K.binaryIdealLocalNormKernel ∧
      Nonempty ((K.binaryPrimitivePolynomialOver ℝ).IsometryEquiv
        (L.binaryPrimitivePolynomialOver ℝ)) := by
  letI := K.binaryDiscriminantOrder_isDomain
  rw [isSameGenus_iff_binaryIdealLocalNormHom_eq K L hg hD]
  have he : (∀ (p : ℕ) [Fact (Nat.Prime p)],
      K.binaryIdealLocalNormHom p (L.binaryIdealClassAt K.binaryPrimitiveDiscriminant hD)=
        K.binaryIdealLocalNormHom p (K.binaryIdealClassAt K.binaryPrimitiveDiscriminant rfl)) ↔
      L.binaryIdealClassAt K.binaryPrimitiveDiscriminant hD*
        (K.binaryIdealClassAt K.binaryPrimitiveDiscriminant rfl)⁻¹ ∈ K.binaryIdealLocalNormKernel := by
    change (∀ (p : ℕ) [Fact (Nat.Prime p)], _) ↔ ∀ (p : ℕ) [Fact (Nat.Prime p)], _
    constructor
    · intro h p hp
      rw [map_mul,map_inv,h p,mul_inv_cancel]
    · intro h p hp
      have hh := h p
      rw [map_mul,map_inv,mul_inv_eq_one] at hh
      exact hh
  exact and_congr_left (fun _ => he)

end PositiveDefiniteIntegralLattice

#assert_standard_axioms BinaryNormIdeal.orderUnitNorm
#assert_standard_axioms BinaryNormIdeal.orderUnitNormSubgroup
#assert_standard_axioms BinaryNormIdeal.OrderUnitNormQuotient
#assert_standard_axioms BinaryNormIdeal.orderUnitNormQuotientMap
#assert_standard_axioms BinaryNormIdeal.orderUnitNormQuotientMap_eq_iff
#assert_standard_axioms BinaryNormIdeal.orderUnitNormQuotientMap_sq
#assert_standard_axioms BinaryNormIdeal.orderUnitNormQuotient_sq
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryPadicRepresentedUnit
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryPadicRepresentedUnit_spec
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryLocalNormClassAt
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryLocalNormClassAt_eq
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryLocalNormClassAt_eq_iff
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryLocalNormClassAt_mul
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryLocalNormClassAt_eq_of_class_eq
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryIdealClassLattice
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryIdealClassLattice_content
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryIdealClassLattice_discriminant
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryIdealClassLattice_class
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryIdealLocalNormClass
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryIdealLocalNormClass_spec
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryIdealLocalNormClass_mul
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryIdealLocalNormHom
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryIdealLocalNormHom_apply
#assert_standard_axioms PositiveDefiniteIntegralLattice.isSameGenus_iff_binaryIdealLocalNormHom_eq
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryIdealLocalNormKernel
#assert_standard_axioms PositiveDefiniteIntegralLattice.square_mem_binaryIdealLocalNormKernel
#assert_standard_axioms PositiveDefiniteIntegralLattice.isSameGenus_iff_binaryIdealLocalNormKernel
