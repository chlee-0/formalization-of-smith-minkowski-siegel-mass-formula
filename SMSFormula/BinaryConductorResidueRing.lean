import SMSFormula.BinaryPicardSurjectivity
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Data.Nat.Totient

/-!
# The actual original conductor residue ring

The proved basis beginning with one identifies the original conductor
residue ring with integers modulo the already defined positive index.
-/

namespace BinaryNormIdeal

/-- In an integer basis beginning with one, the integer intersection of
n*B is exactly n*Z. No conductor or maximality assumption is used. -/
theorem intCast_mem_span_nat_iff {B : Type*} [CommRing B]
    (e : Module.Basis (Fin 2) ℤ B) (he : e 0=1) (n : ℕ) (m : ℤ) :
    (m : B) ∈ Ideal.span {(n : B)} ↔ (n : ℤ) ∣ m := by
  have hcoord (k : ℤ) : e.repr (k : B) 0=k := by
    have hk : (k : B)=k • e 0 := by rw [he]; simp [zsmul_eq_mul]
    rw [hk,map_smul]
    simp
  rw [Ideal.mem_span_singleton]
  constructor
  · rintro ⟨z,hz⟩
    refine ⟨e.repr z 0,?_⟩
    have h := congrArg (fun w : B => e.repr w 0) hz
    have hn : (n : B)*z=(n : ℤ) • z := by simp [zsmul_eq_mul]
    rw [hn] at h
    change e.repr (m : B) 0=e.repr ((n : ℤ) • z) 0 at h
    rw [map_smul,hcoord] at h
    simpa using h
  · rintro ⟨k,hk⟩
    refine ⟨(k : B),?_⟩
    simpa only [Int.cast_mul,Int.cast_natCast] using congrArg (fun t : ℤ => (t : B)) hk

/-- The full scalar quotient of a rank-two integer algebra has n squared
classes. Its submodule basis is constructed from actual multiplication by n. -/
theorem card_quotient_span_nat {B : Type*} [CommRing B]
    (e : Module.Basis (Fin 2) ℤ B) (n : ℕ) (hn : n ≠ 0) :
    Nat.card (B ⧸ Ideal.span {(n : B)})=n^2 := by
  letI := Module.Free.of_basis e
  letI := Module.Finite.of_basis e
  let N : Submodule ℤ B := (Ideal.span {(n : B)}).restrictScalars ℤ
  let f : B →ₗ[ℤ] N := {
    toFun := fun x => ⟨(n : ℤ) • x,by
      change (n : ℤ) • x ∈ Ideal.span {(n : B)}
      exact Ideal.mem_span_singleton.mpr ⟨x,by simp [zsmul_eq_mul]⟩⟩
    map_add' := by intro x y; apply Subtype.ext; exact smul_add _ _ _
    map_smul' := by
      intro r x
      apply Subtype.ext
      change (n : ℤ) • (r • x)=r • ((n : ℤ) • x)
      rw [smul_smul,smul_smul,mul_comm] }
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      apply e.repr.injective
      ext i
      have hh := congrArg (fun z : N => e.repr (z : B) i) h
      change e.repr ((n : ℤ) • x) i=e.repr ((n : ℤ) • y) i at hh
      simp only [map_smul,Finsupp.smul_apply,smul_eq_mul] at hh
      exact mul_left_cancel₀ (show (n : ℤ) ≠ 0 by exact_mod_cast hn) hh
    · intro z
      obtain ⟨x,hx⟩ := Ideal.mem_span_singleton.mp z.prop
      refine ⟨x,Subtype.ext ?_⟩
      change (n : ℤ) • x=(z : B)
      simpa only [zsmul_eq_mul,Int.cast_natCast] using hx.symm
  let ef := LinearEquiv.ofBijective f hf
  let bN := e.map ef
  have hN (i : Fin 2) : (bN i : B)=(n : ℤ) • e i := rfl
  have hdet : (e.det ((↑) ∘ bN))=(n : ℤ)^2 := by
    rw [Module.Basis.det_apply,Matrix.det_fin_two]
    simp only [Module.Basis.toMatrix_apply,Function.comp_apply,hN,map_smul,
      Finsupp.smul_apply,Module.Basis.repr_self,smul_eq_mul]
    simp
    ring
  change Nat.card (B ⧸ N)=n^2
  rw [← Submodule.natAbs_det_basis_change e N bN,hdet,Int.natAbs_pow,Int.natAbs_natCast]

variable (a b c : ℤ) [IsDomain (CoefficientOrder a b c)]

/-- An integer belongs to the original pulled-back conductor iff the
Actual positive order index divides that integer. -/
theorem intCast_mem_originalConductor_iff (hD : b^2-4*a*c<0) (m : ℤ) :
    (m : CoefficientOrder a b c) ∈ originalConductorIdeal a b c ↔
      (orderIndex a b c : ℤ) ∣ m := by
  change orderToRingOfIntegers a b c (m : CoefficientOrder a b c) ∈ orderConductor a b c ↔ _
  rw [map_intCast,orderConductor_eq_span_index a b c hD]
  exact intCast_mem_span_nat_iff (maximalOrderBasisOne a b c hD)
    (maximalOrderBasisOne_zero a b c hD) _ _

/-- Every actual original conductor residue is an integer residue. This
uses image(A)=Z+I*B, with the same literal conductor and order index. -/
theorem originalConductorIntCast_surjective (hD : b^2-4*a*c<0) :
    Function.Surjective (Int.castRingHom
      (CoefficientOrder a b c ⧸ originalConductorIdeal a b c)) := by
  intro q
  obtain ⟨r,rfl⟩ := Ideal.Quotient.mk_surjective q
  obtain ⟨m,w,hr⟩ := (mem_orderImage_iff_int_add_index_mul a b c hD
    (orderToRingOfIntegers a b c r)).mp ⟨r,rfl⟩
  refine ⟨m,?_⟩
  change (m : CoefficientOrder a b c ⧸ originalConductorIdeal a b c)=
    Ideal.Quotient.mk (originalConductorIdeal a b c) r
  rw [← map_intCast (Ideal.Quotient.mk (originalConductorIdeal a b c)) m]
  apply Ideal.Quotient.eq.mpr
  change orderToRingOfIntegers a b c ((m : CoefficientOrder a b c)-r) ∈ orderConductor a b c
  rw [map_sub,map_intCast,hr]
  have hm : (orderIndex a b c : NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c)))*w ∈
      orderConductor a b c := by
    rw [orderConductor_eq_span_index a b c hD]
    exact Ideal.mem_span_singleton.mpr ⟨w,rfl⟩
  have hh := (orderConductor a b c).neg_mem hm
  convert hh using 1
  ring

/-- The exact kernel of the original integer residue map. -/
theorem originalConductorIntCast_ker (hD : b^2-4*a*c<0) :
    RingHom.ker (Int.castRingHom (CoefficientOrder a b c ⧸ originalConductorIdeal a b c)) =
      Ideal.span {(orderIndex a b c : ℤ)} := by
  ext m
  change (m : CoefficientOrder a b c ⧸ originalConductorIdeal a b c)=0 ↔ _
  rw [← map_intCast (Ideal.Quotient.mk (originalConductorIdeal a b c)) m,Ideal.Quotient.eq_zero_iff_mem,
    intCast_mem_originalConductor_iff a b c hD,Ideal.mem_span_singleton]

/-- The original conductor residue ring, on its actual quotient carrier,
is exactly Z/I for the already proved positive quotient index. -/
noncomputable def originalConductorResidueEquivZMod (hD : b^2-4*a*c<0) :
    CoefficientOrder a b c ⧸ originalConductorIdeal a b c ≃+* ZMod (orderIndex a b c) :=
  ((RingHom.quotientKerEquivOfSurjective (originalConductorIntCast_surjective a b c hD)).symm.trans
    (Ideal.quotEquivOfEq (originalConductorIntCast_ker a b c hD))).trans
      (Int.quotientSpanNatEquivZMod (orderIndex a b c))

theorem originalConductorResidueEquivZMod_intCast (hD : b^2-4*a*c<0) (m : ℤ) :
    originalConductorResidueEquivZMod a b c hD (m : CoefficientOrder a b c ⧸ originalConductorIdeal a b c)=
      (m : ZMod (orderIndex a b c)) := map_intCast _ m

/-- The residue embedding into the same maximal-order conductor quotient
is injective on its actual original carrier. -/
theorem originalConductorResidueMap_injective :
    Function.Injective (originalConductorResidueMap a b c) :=
  Ideal.quotientMap_injective

/-- No original residue units are lost under the actual residue embedding. -/
theorem originalConductorResidueUnitsHom_injective :
    Function.Injective (originalConductorResidueUnitsHom a b c) :=
  Units.map_injective (originalConductorResidueMap_injective a b c)

theorem finite_originalConductorResidue (hD : b^2-4*a*c<0) :
    Finite (CoefficientOrder a b c ⧸ originalConductorIdeal a b c) := by
  letI : NeZero (orderIndex a b c) := ⟨ne_of_gt (orderIndex_pos a b c hD)⟩
  exact Finite.of_equiv _ (originalConductorResidueEquivZMod a b c hD).symm.toEquiv

theorem card_originalConductorResidue (hD : b^2-4*a*c<0) :
    Nat.card (CoefficientOrder a b c ⧸ originalConductorIdeal a b c)=orderIndex a b c := by
  rw [Nat.card_congr (originalConductorResidueEquivZMod a b c hD).toEquiv,Nat.card_zmod]

/-- The same maximal-order conductor residue has I squared elements. -/
theorem card_maximalConductorResidue (hD : b^2-4*a*c<0) :
    Nat.card (NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c)) ⧸ orderConductor a b c)=
      (orderIndex a b c)^2 := by
  rw [orderConductor_eq_span_index a b c hD]
  exact card_quotient_span_nat (maximalOrderBasisOne a b c hD) _ (ne_of_gt (orderIndex_pos a b c hD))

theorem finite_maximalConductorResidue (hD : b^2-4*a*c<0) :
    Finite (NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c)) ⧸ orderConductor a b c) := by
  apply Nat.finite_of_card_ne_zero
  rw [card_maximalConductorResidue a b c hD]
  exact pow_ne_zero _ (ne_of_gt (orderIndex_pos a b c hD))

/-- The original residue unit count is the actual Euler totient of I,
including the unit count one when I=1 and the residue ring is zero. -/
theorem card_originalConductorResidueUnits (hD : b^2-4*a*c<0) :
    Nat.card (CoefficientOrder a b c ⧸ originalConductorIdeal a b c)ˣ =
      Nat.totient (orderIndex a b c) := by
  letI : NeZero (orderIndex a b c) := ⟨ne_of_gt (orderIndex_pos a b c hD)⟩
  rw [Nat.card_congr (Units.mapEquiv (originalConductorResidueEquivZMod a b c hD).toMulEquiv).toEquiv,
    Nat.card_eq_fintype_card,ZMod.card_units_eq_totient]

/-- Exact denominator in the residue-unit quotient count. The maximal-order
residue unit count is left as it is, not evaluated by an Euler factor. -/
theorem card_conductorResidueQuotient_mul_totient (hD : b^2-4*a*c<0) :
    Nat.card (ConductorResidueUnitQuotient a b c)*Nat.totient (orderIndex a b c) =
      Nat.card (ConductorResidueUnits a b c) := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (originalConductorResidueUnitsHom a b c).range
  have hr : Nat.card (originalConductorResidueUnitsHom a b c).range =
      Nat.card (CoefficientOrder a b c ⧸ originalConductorIdeal a b c)ˣ :=
    (Nat.card_congr (Equiv.ofInjective _ (originalConductorResidueUnitsHom_injective a b c))).symm
  rw [hr,card_originalConductorResidueUnits a b c hD] at h
  exact h.symm


/-- The actual maximal conductor residue unit group is finite before
any splitting type, quadratic character or Euler factor is evaluated. -/
theorem finite_conductorResidueUnits (hD : b^2-4*a*c<0) :
    Finite (ConductorResidueUnits a b c) := by
  letI := finite_maximalConductorResidue a b c hD
  infer_instance

/-- The literal quotient unit count has the exact positive totient
denominator. This is natural-number division with proved exact divisibility. -/
theorem card_conductorResidueQuotient_eq_div_totient (hD : b^2-4*a*c<0) :
    Nat.card (ConductorResidueUnitQuotient a b c) =
      Nat.card (ConductorResidueUnits a b c) / Nat.totient (orderIndex a b c) := by
  rw [← card_conductorResidueQuotient_mul_totient a b c hD]
  exact (Nat.mul_div_left _ (Nat.totient_pos.mpr (orderIndex_pos a b c hD))).symm

/-- A rational form of the same exact quotient count. The numerator
remains the actual maximal-order residue unit count. -/
theorem card_conductorResidueQuotient_rat_eq_div_totient (hD : b^2-4*a*c<0) :
    (Nat.card (ConductorResidueUnitQuotient a b c) : ℚ) =
      (Nat.card (ConductorResidueUnits a b c) : ℚ) / Nat.totient (orderIndex a b c) := by
  have hp : (Nat.totient (orderIndex a b c) : ℚ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Nat.totient_pos.mpr (orderIndex_pos a b c hD)))
  apply (eq_div_iff hp).mpr
  exact_mod_cast card_conductorResidueQuotient_mul_totient a b c hD

/-- The native class-number/unit correction with its original residue
unit denominator now explicitly evaluated as totient(I). -/
theorem classNumber_div_orderUnits_eq_maximal_mul_residueUnits_div_totient (hD : b^2-4*a*c<0) :
    (Nat.card (ClassGroup (CoefficientOrder a b c)) : ℚ) / Nat.card (CoefficientOrder a b c)ˣ =
      (Nat.card (ClassGroup (NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c)))) : ℚ) /
        Nat.card (NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c)))ˣ *
          ((Nat.card (ConductorResidueUnits a b c) : ℚ) / Nat.totient (orderIndex a b c)) := by
  rw [classNumber_div_orderUnits_eq_maximalClassNumber_div_units_mul_residueQuotient a b c hD,
    card_conductorResidueQuotient_rat_eq_div_totient a b c hD]

end BinaryNormIdeal

namespace PositiveDefiniteIntegralLattice

open BinaryNormIdeal

/-- The original conductor residue ring of K, including original content,
is identified with integers modulo K's actual positive order index. -/
noncomputable def binaryOriginalConductorResidueEquivZMod (K : PositiveDefiniteIntegralLattice 2) :
    letI := K.binaryDiscriminantOrder_isDomain
    DiscriminantOrder K.binaryPrimitiveDiscriminant ⧸
      originalConductorIdeal 1 (K.binaryPrimitiveDiscriminant%2)
        (((K.binaryPrimitiveDiscriminant%2)^2-K.binaryPrimitiveDiscriminant)/4) ≃+*
          ZMod K.binaryOrderIndex := by
  letI := K.binaryDiscriminantOrder_isDomain
  exact originalConductorResidueEquivZMod _ _ _ K.binaryDiscriminantOrder_discriminant_neg

theorem card_binaryMaximalConductorResidue (K : PositiveDefiniteIntegralLattice 2) :
    letI := K.binaryDiscriminantOrder_isDomain
    Nat.card (NumberField.RingOfIntegers (FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant)) ⧸
      K.binaryOrderConductor)=K.binaryOrderIndex^2 := by
  letI := K.binaryDiscriminantOrder_isDomain
  exact card_maximalConductorResidue _ _ _ K.binaryDiscriminantOrder_discriminant_neg

/-- Exact actual residue-unit quotient count with the evaluated original
denominator. No field residue Euler count is substituted for the numerator. -/
theorem card_binaryConductorResidueQuotient_mul_totient (K : PositiveDefiniteIntegralLattice 2) :
    letI := K.binaryDiscriminantOrder_isDomain
    Nat.card (ConductorResidueUnitQuotient 1 (K.binaryPrimitiveDiscriminant%2)
      (((K.binaryPrimitiveDiscriminant%2)^2-K.binaryPrimitiveDiscriminant)/4)) *
        Nat.totient K.binaryOrderIndex =
          Nat.card (ConductorResidueUnits 1 (K.binaryPrimitiveDiscriminant%2)
            (((K.binaryPrimitiveDiscriminant%2)^2-K.binaryPrimitiveDiscriminant)/4)) := by
  letI := K.binaryDiscriminantOrder_isDomain
  exact card_conductorResidueQuotient_mul_totient _ _ _ K.binaryDiscriminantOrder_discriminant_neg

end PositiveDefiniteIntegralLattice

#assert_standard_axioms BinaryNormIdeal.intCast_mem_span_nat_iff
#assert_standard_axioms BinaryNormIdeal.card_quotient_span_nat
#assert_standard_axioms BinaryNormIdeal.intCast_mem_originalConductor_iff
#assert_standard_axioms BinaryNormIdeal.originalConductorIntCast_surjective
#assert_standard_axioms BinaryNormIdeal.originalConductorIntCast_ker
#assert_standard_axioms BinaryNormIdeal.originalConductorResidueEquivZMod
#assert_standard_axioms BinaryNormIdeal.originalConductorResidueEquivZMod_intCast
#assert_standard_axioms BinaryNormIdeal.originalConductorResidueMap_injective
#assert_standard_axioms BinaryNormIdeal.originalConductorResidueUnitsHom_injective
#assert_standard_axioms BinaryNormIdeal.finite_originalConductorResidue
#assert_standard_axioms BinaryNormIdeal.card_originalConductorResidue
#assert_standard_axioms BinaryNormIdeal.card_maximalConductorResidue
#assert_standard_axioms BinaryNormIdeal.finite_maximalConductorResidue
#assert_standard_axioms BinaryNormIdeal.card_originalConductorResidueUnits
#assert_standard_axioms BinaryNormIdeal.card_conductorResidueQuotient_mul_totient
#assert_standard_axioms BinaryNormIdeal.finite_conductorResidueUnits
#assert_standard_axioms BinaryNormIdeal.card_conductorResidueQuotient_eq_div_totient
#assert_standard_axioms BinaryNormIdeal.card_conductorResidueQuotient_rat_eq_div_totient
#assert_standard_axioms BinaryNormIdeal.classNumber_div_orderUnits_eq_maximal_mul_residueUnits_div_totient
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryOriginalConductorResidueEquivZMod
#assert_standard_axioms PositiveDefiniteIntegralLattice.card_binaryMaximalConductorResidue
#assert_standard_axioms PositiveDefiniteIntegralLattice.card_binaryConductorResidueQuotient_mul_totient
