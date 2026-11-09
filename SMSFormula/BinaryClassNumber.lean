import SMSFormula.BinaryPrincipalGenus

/-!
# Finite canonical binary order class groups and mass counts

The original fixed-determinant lattice-class finiteness theorem and actual
fixed-content class realization prove finiteness of the canonical order
class group. No analytic class-number formula is assumed here.
-/

namespace PositiveDefiniteIntegralLattice

open BinaryNormIdeal
open scoped nonZeroDivisors

/-- There are finitely many original proper integral lattice classes at
fixed rank and determinant. Each ordinary class is covered by the finite
proper genus of one representative. This is not pointwise mass doubling. -/
theorem fixed_rank_pairingDeterminant_proper_isometry_classes_finite
    {n : ℕ} (d : ℤ) :
    Set.Finite {C : Set (PositiveDefiniteIntegralLattice n) |
      ∃ L : PositiveDefiniteIntegralLattice n, L.pairingDeterminant=d ∧ C=L.properGlobalIsometryClass} := by
  classical
  let S : Set (Set (PositiveDefiniteIntegralLattice n)) :=
    {C | ∃ L : PositiveDefiniteIntegralLattice n, L.pairingDeterminant=d ∧ C=L.globalIsometryClass}
  have hS : S.Finite := fixed_rank_pairingDeterminant_isometry_classes_finite d
  letI : Fintype S := hS.fintype
  let rep (C : S) : PositiveDefiniteIntegralLattice n := Classical.choose C.prop
  have hrep (C : S) : (rep C).pairingDeterminant=d ∧ C.val=(rep C).globalIsometryClass :=
    Classical.choose_spec C.prop
  have hU : (⋃ C : S, (rep C).properGenus).Finite :=
    Set.finite_iUnion (fun C => (rep C).properGenus_finite)
  apply hU.subset
  rintro C ⟨L,hdet,hC⟩
  let A : S := ⟨L.globalIsometryClass,⟨L,hdet,rfl⟩⟩
  refine Set.mem_iUnion.mpr ⟨A,?_⟩
  refine ⟨L,?_,hC⟩
  apply isSameGenus_of_isGlobalIsometry
  apply isGlobalIsometry_of_globalIsometryClass_eq
  exact (hrep A).2.symm

/-- The original determinant is fixed by original binary content and
primitive discriminant, with the exact g squared D=-4*det convention. -/
theorem pairingDeterminant_eq_of_binaryContent_discriminant (K L : PositiveDefiniteIntegralLattice 2)
    (hg : L.binaryContent=K.binaryContent)
    (hD : L.binaryPrimitiveDiscriminant=K.binaryPrimitiveDiscriminant) :
    L.pairingDeterminant=K.pairingDeterminant := by
  have hL := L.binaryContent_sq_mul_binaryPrimitiveDiscriminant
  have hK := K.binaryContent_sq_mul_binaryPrimitiveDiscriminant
  rw [hg,hD] at hL
  linarith

/-- Actual fixed-(g,D) realization embeds the entire canonical order class
group into original proper lattice classes. No genus premise is imposed. -/
theorem binaryIdealClassLattice_properGlobalIsometryClass_injective
    (K : PositiveDefiniteIntegralLattice 2) :
    letI := K.binaryDiscriminantOrder_isDomain
    Function.Injective (fun xi : ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant) =>
      (K.binaryIdealClassLattice xi).properGlobalIsometryClass) := by
  letI := K.binaryDiscriminantOrder_isDomain
  intro xi eta h
  have hproper := isProperGlobalIsometry_of_properGlobalIsometryClass_eq h
  have hg : (K.binaryIdealClassLattice xi).binaryContent=
      (K.binaryIdealClassLattice eta).binaryContent :=
    (K.binaryIdealClassLattice_content xi).trans (K.binaryIdealClassLattice_content eta).symm
  have hh := (binaryIdealClassAt_eq_iff_isProperGlobalIsometry
    (K.binaryIdealClassLattice xi) (K.binaryIdealClassLattice eta) hg
    K.binaryPrimitiveDiscriminant (K.binaryIdealClassLattice_discriminant xi)
    (K.binaryIdealClassLattice_discriminant eta)).mpr hproper
  simpa only [K.binaryIdealClassLattice_class] using hh.symm

/-- The entire canonical class group of the original quadratic order is
finite, including nonmaximal orders. No Dedekind or analytic premise is used. -/
theorem finite_binaryClassGroup (K : PositiveDefiniteIntegralLattice 2) :
    letI := K.binaryDiscriminantOrder_isDomain
    Finite (ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant)) := by
  letI := K.binaryDiscriminantOrder_isDomain
  let S : Set (Set (PositiveDefiniteIntegralLattice 2)) :=
    {C | ∃ L : PositiveDefiniteIntegralLattice 2, L.pairingDeterminant=K.pairingDeterminant ∧
      C=L.properGlobalIsometryClass}
  have hS : S.Finite := fixed_rank_pairingDeterminant_proper_isometry_classes_finite _
  letI : Fintype S := hS.fintype
  let f : ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant) → S := fun xi =>
    ⟨(K.binaryIdealClassLattice xi).properGlobalIsometryClass,
      ⟨K.binaryIdealClassLattice xi,
        K.pairingDeterminant_eq_of_binaryContent_discriminant _
          (K.binaryIdealClassLattice_content xi) (K.binaryIdealClassLattice_discriminant xi),rfl⟩⟩
  apply Finite.of_injective f
  intro xi eta h
  exact K.binaryIdealClassLattice_properGlobalIsometryClass_injective (congrArg Subtype.val h)

/-- The actual canonical order class number is positive. -/
theorem binaryClassGroup_card_pos (K : PositiveDefiniteIntegralLattice 2) :
    letI := K.binaryDiscriminantOrder_isDomain
    0<Nat.card (ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant)) := by
  letI := K.binaryDiscriminantOrder_isDomain
  letI := K.finite_binaryClassGroup
  exact Nat.card_pos

/-- The actual finite square-class quotient classifies the original genus
at fixed original content and primitive discriminant. -/
theorem binaryClassSquareQuotient_eq_iff_isSameGenus (K L : PositiveDefiniteIntegralLattice 2)
    (hg : L.binaryContent=K.binaryContent)
    (hD : L.binaryPrimitiveDiscriminant=K.binaryPrimitiveDiscriminant) :
    letI := K.binaryDiscriminantOrder_isDomain
    let H := (powMonoidHom 2 : ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant) →*
      ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant)).range
    QuotientGroup.mk' H (L.binaryIdealClassAt K.binaryPrimitiveDiscriminant hD)=
      QuotientGroup.mk' H (K.binaryIdealClassAt K.binaryPrimitiveDiscriminant rfl) ↔ K.IsSameGenus L := by
  letI := K.binaryDiscriminantOrder_isDomain
  simp only [QuotientGroup.mk'_apply]
  rw [QuotientGroup.eq_iff_div_mem,div_eq_mul_inv,← K.binaryIdealLocalNormKernel_eq_squares]
  exact (K.isSameGenus_iff_binaryIdealLocalNormKernel_mem L hg hD).symm

/-- Every actual square-quotient class is realized at the original content
and primitive discriminant. No new genus or caller certificate is used. -/
theorem exists_lattice_of_binaryClassSquareQuotient (K : PositiveDefiniteIntegralLattice 2)
    (q : letI := K.binaryDiscriminantOrder_isDomain
      ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant) ⧸
        (powMonoidHom 2 : ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant) →*
          ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant)).range) :
    letI := K.binaryDiscriminantOrder_isDomain
    ∃ L : PositiveDefiniteIntegralLattice 2, L.binaryContent=K.binaryContent ∧
      ∃ hD : L.binaryPrimitiveDiscriminant=K.binaryPrimitiveDiscriminant,
        QuotientGroup.mk' (powMonoidHom 2 : ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant) →*
          ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant)).range
          (L.binaryIdealClassAt K.binaryPrimitiveDiscriminant hD)=q := by
  letI := K.binaryDiscriminantOrder_isDomain
  obtain ⟨xi,hxi⟩ := QuotientGroup.mk'_surjective
    (powMonoidHom 2 : ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant) →*
      ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant)).range q
  obtain ⟨L,hg,hD,hclass⟩ := K.exists_lattice_of_binaryIdealClass xi
  exact ⟨L,hg,hD,by rw [hclass]; exact hxi⟩

/-- The canonical genus quotient is finite by the proved entire class-group
finiteness, not merely by finite square-subgroup cardinality. -/
theorem finite_binaryClassSquareQuotient (K : PositiveDefiniteIntegralLattice 2) :
    letI := K.binaryDiscriminantOrder_isDomain
    Finite (ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant) ⧸
      (powMonoidHom 2 : ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant) →*
        ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant)).range) := by
  letI := K.binaryDiscriminantOrder_isDomain
  letI := K.finite_binaryClassGroup
  infer_instance

/-- The actual square-class quotient has a positive cardinality. -/
theorem binaryClassSquareQuotient_card_pos (K : PositiveDefiniteIntegralLattice 2) :
    letI := K.binaryDiscriminantOrder_isDomain
    0<Nat.card (ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant) ⧸
      (powMonoidHom 2 : ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant) →*
        ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant)).range) := by
  letI := K.binaryDiscriminantOrder_isDomain
  letI := K.finite_binaryClassSquareQuotient
  exact Nat.card_pos

/-- The class number is the actual genus-quotient count times the original
proper-genus count. No numerical class-number formula is assumed. -/
theorem binaryClassGroup_card_eq_genusQuotient_mul_properGenus (K : PositiveDefiniteIntegralLattice 2) :
    letI := K.binaryDiscriminantOrder_isDomain
    Nat.card (ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant))=
      Nat.card (ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant) ⧸
        (powMonoidHom 2 : ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant) →*
          ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant)).range)*
        Fintype.card K.properGenus := by
  letI := K.binaryDiscriminantOrder_isDomain
  rw [← K.card_binaryIdealClassSquares]
  exact Subgroup.card_eq_card_quotient_mul_card_subgroup _

/-- The original ordinary full-O mass is h(O)/(2*w_D*g(O)), with the actual
finite canonical class number and actual genus quotient. This does not
identify h(O) with an analytic L-value or compute g(O) numerically. -/
theorem ordinaryGenusMass_eq_classNumber_div_two_normOneUnits_genusQuotient
    (K : PositiveDefiniteIntegralLattice 2) :
    letI := K.binaryDiscriminantOrder_isDomain
    K.ordinaryGenusMass=
      (Nat.card (ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant)) : ℚ)/
        (2*(Nat.card (DiscriminantNormOneUnits K.binaryPrimitiveDiscriminant) : ℚ)*
          (Nat.card (ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant) ⧸
            (powMonoidHom 2 : ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant) →*
              ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant)).range) : ℚ)) := by
  letI := K.binaryDiscriminantOrder_isDomain
  have hq : (Nat.card (ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant) ⧸
      (powMonoidHom 2 : ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant) →*
        ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant)).range) : ℚ) ≠ 0 := by
    exact_mod_cast (ne_of_gt K.binaryClassSquareQuotient_card_pos)
  have he (s q a h : ℚ) (hq : q ≠ 0) (hc : h=q*s) : s/a=h/(a*q) := by
    rw [hc,mul_comm q s]
    exact (mul_div_mul_right s a hq).symm
  rw [K.ordinaryGenusMass_eq_card_properGenus_div_two_discriminantNormOneUnits]
  apply he _ _ _ _ hq
  exact_mod_cast K.binaryClassGroup_card_eq_genusQuotient_mul_properGenus

/-- The actual finite genus-quotient count equals the actual class-group
2-torsion count, by the square homomorphism's first isomorphism theorem.
This is not a numerical conductor or discriminant formula for that count. -/
theorem binaryClassSquareQuotient_card_eq_twoTorsion (K : PositiveDefiniteIntegralLattice 2) :
    letI := K.binaryDiscriminantOrder_isDomain
    Nat.card (ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant) ⧸
      (powMonoidHom 2 : ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant) →*
        ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant)).range)=
      Nat.card (powMonoidHom 2 : ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant) →*
        ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant)).ker := by
  letI := K.binaryDiscriminantOrder_isDomain
  letI := K.finite_binaryClassGroup
  let G := ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant)
  let f : G →* G := powMonoidHom 2
  have he : Nat.card (G ⧸ f.ker)=Nat.card f.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
  have hker := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  rw [he] at hker
  have hrange := Subgroup.card_eq_card_quotient_mul_card_subgroup f.range
  have hpos : 0<Nat.card f.range := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_right hpos
  calc
    Nat.card (G ⧸ f.range)*Nat.card f.range=Nat.card G := hrange.symm
    _=Nat.card f.range*Nat.card f.ker := hker
    _=Nat.card f.ker*Nat.card f.range := mul_comm _ _

/-- The same original mass count can be written using actual class-group
2-torsion: h(O)/(2*w_D*#H[2]). Analytic/density evaluation remains separate. -/
theorem ordinaryGenusMass_eq_classNumber_div_two_normOneUnits_twoTorsion
    (K : PositiveDefiniteIntegralLattice 2) :
    letI := K.binaryDiscriminantOrder_isDomain
    K.ordinaryGenusMass=
      (Nat.card (ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant)) : ℚ)/
        (2*(Nat.card (DiscriminantNormOneUnits K.binaryPrimitiveDiscriminant) : ℚ)*
          (Nat.card (powMonoidHom 2 : ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant) →*
            ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant)).ker : ℚ)) := by
  letI := K.binaryDiscriminantOrder_isDomain
  rw [K.ordinaryGenusMass_eq_classNumber_div_two_normOneUnits_genusQuotient,
    K.binaryClassSquareQuotient_card_eq_twoTorsion]

end PositiveDefiniteIntegralLattice

#assert_standard_axioms PositiveDefiniteIntegralLattice.fixed_rank_pairingDeterminant_proper_isometry_classes_finite
#assert_standard_axioms PositiveDefiniteIntegralLattice.pairingDeterminant_eq_of_binaryContent_discriminant
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryIdealClassLattice_properGlobalIsometryClass_injective
#assert_standard_axioms PositiveDefiniteIntegralLattice.finite_binaryClassGroup
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryClassGroup_card_pos
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryClassSquareQuotient_eq_iff_isSameGenus
#assert_standard_axioms PositiveDefiniteIntegralLattice.exists_lattice_of_binaryClassSquareQuotient
#assert_standard_axioms PositiveDefiniteIntegralLattice.finite_binaryClassSquareQuotient
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryClassSquareQuotient_card_pos
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryClassGroup_card_eq_genusQuotient_mul_properGenus
#assert_standard_axioms PositiveDefiniteIntegralLattice.ordinaryGenusMass_eq_classNumber_div_two_normOneUnits_genusQuotient
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryClassSquareQuotient_card_eq_twoTorsion
#assert_standard_axioms PositiveDefiniteIntegralLattice.ordinaryGenusMass_eq_classNumber_div_two_normOneUnits_twoTorsion
