import SMSFormula.Applications.Unimodular.TypeIIdentityMass
import SMSFormula.Applications.Unimodular.GenusClassification
import SMSFormula.StandardAxiomsGuard

/-!
# Total Type I class mass and proved single-genus classification

This module packages the finite sum over all global isometry classes of
classically unimodular Type I lattices in a fixed rank.  It is a genuine class
sum, not a new definition of ordinary genus mass by the desired Bernoulli
constant.  Transport interfaces taking a classification as a hypothesis are
provided, and the Bernoulli endpoints use the identity-genus classifier proved
in `GenusClassification`.
-/

noncomputable section

open scoped BigOperators
open UnimodularMass

namespace PositiveDefiniteIntegralLattice

/-- Global isometry classes represented by classically unimodular Type I
lattices of rank `n`.  This is a finite subtype of the fixed-`pairingDeterminant = 1`
class set. -/
abbrev UnimodularTypeIIsometryClass (n : ℕ) :=
  { C : Set (PositiveDefiniteIntegralLattice n) //
    ∃ L : PositiveDefiniteIntegralLattice n,
      L.IsUnimodular ∧ L.HasOddNorm ∧ C = L.globalIsometryClass }

noncomputable instance unimodularTypeIIsometryClass_fintype (n : ℕ) :
    Fintype (UnimodularTypeIIsometryClass n) := by
  classical
  let S : Set (Set (PositiveDefiniteIntegralLattice n)) :=
    { C | ∃ L : PositiveDefiniteIntegralLattice n,
      L.IsUnimodular ∧ L.HasOddNorm ∧ C = L.globalIsometryClass }
  have hS : S.Finite := by
    refine Set.Finite.subset
      (fixed_rank_pairingDeterminant_isometry_classes_finite (n := n) (d := 1)) ?_
    intro C hC
    rcases hC with ⟨L, hU, _hI, hC⟩
    exact ⟨L, hU, hC⟩
  change Fintype { C : Set (PositiveDefiniteIntegralLattice n) // C ∈ S }
  exact hS.fintype

/-- A chosen representative of a Type I unimodular global isometry class. -/
def typeIClassRepresentative {n : ℕ} (C : UnimodularTypeIIsometryClass n) :
    PositiveDefiniteIntegralLattice n :=
  Classical.choose C.property

lemma typeIClassRepresentative_spec {n : ℕ} (C : UnimodularTypeIIsometryClass n) :
    (typeIClassRepresentative C).IsUnimodular ∧
      (typeIClassRepresentative C).HasOddNorm ∧
        C.1 = (typeIClassRepresentative C).globalIsometryClass :=
  Classical.choose_spec C.property

lemma typeIClassRepresentative_isUnimodular {n : ℕ}
    (C : UnimodularTypeIIsometryClass n) :
    (typeIClassRepresentative C).IsUnimodular :=
  (typeIClassRepresentative_spec C).1

lemma typeIClassRepresentative_hasOddNorm {n : ℕ}
    (C : UnimodularTypeIIsometryClass n) :
    (typeIClassRepresentative C).HasOddNorm :=
  (typeIClassRepresentative_spec C).2.1

lemma typeIClassRepresentative_globalIsometryClass {n : ℕ}
    (C : UnimodularTypeIIsometryClass n) :
    C.1 = (typeIClassRepresentative C).globalIsometryClass :=
  (typeIClassRepresentative_spec C).2.2

/-- The actual total Type I class mass in rank `n`, summed over all global
isometry classes represented by classically unimodular Type I lattices. -/
def totalTypeIClassMass (n : ℕ) : ℚ :=
  ∑ C : UnimodularTypeIIsometryClass n,
    ((Fintype.card (typeIClassRepresentative C).IsometryGroup : ℚ)⁻¹)

/-- There are no rank-zero Type I classes, so the total Type I class mass is
zero in rank zero. -/
theorem totalTypeIClassMass_zero : totalTypeIClassMass 0 = 0 := by
  classical
  unfold totalTypeIClassMass
  refine Finset.sum_eq_zero ?_
  intro C _hC
  exfalso
  exact not_hasOddNorm_rank_zero (typeIClassRepresentative C)
    (typeIClassRepresentative_hasOddNorm C)

/-- Under a supplied single-genus classification of all Type I unimodular
lattices in positive rank `n`, Type I global classes are exactly the ordinary
classes in the identity genus. -/
def typeIClassEquivIdentityGenus_of_classification {n : ℕ} (hn : 0 < n)
    (hclass : ∀ L : PositiveDefiniteIntegralLattice n, L.IsUnimodular → L.HasOddNorm →
      L.IsSameGenus (identityLattice n)) :
    UnimodularTypeIIsometryClass n ≃ (identityLattice n).genus where
  toFun C := by
    refine ⟨C.1, ?_⟩
    refine ⟨typeIClassRepresentative C, ?_, typeIClassRepresentative_globalIsometryClass C⟩
    exact isSameGenus_symm
      (hclass (typeIClassRepresentative C)
        (typeIClassRepresentative_isUnimodular C)
        (typeIClassRepresentative_hasOddNorm C))
  invFun A := by
    let M := genusClassRepresentative (identityLattice n) A
    refine ⟨A.1, ?_⟩
    have hM : (identityLattice n).IsSameGenus M :=
      genusClassRepresentative_isSameGenus (identityLattice n) A
    have hA : A.1 = M.globalIsometryClass :=
      genusClassRepresentative_globalIsometryClass (identityLattice n) A
    have hsym : M.IsSameGenus (identityLattice n) := isSameGenus_symm hM
    have hU : M.IsUnimodular :=
      M.isUnimodular_of_isSameGenus hsym (identityLattice_isUnimodular n)
    have hI : M.HasOddNorm :=
      hasOddNorm_of_isSameGenus hsym (identityLattice_hasOddNorm hn)
    exact ⟨M, hU, hI, hA⟩
  left_inv C := by
    apply Subtype.ext
    rfl
  right_inv A := by
    apply Subtype.ext
    rfl

/-- If all Type I unimodular lattices in positive rank `n` are supplied to be in
identity genus, then the total Type I class mass is the ordinary genus mass of
the identity lattice. -/
theorem totalTypeIClassMass_eq_identity_ordinaryGenusMass_of_classification
    {n : ℕ} (hn : 0 < n)
    (hclass : ∀ L : PositiveDefiniteIntegralLattice n, L.IsUnimodular → L.HasOddNorm →
      L.IsSameGenus (identityLattice n)) :
    totalTypeIClassMass n = (identityLattice n).ordinaryGenusMass := by
  classical
  let e := typeIClassEquivIdentityGenus_of_classification hn hclass
  unfold totalTypeIClassMass ordinaryGenusMass
  refine Fintype.sum_equiv e _ _ ?_
  intro C
  apply ordinaryGenusMass_summand_eq_of_isGlobalIsometry
  have hmem : genusClassRepresentative (identityLattice n) (e C) ∈ C.1 := by
    change genusClassRepresentative (identityLattice n) (e C) ∈ (e C).1
    rw [genusClassRepresentative_globalIsometryClass]
    exact mem_globalIsometryClass_self _
  rw [typeIClassRepresentative_globalIsometryClass C] at hmem
  exact hmem

/-- All-rank total Type I class mass under the same explicit higher-rank
identity-genus classification hypothesis as the ordinary-genus Type I theorems.
Ranks one and two use the closed low-rank classifications; rank zero is empty. -/
theorem totalTypeIClassMass_eq_typeIConstant_of_typeI_sameGenus_identityLattice_classification_allRank
    {n : ℕ}
    (hclass : 3 ≤ n → ∀ L : PositiveDefiniteIntegralLattice n, L.IsUnimodular →
      L.HasOddNorm → L.IsSameGenus (identityLattice n)) :
    totalTypeIClassMass n = typeIConstant n := by
  by_cases hn0 : n = 0
  · subst n
    rw [totalTypeIClassMass_zero, typeIConstant_zero]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    have hclass_all : ∀ L : PositiveDefiniteIntegralLattice n, L.IsUnimodular →
        L.HasOddNorm → L.IsSameGenus (identityLattice n) := by
      intro L hU hI
      by_cases hn1 : n = 1
      · subst n
        exact isSameGenus_of_isGlobalIsometry
          (isGlobalIsometry_identityLattice_one_of_isUnimodular L hU)
      by_cases hn2 : n = 2
      · subst n
        exact isSameGenus_of_isGlobalIsometry
          (isGlobalIsometry_identityLattice_two_of_isUnimodular L hU)
      have hn3 : 3 ≤ n := by omega
      exact hclass hn3 L hU hI
    exact
      (totalTypeIClassMass_eq_identity_ordinaryGenusMass_of_classification
        hnpos hclass_all).trans
        (ordinaryGenusMass_eq_typeIConstant_of_typeI_sameGenus_identityLattice_classification_allRank
          hclass (identityLattice n) (identityLattice_isUnimodular n)
          (identityLattice_hasOddNorm hnpos))

/-- Real-valued form of the all-rank total Type I class-mass theorem under the
same explicit higher-rank identity-genus classification hypothesis. -/
theorem totalTypeIClassMass_real_eq_typeIConstant_of_typeI_sameGenus_identityLattice_classification_allRank
    {n : ℕ}
    (hclass : 3 ≤ n → ∀ L : PositiveDefiniteIntegralLattice n, L.IsUnimodular →
      L.HasOddNorm → L.IsSameGenus (identityLattice n)) :
    ((totalTypeIClassMass n : ℚ) : ℝ) = (typeIConstant n : ℝ) := by
  exact_mod_cast
    totalTypeIClassMass_eq_typeIConstant_of_typeI_sameGenus_identityLattice_classification_allRank
      hclass

/-- Total Type I class mass in every rank, using the proved identity-genus
classifier rather than a supplied classification premise. -/
theorem totalTypeIClassMass_eq_typeIConstant
    {n : ℕ} :
    totalTypeIClassMass n = typeIConstant n :=
  totalTypeIClassMass_eq_typeIConstant_of_typeI_sameGenus_identityLattice_classification_allRank
    (fun _ L hU hI => isSameGenus_identity_of_typeIUnimodular L hU hI)

/-- Real-valued total Type I class mass without a supplied classifier. -/
theorem totalTypeIClassMass_real_eq_typeIConstant
    {n : ℕ} :
    ((totalTypeIClassMass n : ℚ) : ℝ) = (typeIConstant n : ℝ) := by
  exact_mod_cast totalTypeIClassMass_eq_typeIConstant (n := n)

#assert_standard_axioms totalTypeIClassMass_zero
#assert_standard_axioms typeIClassEquivIdentityGenus_of_classification
#assert_standard_axioms totalTypeIClassMass_eq_identity_ordinaryGenusMass_of_classification
#assert_standard_axioms totalTypeIClassMass_eq_typeIConstant_of_typeI_sameGenus_identityLattice_classification_allRank
#assert_standard_axioms totalTypeIClassMass_real_eq_typeIConstant_of_typeI_sameGenus_identityLattice_classification_allRank
#assert_standard_axioms totalTypeIClassMass_eq_typeIConstant
#assert_standard_axioms totalTypeIClassMass_real_eq_typeIConstant

end PositiveDefiniteIntegralLattice

end
