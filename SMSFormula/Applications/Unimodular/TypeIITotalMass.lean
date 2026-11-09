import SMSFormula.Applications.Unimodular.TypeIIDirectHMass
import SMSFormula.Applications.Unimodular.GenusClassification
import SMSFormula.StandardAxiomsGuard

/-!
# Total Type II class mass and the rank obstruction

This module defines the finite sum over all global isometry classes of
classically unimodular Type II lattices in a fixed rank.  The inadmissible-rank
zero result uses the Type II rank obstruction.  The positive admissible-rank
comparison with a Bernoulli constant uses the single-genus classifier into
`typeIISeed k`.  Versions taking a classification as a hypothesis are also
provided; classification is not inferred from local factors.
-/

noncomputable section

open scoped BigOperators
open UnimodularMass

namespace PositiveDefiniteIntegralLattice

/-- Global isometry classes represented by classically unimodular Type II
lattices of rank `n`. -/
abbrev UnimodularTypeIIIsometryClass (n : ℕ) :=
  { C : Set (PositiveDefiniteIntegralLattice n) //
    ∃ L : PositiveDefiniteIntegralLattice n,
      L.IsUnimodular ∧ L.HasEvenNorms ∧ C = L.globalIsometryClass }

noncomputable instance unimodularTypeIIIsometryClass_fintype (n : ℕ) :
    Fintype (UnimodularTypeIIIsometryClass n) := by
  classical
  let S : Set (Set (PositiveDefiniteIntegralLattice n)) :=
    { C | ∃ L : PositiveDefiniteIntegralLattice n,
      L.IsUnimodular ∧ L.HasEvenNorms ∧ C = L.globalIsometryClass }
  have hS : S.Finite := by
    refine Set.Finite.subset
      (fixed_rank_pairingDeterminant_isometry_classes_finite (n := n) (d := 1)) ?_
    intro C hC
    rcases hC with ⟨L, hU, _hII, hC⟩
    exact ⟨L, hU, hC⟩
  change Fintype { C : Set (PositiveDefiniteIntegralLattice n) // C ∈ S }
  exact hS.fintype

/-- A chosen representative of a Type II unimodular global isometry class. -/
def typeIIClassRepresentative {n : ℕ} (C : UnimodularTypeIIIsometryClass n) :
    PositiveDefiniteIntegralLattice n :=
  Classical.choose C.property

lemma typeIIClassRepresentative_spec {n : ℕ} (C : UnimodularTypeIIIsometryClass n) :
    (typeIIClassRepresentative C).IsUnimodular ∧
      (typeIIClassRepresentative C).HasEvenNorms ∧
        C.1 = (typeIIClassRepresentative C).globalIsometryClass :=
  Classical.choose_spec C.property

lemma typeIIClassRepresentative_isUnimodular {n : ℕ}
    (C : UnimodularTypeIIIsometryClass n) :
    (typeIIClassRepresentative C).IsUnimodular :=
  (typeIIClassRepresentative_spec C).1

lemma typeIIClassRepresentative_hasEvenNorms {n : ℕ}
    (C : UnimodularTypeIIIsometryClass n) :
    (typeIIClassRepresentative C).HasEvenNorms :=
  (typeIIClassRepresentative_spec C).2.1

lemma typeIIClassRepresentative_globalIsometryClass {n : ℕ}
    (C : UnimodularTypeIIIsometryClass n) :
    C.1 = (typeIIClassRepresentative C).globalIsometryClass :=
  (typeIIClassRepresentative_spec C).2.2

/-- The actual total Type II class mass in rank `n`, summed over all global
isometry classes represented by classically unimodular Type II lattices. -/
def totalTypeIIClassMass (n : ℕ) : ℚ :=
  ∑ C : UnimodularTypeIIIsometryClass n,
    ((Fintype.card (typeIIClassRepresentative C).IsometryGroup : ℚ)⁻¹)

/-- Under a supplied single-genus classification of all Type II unimodular
lattices into a seed genus, Type II global classes are exactly the ordinary
classes in that seed genus. -/
def typeIIClassEquivGenus_of_classification {n : ℕ} (S : PositiveDefiniteIntegralLattice n)
    (hSU : S.IsUnimodular) (hSII : S.HasEvenNorms)
    (hclass : ∀ L : PositiveDefiniteIntegralLattice n, L.IsUnimodular → L.HasEvenNorms →
      L.IsSameGenus S) :
    UnimodularTypeIIIsometryClass n ≃ S.genus where
  toFun C := by
    refine ⟨C.1, ?_⟩
    refine ⟨typeIIClassRepresentative C, ?_, typeIIClassRepresentative_globalIsometryClass C⟩
    exact isSameGenus_symm
      (hclass (typeIIClassRepresentative C)
        (typeIIClassRepresentative_isUnimodular C)
        (typeIIClassRepresentative_hasEvenNorms C))
  invFun A := by
    let M := genusClassRepresentative S A
    refine ⟨A.1, ?_⟩
    have hM : S.IsSameGenus M := genusClassRepresentative_isSameGenus S A
    have hA : A.1 = M.globalIsometryClass := genusClassRepresentative_globalIsometryClass S A
    have hsym : M.IsSameGenus S := isSameGenus_symm hM
    have hU : M.IsUnimodular := M.isUnimodular_of_isSameGenus hsym hSU
    have hII : M.HasEvenNorms := hasEvenNorms_of_isSameGenus hsym hSII
    exact ⟨M, hU, hII, hA⟩
  left_inv C := by
    apply Subtype.ext
    rfl
  right_inv A := by
    apply Subtype.ext
    rfl

/-- If all Type II unimodular lattices in rank `n` are supplied to be in the
genus of a seed `S`, then the total Type II class mass is the ordinary genus
mass of `S`. -/
theorem totalTypeIIClassMass_eq_ordinaryGenusMass_of_classification
    {n : ℕ} (S : PositiveDefiniteIntegralLattice n)
    (hSU : S.IsUnimodular) (hSII : S.HasEvenNorms)
    (hclass : ∀ L : PositiveDefiniteIntegralLattice n, L.IsUnimodular → L.HasEvenNorms →
      L.IsSameGenus S) :
    totalTypeIIClassMass n = S.ordinaryGenusMass := by
  classical
  let e := typeIIClassEquivGenus_of_classification S hSU hSII hclass
  unfold totalTypeIIClassMass ordinaryGenusMass
  refine Fintype.sum_equiv e _ _ ?_
  intro C
  apply ordinaryGenusMass_summand_eq_of_isGlobalIsometry
  have hmem : genusClassRepresentative S (e C) ∈ C.1 := by
    change genusClassRepresentative S (e C) ∈ (e C).1
    rw [genusClassRepresentative_globalIsometryClass]
    exact mem_globalIsometryClass_self _
  rw [typeIIClassRepresentative_globalIsometryClass C] at hmem
  exact hmem

/-- The rank-zero Type II total class mass is one, equivalently the rank-zero
Type II Bernoulli constant. -/
theorem totalTypeIIClassMass_zero : totalTypeIIClassMass 0 = typeIIConstant 0 := by
  exact
    (totalTypeIIClassMass_eq_ordinaryGenusMass_of_classification
      (identityLattice 0) (identityLattice_isUnimodular 0)
      identityLattice_zero_hasEvenNorms
      (fun L _hU _hII => isSameGenus_of_isGlobalIsometry
        (isGlobalIsometry_identityLattice_zero L))).trans
      identityLattice_zero_ordinaryGenusMass_eq_typeIIConstant

/-- In a rank not divisible by eight there are no Type II unimodular classes,
so the total Type II class mass is zero. -/
theorem totalTypeIIClassMass_eq_zero_of_not_dvd_eight
    {n : ℕ} (h8 : ¬ 8 ∣ n) :
    totalTypeIIClassMass n = 0 := by
  classical
  unfold totalTypeIIClassMass
  refine Finset.sum_eq_zero ?_
  intro C _hC
  exfalso
  exact h8 (eight_dvd_rank_of_isUnimodular_isTypeII
    (typeIIClassRepresentative C)
    (typeIIClassRepresentative_isUnimodular C)
    (typeIIClassRepresentative_hasEvenNorms C))

/-- Positive inadmissible-rank total Type II class mass, written against the
zero branch of the Type II Bernoulli constant. -/
theorem totalTypeIIClassMass_eq_typeIIConstant_of_pos_not_dvd_eight
    {n : ℕ} (hn : 0 < n) (h8 : ¬ 8 ∣ n) :
    totalTypeIIClassMass n = typeIIConstant n := by
  rw [totalTypeIIClassMass_eq_zero_of_not_dvd_eight h8,
    typeIIConstant_eq_zero_of_pos_not_dvd_eight hn h8]

/-- If all Type II unimodular lattices in rank `8*k` are supplied to lie in the
checked seed genus, then the total Type II class mass is the Type II Bernoulli
constant.  This is a total-class transport statement; it does not prove the
single-genus classification hypothesis. -/
theorem totalTypeIIClassMass_eq_typeIIConstant_of_typeIISeed_classification
    (k : ℕ) (hk : 0 < k)
    (hclass : ∀ L : PositiveDefiniteIntegralLattice (8 * k), L.IsUnimodular →
      L.HasEvenNorms → L.IsSameGenus (typeIISeed k)) :
    totalTypeIIClassMass (8 * k) = typeIIConstant (8 * k) := by
  exact
    (totalTypeIIClassMass_eq_ordinaryGenusMass_of_classification
      (typeIISeed k) (typeIISeed_isUnimodular k) (typeIISeed_hasEvenNorms k)
      hclass).trans
      (ordinaryGenusMass_eq_typeIIConstant_of_typeIIUnimodular_directH
        k hk (typeIISeed k) (typeIISeed_isUnimodular k) (typeIISeed_hasEvenNorms k))

/-- Real-valued form of the positive inadmissible-rank total Type II class mass endpoint. -/
theorem totalTypeIIClassMass_real_eq_typeIIConstant_of_pos_not_dvd_eight
    {n : ℕ} (hn : 0 < n) (h8 : ¬ 8 ∣ n) :
    ((totalTypeIIClassMass n : ℚ) : ℝ) = (typeIIConstant n : ℝ) := by
  exact_mod_cast totalTypeIIClassMass_eq_typeIIConstant_of_pos_not_dvd_eight hn h8

/-- Real-valued form of the supplied-classification positive admissible-rank
Type II total class-mass theorem. -/
theorem totalTypeIIClassMass_real_eq_typeIIConstant_of_typeIISeed_classification
    (k : ℕ) (hk : 0 < k)
    (hclass : ∀ L : PositiveDefiniteIntegralLattice (8 * k), L.IsUnimodular →
      L.HasEvenNorms → L.IsSameGenus (typeIISeed k)) :
    ((totalTypeIIClassMass (8 * k) : ℚ) : ℝ) = (typeIIConstant (8 * k) : ℝ) := by
  exact_mod_cast totalTypeIIClassMass_eq_typeIIConstant_of_typeIISeed_classification k hk hclass

/-- All-rank Type II total class mass, with the positive admissible-rank
classification discharged by actual local isometries at every place. -/
theorem totalTypeIIClassMass_eq_typeIIConstant
    (n : ℕ) :
    totalTypeIIClassMass n = typeIIConstant n := by
  by_cases hn0 : n = 0
  · subst n
    exact totalTypeIIClassMass_zero
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
  by_cases h8 : 8 ∣ n
  · rcases h8 with ⟨k, rfl⟩
    have hkpos : 0 < k := by
      cases k with
      | zero => norm_num at hnpos
      | succ k => exact Nat.succ_pos k
    exact totalTypeIIClassMass_eq_typeIIConstant_of_typeIISeed_classification
      k hkpos (fun L hU hII => isSameGenus_typeIISeed_of_typeIIUnimodular k hkpos L hU hII)
  · exact totalTypeIIClassMass_eq_typeIIConstant_of_pos_not_dvd_eight hnpos h8

/-- Real-valued all-rank Type II total class mass without a supplied classifier. -/
theorem totalTypeIIClassMass_real_eq_typeIIConstant
    (n : ℕ) :
    ((totalTypeIIClassMass n : ℚ) : ℝ) = (typeIIConstant n : ℝ) := by
  exact_mod_cast totalTypeIIClassMass_eq_typeIIConstant n

#assert_standard_axioms typeIIClassEquivGenus_of_classification
#assert_standard_axioms totalTypeIIClassMass_eq_ordinaryGenusMass_of_classification
#assert_standard_axioms totalTypeIIClassMass_zero
#assert_standard_axioms totalTypeIIClassMass_eq_zero_of_not_dvd_eight
#assert_standard_axioms totalTypeIIClassMass_eq_typeIIConstant_of_pos_not_dvd_eight
#assert_standard_axioms totalTypeIIClassMass_eq_typeIIConstant_of_typeIISeed_classification
#assert_standard_axioms totalTypeIIClassMass_real_eq_typeIIConstant_of_pos_not_dvd_eight
#assert_standard_axioms totalTypeIIClassMass_real_eq_typeIIConstant_of_typeIISeed_classification
#assert_standard_axioms totalTypeIIClassMass_eq_typeIIConstant
#assert_standard_axioms totalTypeIIClassMass_real_eq_typeIIConstant

end PositiveDefiniteIntegralLattice

end
