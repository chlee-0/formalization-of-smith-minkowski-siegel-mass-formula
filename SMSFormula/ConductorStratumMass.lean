import SMSFormula.ExactConductorExistence

/-!
# The mass of a conductor stratum is `phi(m)`

The exact-conductor-`m` frequencies are the primitive fractions with coprime numerator modulo the
integral finite adeles, indexed by the units of `ZMod m` (`ExactConductorExistence`).  This file
computes the mass of that stratum.

A class has unit mass, and that is translation invariance and nothing else: the class of `t` is the
translate `(-t + .)^{-1}` of the integral finite adeles, whose mass is one because the repository's
own Haar measure is normalised at exactly that compact open set.

The stratum is the disjoint union of `phi(m)` classes.  The union is over the units of `ZMod m`,
each contributing the class of `a/m` at mathlib's canonical `ZMod.val`; no representative is chosen,
since two numerators with the same residue give the same class -- already proved -- so the indexed
sets depend only on the unit.  Disjointness is that same fact read backwards: a common point forces
the residues equal, hence the units equal.

Hence the mass is exactly `phi(m)`, mathlib's own count of the units.

Negative scope.  This is the mass of a stratum of frequencies.  It is not a statement about the
local integral, and nothing here identifies that integral with the finite factor of the repository's
adelic Bruhat coefficient; that is `FiniteFactorIdentification`.  No Gauss sum is evaluated.
-/

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

open MeasureTheory SMSFormula.QuadraticPhaseDescent
open scoped ENNReal

/-! ## A class has unit mass -/

/-- The class of `t` is measurable, being a translate of an open set. -/
theorem measurableSet_congruenceClass (t : RationalFiniteAdele) :
    MeasurableSet {s : RationalFiniteAdele | s - t ∈ integralFiniteAdeleSubring} := by
  rw [show {s : RationalFiniteAdele | s - t ∈ integralFiniteAdeleSubring} =
    (fun x => -t + x) ⁻¹' (integralFiniteAdeleSubring : Set RationalFiniteAdele) by
      ext s; simp [sub_eq_neg_add, add_comm]]
  exact (measurable_const_add _) isOpen_integralFiniteAdeleSubring.measurableSet

/-- And it has mass one -- translation invariance, the repository's Haar being normalised exactly at
the integral finite adeles. -/
theorem measure_congruenceClass_eq_one (t : RationalFiniteAdele) :
    rationalFiniteAdeleAddHaarMeasure
      {s : RationalFiniteAdele | s - t ∈ integralFiniteAdeleSubring} = 1 := by
  rw [show {s : RationalFiniteAdele | s - t ∈ integralFiniteAdeleSubring} =
    (fun x => -t + x) ⁻¹' (integralFiniteAdeleSubring : Set RationalFiniteAdele) by
      ext s; simp [sub_eq_neg_add, add_comm]]
  rw [measure_preimage_add]
  exact rationalFiniteAdeleAddHaarMeasure_integral

/-! ## The numerators of the units -/

/-- A unit's canonical numerator is coprime to the conductor. -/
theorem isCoprime_unitVal (m : ℕ) [NeZero m] (a : (ZMod m)ˣ) :
    IsCoprime (((a : ZMod m).val : ℕ) : ℤ) (m : ℤ) := by
  rw [Nat.isCoprime_iff_coprime, ← ZMod.isUnit_iff_coprime,
    show (((a : ZMod m).val : ℕ) : ZMod m) = (a : ZMod m) by simp [ZMod.natCast_val, ZMod.cast_id]]
  exact a.isUnit

/-- Its residue is the unit itself. -/
theorem intCast_unitVal (m : ℕ) [NeZero m] (a : (ZMod m)ˣ) :
    ((((a : ZMod m).val : ℕ) : ℤ) : ZMod m) = (a : ZMod m) := by
  push_cast
  simp [ZMod.natCast_val, ZMod.cast_id]

/-! ## The stratum is a disjoint union of classes -/

/-- The exact-conductor-`m` stratum is the union of the classes of the primitive fractions with unit
numerator.  The indexing uses mathlib's canonical `ZMod.val`, and no representative is chosen: two
numerators with the same residue give the same class. -/
theorem exactConductor_eq_iUnion (m : ℕ) [NeZero m] :
    {t : RationalFiniteAdele |
        t * (m : RationalFiniteAdele) ∈ integralFiniteAdeleSubring ∧ HasExactConductor t m} =
      ⋃ a : (ZMod m)ˣ,
        {s : RationalFiniteAdele |
          s - primitiveFrequency (((a : ZMod m).val : ℕ) : ℤ) m ∈ integralFiniteAdeleSubring} := by
  have hm : m ≠ 0 := NeZero.ne m
  ext t
  simp only [Set.mem_setOf_eq, Set.mem_iUnion]
  constructor
  · intro ht
    obtain ⟨z, hcop, hz⟩ := (hasExactConductor_iff_congr_primitiveFrequency t m hm).1 ht
    refine ⟨ZMod.unitOfIsCoprime z hcop, ?_⟩
    have hres : ((z : ℤ) : ZMod m) =
        ((((ZMod.unitOfIsCoprime z hcop : (ZMod m)ˣ) : ZMod m).val : ℕ) : ℤ) := by
      rw [show ((((((ZMod.unitOfIsCoprime z hcop : (ZMod m)ˣ) : ZMod m).val : ℕ) : ℤ)) : ZMod m) =
        ((ZMod.unitOfIsCoprime z hcop : (ZMod m)ˣ) : ZMod m) from
          intCast_unitVal m (ZMod.unitOfIsCoprime z hcop)]
      rfl
    have hshift : primitiveFrequency z m -
        primitiveFrequency ((((ZMod.unitOfIsCoprime z hcop : (ZMod m)ˣ) : ZMod m).val : ℕ) : ℤ) m ∈
        integralFiniteAdeleSubring :=
      (primitiveFrequency_sub_mem_integral_iff _ _ m hm).2 hres
    have := Subring.add_mem _ hz hshift
    simpa using this
  · rintro ⟨a, ha⟩
    exact (hasExactConductor_iff_congr_primitiveFrequency t m hm).2
      ⟨_, isCoprime_unitVal m a, ha⟩

/-- The classes are pairwise disjoint: a common point forces the residues equal, hence the units. -/
theorem pairwiseDisjoint_unitClasses (m : ℕ) [NeZero m] :
    (↑(Finset.univ : Finset (ZMod m)ˣ) : Set (ZMod m)ˣ).PairwiseDisjoint
      (fun a : (ZMod m)ˣ =>
        {s : RationalFiniteAdele |
          s - primitiveFrequency (((a : ZMod m).val : ℕ) : ℤ) m ∈
            integralFiniteAdeleSubring}) := by
  have hm : m ≠ 0 := NeZero.ne m
  intro a _ b _ hab
  refine Set.disjoint_left.2 fun s hs hs' ↦ hab ?_
  simp only [Set.mem_setOf_eq] at hs hs'
  have hdiff : primitiveFrequency (((a : ZMod m).val : ℕ) : ℤ) m -
      primitiveFrequency (((b : ZMod m).val : ℕ) : ℤ) m ∈ integralFiniteAdeleSubring := by
    have h := Subring.sub_mem _ hs' hs
    rwa [show (s - primitiveFrequency (((b : ZMod m).val : ℕ) : ℤ) m) -
      (s - primitiveFrequency (((a : ZMod m).val : ℕ) : ℤ) m) =
        primitiveFrequency (((a : ZMod m).val : ℕ) : ℤ) m -
          primitiveFrequency (((b : ZMod m).val : ℕ) : ℤ) m from by ring] at h
  have hres := (primitiveFrequency_sub_mem_integral_iff _ _ m hm).1 hdiff
  rw [intCast_unitVal m a, intCast_unitVal m b] at hres
  exact Units.ext hres

/-! ## The mass -/

/-- The mass of the exact-conductor-`m` stratum is exactly `phi(m)`. -/
theorem measure_exactConductor_eq_totient (m : ℕ) [NeZero m] :
    rationalFiniteAdeleAddHaarMeasure
        {t : RationalFiniteAdele |
          t * (m : RationalFiniteAdele) ∈ integralFiniteAdeleSubring ∧
            HasExactConductor t m} =
      (Nat.totient m : ℝ≥0∞) := by
  rw [exactConductor_eq_iUnion m,
    show (⋃ a : (ZMod m)ˣ,
        {s : RationalFiniteAdele |
          s - primitiveFrequency (((a : ZMod m).val : ℕ) : ℤ) m ∈ integralFiniteAdeleSubring}) =
      ⋃ a ∈ (Finset.univ : Finset (ZMod m)ˣ),
        {s : RationalFiniteAdele |
          s - primitiveFrequency (((a : ZMod m).val : ℕ) : ℤ) m ∈ integralFiniteAdeleSubring} by
      simp,
    measure_biUnion_finset (pairwiseDisjoint_unitClasses m)
      (fun a _ => measurableSet_congruenceClass _)]
  have hone : ∀ a : (ZMod m)ˣ, rationalFiniteAdeleAddHaarMeasure
      {s : RationalFiniteAdele | s - primitiveFrequency (((a : ZMod m).val : ℕ) : ℤ) m ∈
        integralFiniteAdeleSubring} = 1 := fun a ↦ measure_congruenceClass_eq_one _
  simp only [hone, Finset.sum_const, Finset.card_univ, ZMod.card_units_eq_totient m]
  simp

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
