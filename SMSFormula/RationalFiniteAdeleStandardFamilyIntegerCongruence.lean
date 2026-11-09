import SMSFormula.RationalFiniteAdeleStandardFamilyDualDiagonal

/-!
# The literal quotient is integer congruence, on the rational diagonal

Poisson for the family was reduced to Poisson for a single coset indicator.
This file converts that last piece from adelic language into pure integer
language: on the rational diagonal the literal finite quotient
`Zhat^n / N * Zhat^n` detects exactly congruence of integer vectors modulo `N`,
and every class is the class of an integer vector.

Consequently a coset indicator evaluated on the integer diagonal is the literal
integer congruence indicator, and what is left is a statement about
`Z^n` alone: no further adelic construction is involved.

The integer vectors here are supplied, never chosen from a class, except in the
surjectivity statement, which is an existence theorem derived from the
residue surjectivity and stores nothing.
-/

noncomputable section

open PositiveDefiniteIntegralLattice MeasureTheory Matrix
open scoped BigOperators

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-! ## Integer vectors inside the integral coordinate lattice -/

/-- The integral coordinate vector attached to an integer vector. -/
def integerToIntegralFiniteAdeleVector (n : ℕ) (m : Fin n → ℤ) :
    Fin n → IntegralFiniteAdele :=
  fun i => integerToIntegralFiniteAdele (m i)

@[simp]
theorem integerToIntegralFiniteAdeleVector_coe (n : ℕ) (m : Fin n → ℤ) :
    (fun i => ((integerToIntegralFiniteAdeleVector n m i : IntegralFiniteAdele) :
      RationalFiniteAdele)) =
      rationalFiniteAdeleVectorDiagonal n (fun i => ((m i : ℤ) : ℚ)) := rfl

theorem mem_integralFiniteAdeleCoordinateNatDilation_range_iff (n N : ℕ)
    (z : Fin n → IntegralFiniteAdele) :
    z ∈ (integralFiniteAdeleCoordinateNatDilation n N).range ↔
      ∀ i, z i ∈ (integralFiniteAdeleNatDilation N).range := by
  classical
  constructor
  · rintro ⟨w, rfl⟩ i
    exact ⟨w i, rfl⟩
  · intro h
    choose w hw using h
    exact ⟨w, by funext i; exact hw i⟩

theorem integerVector_mem_coordinateNatDilation_range_iff {N : ℕ} (hN : N ≠ 0)
    (m : Fin n → ℤ) :
    integerToIntegralFiniteAdeleVector n m ∈
        (integralFiniteAdeleCoordinateNatDilation n N).range ↔
      ∀ i, (N : ℤ) ∣ m i := by
  rw [mem_integralFiniteAdeleCoordinateNatDilation_range_iff]
  exact forall_congr' fun i =>
    integerToIntegralFiniteAdele_mem_natDilation_range_iff hN (m i)

/-! ## The literal quotient detects integer congruence -/

/-- Two integer vectors have the same class in the literal finite quotient
exactly when they are congruent modulo `N` coordinatewise. -/
theorem integerVector_quotient_eq_iff {N : ℕ} (hN : N ≠ 0) (m m' : Fin n → ℤ) :
    ((integerToIntegralFiniteAdeleVector n m :
        (Fin n → IntegralFiniteAdele) ⧸
          (integralFiniteAdeleCoordinateNatDilation n N).range) =
      (integerToIntegralFiniteAdeleVector n m' :
        (Fin n → IntegralFiniteAdele) ⧸
          (integralFiniteAdeleCoordinateNatDilation n N).range)) ↔
      ∀ i, (N : ℤ) ∣ (m i - m' i) := by
  rw [QuotientAddGroup.eq_iff_sub_mem]
  have hsub : integerToIntegralFiniteAdeleVector n m -
      integerToIntegralFiniteAdeleVector n m' =
      integerToIntegralFiniteAdeleVector n (fun i => m i - m' i) := by
    funext i
    exact (map_sub integerToIntegralFiniteAdele (m i) (m' i)).symm
  rw [hsub]
  exact integerVector_mem_coordinateNatDilation_range_iff hN _

/-- Every class of the literal quotient is the class of an integer vector.
This is an existence theorem derived from the residue surjectivity; nothing
is stored. -/
theorem exists_integerVector_quotient_eq {N : ℕ} (hN : N ≠ 0)
    (y : Fin n → IntegralFiniteAdele) :
    ∃ m : Fin n → ℤ,
      ((integerToIntegralFiniteAdeleVector n m :
        (Fin n → IntegralFiniteAdele) ⧸
          (integralFiniteAdeleCoordinateNatDilation n N).range)) =
        (y : (Fin n → IntegralFiniteAdele) ⧸
          (integralFiniteAdeleCoordinateNatDilation n N).range) := by
  classical
  have hscalar : ∀ i, ∃ z : ℤ,
      ((integerToIntegralFiniteAdele z :
        IntegralFiniteAdele ⧸ (integralFiniteAdeleNatDilation N).range)) =
        (y i : IntegralFiniteAdele ⧸ (integralFiniteAdeleNatDilation N).range) := by
    intro i
    obtain ⟨r, hr⟩ := residueToIntegralFiniteAdeleModDilation_surjective hN
      ((y i : IntegralFiniteAdele ⧸ (integralFiniteAdeleNatDilation N).range))
    obtain ⟨z, rfl⟩ := ZMod.intCast_surjective r
    rw [residueToIntegralFiniteAdeleModDilation_intCast] at hr
    exact ⟨z, hr⟩
  choose z hz using hscalar
  refine ⟨z, QuotientAddGroup.eq_iff_sub_mem.mpr ?_⟩
  rw [mem_integralFiniteAdeleCoordinateNatDilation_range_iff]
  intro i
  exact QuotientAddGroup.eq_iff_sub_mem.mp (hz i)

/-! ## Coset indicators on the integer diagonal -/

theorem integerDiagonal_lift {m : Fin n → ℤ}
    (hm : rationalFiniteAdeleVectorDiagonal n (fun i => ((m i : ℤ) : ℚ)) ∈
      integralFiniteAdeleVectors n) :
    (fun i => (⟨rationalFiniteAdeleVectorDiagonal n (fun i => ((m i : ℤ) : ℚ)) i,
      hm i⟩ : IntegralFiniteAdele)) = integerToIntegralFiniteAdeleVector n m := by
  funext i
  exact Subtype.ext rfl

/-- On the integer diagonal a coset indicator is the literal integer congruence
indicator.  Both integer vectors are supplied. -/
theorem standardCosetIndicator_integerDiagonal_of_dvd {N : ℕ} (hN : N ≠ 0)
    (m m' : Fin n → ℤ) (hdvd : ∀ i, (N : ℤ) ∣ (m i - m' i)) :
    standardCosetIndicator n N
        ((integerToIntegralFiniteAdeleVector n m' :
          (Fin n → IntegralFiniteAdele) ⧸
            (integralFiniteAdeleCoordinateNatDilation n N).range))
        (rationalFiniteAdeleVectorDiagonal n (fun i => ((m i : ℤ) : ℚ))) = 1 := by
  have hm := integerDiagonal_mem_integralFiniteAdeleVectors m
  refine Set.indicator_of_mem ?_ _
  rw [mem_standardCosetSet_iff_of_mem _ hm, integerDiagonal_lift hm]
  exact (integerVector_quotient_eq_iff hN m m').mpr hdvd

theorem standardCosetIndicator_integerDiagonal_of_not_dvd {N : ℕ} (hN : N ≠ 0)
    (m m' : Fin n → ℤ) (hdvd : ¬ ∀ i, (N : ℤ) ∣ (m i - m' i)) :
    standardCosetIndicator n N
        ((integerToIntegralFiniteAdeleVector n m' :
          (Fin n → IntegralFiniteAdele) ⧸
            (integralFiniteAdeleCoordinateNatDilation n N).range))
        (rationalFiniteAdeleVectorDiagonal n (fun i => ((m i : ℤ) : ℚ))) = 0 := by
  have hm := integerDiagonal_mem_integralFiniteAdeleVectors m
  refine Set.indicator_of_notMem (fun hmem => hdvd ?_) _
  have := (mem_standardCosetSet_iff_of_mem _ hm).mp hmem
  rw [integerDiagonal_lift hm] at this
  exact (integerVector_quotient_eq_iff hN m m').mp this

/-! ## The coset diagonal sum is an integer congruence sum -/

theorem rationalScaledIntegerVector_one (m : Fin n → ℤ) :
    rationalScaledIntegerVector 1 m = fun i => ((m i : ℤ) : ℚ) := by
  funext i
  show ((m i : ℤ) : ℚ) / (((1 : ℕ) : ℚ)) = _
  norm_num

/-- The literal integer congruence indicator modulo `N`. -/
def integerCongruenceIndicator (n N : ℕ) (m' m : Fin n → ℤ) : ℂ :=
  if ∀ i, (N : ℤ) ∣ (m i - m' i) then 1 else 0

theorem standardCosetIndicator_integerDiagonal_eq {N : ℕ} (hN : N ≠ 0)
    (m m' : Fin n → ℤ) :
    standardCosetIndicator n N
        ((integerToIntegralFiniteAdeleVector n m' :
          (Fin n → IntegralFiniteAdele) ⧸
            (integralFiniteAdeleCoordinateNatDilation n N).range))
        (rationalFiniteAdeleVectorDiagonal n (fun i => ((m i : ℤ) : ℚ))) =
      integerCongruenceIndicator n N m' m := by
  unfold integerCongruenceIndicator
  by_cases hdvd : ∀ i, (N : ℤ) ∣ (m i - m' i)
  · rw [standardCosetIndicator_integerDiagonal_of_dvd hN m m' hdvd, if_pos hdvd]
  · rw [standardCosetIndicator_integerDiagonal_of_not_dvd hN m m' hdvd, if_neg hdvd]

/-- The rational-diagonal sum against a coset indicator is the literal integer
congruence-class sum.  This removes the last adelic ingredient: what remains for
Poisson is a statement about `Z^n` alone. -/
theorem tsum_rationalDiagonal_standardCosetIndicator {N : ℕ} (hN : N ≠ 0)
    (G : (Fin n → ℚ) → ℂ) (m' : Fin n → ℤ) :
    (∑' q : Fin n → ℚ, G q * standardCosetIndicator n N
        ((integerToIntegralFiniteAdeleVector n m' :
          (Fin n → IntegralFiniteAdele) ⧸
            (integralFiniteAdeleCoordinateNatDilation n N).range))
        (rationalFiniteAdeleVectorDiagonal n q)) =
      ∑' m : Fin n → ℤ, G (fun i => ((m i : ℤ) : ℚ)) *
        integerCongruenceIndicator n N m' m := by
  rw [tsum_rationalDiagonal_mul one_ne_zero
    (isStandardCarried_standardCosetIndicator n N _) G]
  refine tsum_congr fun m => ?_
  rw [rationalScaledIntegerVector_one, standardCosetIndicator_integerDiagonal_eq hN]

end RationalQuadraticSpaceMatrix
