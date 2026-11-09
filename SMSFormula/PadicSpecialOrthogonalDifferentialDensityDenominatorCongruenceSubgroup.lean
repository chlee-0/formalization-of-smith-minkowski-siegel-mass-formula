import SMSFormula.PadicSpecialOrthogonalDifferentialDensityPadicDenominatorStability

/-!
# The denominator-congruence subgroup

This module defines the intermediate subgroup of the integral local lattice
stabilizer whose matrix is congruent to the identity modulo the local-dual
denominator.  At odd primes this is exactly the associated-bilinear
denominator subgroup.

It also proves the literal relative criterion: `g * h⁻¹` belongs to this
subgroup exactly when every column of the integral matrices of `g` and `h`
differs by a vector in the denominator.  No quotient, torsor, or Cayley
equivalence is constructed here.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

private theorem matrix_mul_right_forall_column_mem
    (p : ℕ) [Fact (Nat.Prime p)]
    (D : Submodule ℤ_[p] (Fin n → ℤ_[p]))
    (A B : Matrix (Fin n) (Fin n) ℤ_[p])
    (hA : ∀ j : Fin n, (fun i ↦ A i j) ∈ D) :
    ∀ j : Fin n, (fun i ↦ (A * B) i j) ∈ D := by
  intro j
  have hsum :
      (∑ l : Fin n, B l j • (fun i ↦ A i l)) ∈ D := by
    exact D.sum_mem fun l _ ↦ D.smul_mem (B l j) (hA l)
  convert hsum using 1
  funext i
  simp [Matrix.mul_apply, Pi.smul_apply, mul_comm]

/-- The subgroup of integral local stabilizers congruent to the identity
columnwise modulo the local-dual p-adic denominator. -/
def localPadicLatticeStabilizerLocalDualDenominatorCongruenceSubgroup
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] :
    Subgroup (L.localPadicLatticeStabilizerSubgroup p) where
  carrier := {g | ∀ j : Fin n,
    (fun i ↦
      L.localPadicLatticeStabilizerIntegralGL p g i j -
        (1 : Matrix (Fin n) (Fin n) ℤ_[p]) i j) ∈
      localDualPadicDenominator L p k}
  one_mem' := by
    intro j
    have hone :
        (L.localPadicLatticeStabilizerIntegralGL p 1).1 = 1 := by
      exact congrArg Units.val
        (L.localPadicLatticeStabilizerIntegralGLHom p).map_one
    rw [hone]
    have hz :
        (fun i ↦
          (1 : Matrix (Fin n) (Fin n) ℤ_[p]) i j -
            (1 : Matrix (Fin n) (Fin n) ℤ_[p]) i j) = 0 := by
      funext i
      simp
    rw [hz]
    exact (localDualPadicDenominator L p k).zero_mem
  mul_mem' := by
    intro g h hg hh j
    let A := (L.localPadicLatticeStabilizerIntegralGL p g).1
    let B := (L.localPadicLatticeStabilizerIntegralGL p h).1
    let dB : Fin n → ℤ_[p] := fun i ↦
      B i j - (1 : Matrix (Fin n) (Fin n) ℤ_[p]) i j
    have hdB : dB ∈ localDualPadicDenominator L p k := hh j
    have hmul : A.mulVec dB ∈ localDualPadicDenominator L p k :=
      (L.localPadicLatticeStabilizerIntegralGL_mulVec_mem_localDualPadicDenominator_iff
        p k g dB).2 hdB
    have hsum := (localDualPadicDenominator L p k).add_mem hmul (hg j)
    have hAB :
        (L.localPadicLatticeStabilizerIntegralGL p (g * h)).1 = A * B := by
      exact congrArg Units.val
        ((L.localPadicLatticeStabilizerIntegralGLHom p).map_mul g h)
    rw [hAB]
    convert hsum using 1
    funext i
    simp only [A, B, dB, Matrix.mulVec, dotProduct, Matrix.mul_apply,
      Pi.add_apply]
    have hmatrix : A * B - 1 = A * (B - 1) + (A - 1) := by
      noncomm_ring
    exact congr_fun (congr_fun hmatrix i) j
  inv_mem' := by
    intro g hg j
    let A := (L.localPadicLatticeStabilizerIntegralGL p g).1
    let Ainv := (L.localPadicLatticeStabilizerIntegralGL p g⁻¹).1
    let dA : Fin n → ℤ_[p] := fun i ↦
      A i j - (1 : Matrix (Fin n) (Fin n) ℤ_[p]) i j
    have hdA : dA ∈ localDualPadicDenominator L p k := hg j
    have hmul : Ainv.mulVec dA ∈ localDualPadicDenominator L p k :=
      (L.localPadicLatticeStabilizerIntegralGL_mulVec_mem_localDualPadicDenominator_iff
        p k g⁻¹ dA).2 hdA
    have hneg := (localDualPadicDenominator L p k).neg_mem hmul
    have hinv_mul : Ainv * A = 1 := by
      have hinv := (L.localPadicLatticeStabilizerIntegralGLHom p).map_inv g
      have hval := congrArg Units.val hinv
      simpa only [A, Ainv, hval] using
        (L.localPadicLatticeStabilizerIntegralGL p g).inv_val
    convert hneg using 1
    funext i
    simp only [A, Ainv, dA, Matrix.mulVec, dotProduct, Pi.neg_apply]
    have hmatrix : Ainv - 1 = -(Ainv * (A - 1)) := by
      calc
        Ainv - 1 = Ainv - Ainv * A := by rw [hinv_mul]
        _ = -(Ainv * (A - 1)) := by noncomm_ring
    exact congr_fun (congr_fun hmatrix i) j

/-- Membership in the local-dual denominator-congruence subgroup is its
literal columnwise condition. -/
theorem mem_localPadicLatticeStabilizerLocalDualDenominatorCongruenceSubgroup_iff
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (g : L.localPadicLatticeStabilizerSubgroup p) :
    g ∈ L.localPadicLatticeStabilizerLocalDualDenominatorCongruenceSubgroup p k ↔
      ∀ j : Fin n,
        (fun i ↦
          L.localPadicLatticeStabilizerIntegralGL p g i j -
            (1 : Matrix (Fin n) (Fin n) ℤ_[p]) i j) ∈
          localDualPadicDenominator L p k :=
  Iff.rfl

/-- The relative local-dual criterion for two integral stabilizers. -/
theorem mul_inv_mem_localPadicLatticeStabilizerLocalDualDenominatorCongruenceSubgroup_iff
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (g h : L.localPadicLatticeStabilizerSubgroup p) :
    g * h⁻¹ ∈
        L.localPadicLatticeStabilizerLocalDualDenominatorCongruenceSubgroup p k ↔
      ∀ j : Fin n,
        (fun i ↦
          L.localPadicLatticeStabilizerIntegralGL p g i j -
            L.localPadicLatticeStabilizerIntegralGL p h i j) ∈
          localDualPadicDenominator L p k := by
  let A := (L.localPadicLatticeStabilizerIntegralGL p g).1
  let B := (L.localPadicLatticeStabilizerIntegralGL p h).1
  let Binv := (L.localPadicLatticeStabilizerIntegralGL p h⁻¹).1
  let C := (L.localPadicLatticeStabilizerIntegralGL p (g * h⁻¹)).1
  have hB_Binv : B * Binv = 1 := by
    have hinv := (L.localPadicLatticeStabilizerIntegralGLHom p).map_inv h
    have hval := congrArg Units.val hinv
    simpa only [B, Binv, hval] using
      (L.localPadicLatticeStabilizerIntegralGL p h).val_inv
  have hBinv_B : Binv * B = 1 := by
    have hinv := (L.localPadicLatticeStabilizerIntegralGLHom p).map_inv h
    have hval := congrArg Units.val hinv
    simpa only [B, Binv, hval] using
      (L.localPadicLatticeStabilizerIntegralGL p h).inv_val
  have hC : C = A * Binv := by
    exact congrArg Units.val
      ((L.localPadicLatticeStabilizerIntegralGLHom p).map_mul g h⁻¹)
  have hforward : C - 1 = (A - B) * Binv := by
    rw [hC]
    calc
      A * Binv - 1 = A * Binv - B * Binv := by rw [hB_Binv]
      _ = (A - B) * Binv := by noncomm_ring
  have hbackward : A - B = (C - 1) * B := by
    rw [hC]
    calc
      A - B = A * (Binv * B) - B := by rw [hBinv_B, mul_one]
      _ = (A * Binv - 1) * B := by noncomm_ring
  constructor
  · intro hrel
    rw [mem_localPadicLatticeStabilizerLocalDualDenominatorCongruenceSubgroup_iff]
      at hrel
    have hcols : ∀ j : Fin n, (fun i ↦ (C - 1) i j) ∈
        localDualPadicDenominator L p k := by
      simpa [C, Matrix.sub_apply] using hrel
    have hright := matrix_mul_right_forall_column_mem p
      (localDualPadicDenominator L p k) (C - 1) B hcols
    intro j
    have hj := hright j
    rw [← hbackward] at hj
    simpa [A, B, Matrix.sub_apply] using hj
  · intro hdiff
    rw [mem_localPadicLatticeStabilizerLocalDualDenominatorCongruenceSubgroup_iff]
    have hcols : ∀ j : Fin n, (fun i ↦ (A - B) i j) ∈
        localDualPadicDenominator L p k := by
      simpa [A, B, Matrix.sub_apply] using hdiff
    have hright := matrix_mul_right_forall_column_mem p
      (localDualPadicDenominator L p k) (A - B) Binv hcols
    intro j
    have hj := hright j
    rw [← hforward] at hj
    simpa [C, Matrix.sub_apply] using hj

/-- At an odd prime, the local-dual subgroup is exactly the selected
associated-bilinear denominator-congruence subgroup. -/
theorem mem_localPadicLatticeStabilizerLocalDualDenominatorCongruenceSubgroup_iff_associated
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2)
    (g : L.localPadicLatticeStabilizerSubgroup p) :
    g ∈ L.localPadicLatticeStabilizerLocalDualDenominatorCongruenceSubgroup p k ↔
      ∀ j : Fin n,
        (fun i ↦
          L.localPadicLatticeStabilizerIntegralGL p g i j -
            (1 : Matrix (Fin n) (Fin n) ℤ_[p]) i j) ∈
          associatedBilinearDualPadicDenominator L p k := by
  rw [mem_localPadicLatticeStabilizerLocalDualDenominatorCongruenceSubgroup_iff,
    L.associatedBilinearDualPadicDenominator_eq_localDualPadicDenominator_of_ne_two
      p k hp2]

/-- The selected-depth ordinary reduction-range point represented by an
actual integral local stabilizer. -/
def localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionOfStabilizer
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (g : L.localPadicLatticeStabilizerSubgroup p) :
    L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange p :=
  ⟨L.localPadicLatticeStabilizerReduction p
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p) g,
    ⟨g, rfl⟩⟩

/-- Equality of quotient-family values of two actual stabilizers is exactly
columnwise membership of their p-adic matrix difference in the selected
associated-bilinear denominator. -/
theorem
    localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionOfStabilizer_quotient_eq_iff_padicColumnDifference_mem
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (g h : L.localPadicLatticeStabilizerSubgroup p) :
    L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRangeToQuotientFamily
        p
        (L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionOfStabilizer
          p g) =
        L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRangeToQuotientFamily
          p
          (L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionOfStabilizer
            p h) ↔
      ∀ j : Fin n,
        (fun i ↦
          L.localPadicLatticeStabilizerIntegralGL p g i j -
            L.localPadicLatticeStabilizerIntegralGL p h i j) ∈
          associatedBilinearDualPadicDenominator L p
            (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p) := by
  let k := L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p
  constructor
  · intro hquot j
    have hstd :=
      (L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRangeToQuotientFamily_eq_iff_columnDifference_mem
        p _ _).mp hquot j
    apply
      (L.padicVector_sub_mem_associatedBilinearDualPadicDenominator_iff_standardRepresentativeDifference_mem
        p k
        (fun i ↦ L.localPadicLatticeStabilizerIntegralGL p g i j)
        (fun i ↦ L.localPadicLatticeStabilizerIntegralGL p h i j)).2
    simpa only [k,
      localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionColumnDifference,
      localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionOfStabilizer,
      localPadicLatticeStabilizerReduction_apply] using hstd
  · intro hcols
    apply
      (L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRangeToQuotientFamily_eq_iff_columnDifference_mem
        p _ _).mpr
    intro j
    have hstd :=
      (L.padicVector_sub_mem_associatedBilinearDualPadicDenominator_iff_standardRepresentativeDifference_mem
        p k
        (fun i ↦ L.localPadicLatticeStabilizerIntegralGL p g i j)
        (fun i ↦ L.localPadicLatticeStabilizerIntegralGL p h i j)).1
        (hcols j)
    simpa only [k,
      localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionColumnDifference,
      localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionOfStabilizer,
      localPadicLatticeStabilizerReduction_apply] using hstd

/-- The selected-depth denominator-congruence subgroup `H_k`. -/
def localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceSubgroup
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    Subgroup (L.localPadicLatticeStabilizerSubgroup p) :=
  L.localPadicLatticeStabilizerLocalDualDenominatorCongruenceSubgroup p
    (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)

/-- At an odd prime, original relative membership in `H_k` is exactly
equality of the selected associated-bilinear quotient-family values. -/
theorem
    mul_inv_mem_localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceSubgroup_iff_quotient_eq
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2)
    (g h : L.localPadicLatticeStabilizerSubgroup p) :
    g * h⁻¹ ∈
        L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceSubgroup p ↔
      L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRangeToQuotientFamily
          p
          (L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionOfStabilizer
            p g) =
        L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRangeToQuotientFamily
          p
          (L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionOfStabilizer
            p h) := by
  rw [localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceSubgroup,
    L.mul_inv_mem_localPadicLatticeStabilizerLocalDualDenominatorCongruenceSubgroup_iff,
    ← L.associatedBilinearDualPadicDenominator_eq_localDualPadicDenominator_of_ne_two
      p (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p) hp2]
  exact
    (L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionOfStabilizer_quotient_eq_iff_padicColumnDifference_mem
      p g h).symm

/-- The coherent-branch/Hensel relative stabilizer belongs to the selected
denominator-congruence subgroup throughout one odd-prime liftable fiber. -/
theorem infinitelyLiftableRawGramFiber_relativeStabilizer_mem_denominatorCongruenceSubgroup
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2)
    (Y :
      L.localPadicSpecialOrthogonalDifferentialDensityAssociatedBilinearQuotientFamily
        p)
    (X :
      L.localPadicSpecialOrthogonalDifferentialDensityInfinitelyLiftableRawGramFiber
        p hp2 Y) :
    L.localPadicSpecialOrthogonalDifferentialDensityInfinitelyLiftableRawGramStabilizer
          p X.1 *
        (L.localPadicSpecialOrthogonalDifferentialDensityQuotientFamilyHenselStabilizer
          p Y)⁻¹ ∈
      L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceSubgroup p := by
  rw [localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceSubgroup,
    L.mul_inv_mem_localPadicLatticeStabilizerLocalDualDenominatorCongruenceSubgroup_iff]
  intro j
  rw [← L.associatedBilinearDualPadicDenominator_eq_localDualPadicDenominator_of_ne_two
    p (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p) hp2]
  exact
    L.infinitelyLiftableRawGramFiber_padicStabilizerColumnDifference_mem_denominator
      p hp2 Y X j

end PositiveDefiniteIntegralLattice
