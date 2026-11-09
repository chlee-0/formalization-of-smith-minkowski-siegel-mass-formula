import SMSFormula.Genus
import SMSFormula.IntegralLatticeCoordinates
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.LinearAlgebra.Matrix.Integer
import Mathlib.Data.ZMod.Coprime
import Mathlib.Data.Sym.Card
import Mathlib.NumberTheory.Padics.RingHoms

/-!
# Schulze--Pillot local density: finite congruence counts

This file defines the local density at a prime `p` from finite congruence
counts. `SMSFormula.LocalDensity` proves the quantitative Hensel recurrence
that makes it independent of the admissible exponent.

For an integral matrix `A` and a positive modulus `m`,
`congruenceSolutionMatrices A m` is the finite set of matrices `X` over `ZMod m`
satisfying
`Xᵀ A X = A` modulo `m`.  The specialization
`gramCongruenceSolutionCount L p k` is the raw count

`#{X in M_n(Z / p^k Z) | Xᵀ gram(L) X = gram(L)}`.

The normalized density `normalizedLocalDensity` (Schulze--Pillot) combines the
local-dual quotient count at an admissible exponent `k`, the determinant
factor and the `|2|_p` factor. The adjacent-depth Hensel recurrence
(`localDualQuotientCount_succ_eq`) shows that the result does not depend on
`k`.
-/

open Matrix

noncomputable section

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-! ## Matrix congruence solution counts -/

/-- Reduce an integral matrix modulo the positive modulus `m`. -/
def matrixMod (A : Matrix (Fin n) (Fin n) ℤ) (m : ℕ+) :
    Matrix (Fin n) (Fin n) (ZMod (m : ℕ)) :=
  A.map (Int.cast : ℤ → ZMod m)

/-- Matrices over `ZMod m` preserving the integral matrix `A` modulo the
positive modulus `m`. -/
def congruenceSolutionMatrices (A : Matrix (Fin n) (Fin n) ℤ) (m : ℕ+) :
    Finset (Matrix (Fin n) (Fin n) (ZMod (m : ℕ))) :=
  Finset.univ.filter fun X => Xᵀ * matrixMod A m * X = matrixMod A m

/-- The finite number of matrices over `ZMod m` preserving `A` modulo the
positive modulus `m`. -/
def congruenceSolutionCount (A : Matrix (Fin n) (Fin n) ℤ) (m : ℕ+) : ℕ :=
  (congruenceSolutionMatrices A m).card

lemma mem_congruenceSolutionMatrices_iff
    {A : Matrix (Fin n) (Fin n) ℤ} {m : ℕ+}
    {X : Matrix (Fin n) (Fin n) (ZMod (m : ℕ))} :
    X ∈ congruenceSolutionMatrices A m ↔
      Xᵀ * matrixMod A m * X = matrixMod A m := by
  simp [congruenceSolutionMatrices]

/-! ## Gram-matrix specialization for integral lattices -/

/-- The positive modulus `p^k` attached to a prime `p`. -/
def primePowModulus (p k : ℕ) [Fact (Nat.Prime p)] : ℕ+ :=
  ⟨p ^ k, pow_pos (Fact.out : Nat.Prime p).pos k⟩

/-- An integral quadratic congruence modulo `p^(k+1)` remains valid after
reduction modulo `p^k`. -/
lemma quadForm_zmod_eq_of_succ
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    {x y : Fin n → ℤ}
    (h : (L.quadForm y : ZMod (primePowModulus p (k + 1) : ℕ)) =
      (L.quadForm x : ZMod (primePowModulus p (k + 1) : ℕ))) :
    (L.quadForm y : ZMod (primePowModulus p k : ℕ)) =
      (L.quadForm x : ZMod (primePowModulus p k : ℕ)) := by
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h ⊢
  exact dvd_trans (by
    change ((p ^ k : ℕ) : ℤ) ∣ ((p ^ (k + 1) : ℕ) : ℤ)
    push_cast
    rw [pow_succ]
    exact dvd_mul_right _ _) h

/-- The raw matrix solution set
`{X : M_n(Z / p^k Z) | Xᵀ gram(L) X = gram(L)}`. -/
def gramCongruenceSolutionMatrices (L : PositiveDefiniteIntegralLattice n) (p k : ℕ)
    [Fact (Nat.Prime p)] :
    Finset (Matrix (Fin n) (Fin n) (ZMod (primePowModulus p k : ℕ))) :=
  congruenceSolutionMatrices L.polarGramMatrix (primePowModulus p k)

/-- The raw matrix count
`#{X : M_n(Z / p^k Z) | Xᵀ gram(L) X = gram(L)}` used in the local-density
matrix-count comparison. -/
def gramCongruenceSolutionCount (L : PositiveDefiniteIntegralLattice n) (p k : ℕ)
    [Fact (Nat.Prime p)] : ℕ :=
  (gramCongruenceSolutionMatrices L p k).card

lemma mem_gramCongruenceSolutionMatrices_iff
    {L : PositiveDefiniteIntegralLattice n} {p k : ℕ} [Fact (Nat.Prime p)]
    {X : Matrix (Fin n) (Fin n) (ZMod (primePowModulus p k : ℕ))} :
    X ∈ gramCongruenceSolutionMatrices L p k ↔
      Xᵀ * matrixMod L.polarGramMatrix (primePowModulus p k) * X =
        matrixMod L.polarGramMatrix (primePowModulus p k) := by
  simp [gramCongruenceSolutionMatrices, mem_congruenceSolutionMatrices_iff]

/-! ## Coordinate local-dual quotient count -/

/-- The coordinate quotient that models `L_p / p^k L_p#` after choosing a
full-rank integral coordinate submodule `D` for the admissible denominator.

The intended later specialization is `D = p^k L_p# ∩ L` in coordinates. -/
abbrev localDualQuotientTarget (D : Submodule ℤ (Fin n → ℤ)) :=
  (Fin n → ℤ) ⧸ D

/-- The good-prime coordinate denominator `p^k • ℤ^n`, used when
`p^k L_p# ∩ L` is just the scalar multiple of the chosen coordinate lattice. -/
def primePowCoordinateSubmodule (p k : ℕ) :
    Submodule ℤ (Fin n → ℤ) :=
  LinearMap.range (LinearMap.lsmul ℤ (Fin n → ℤ) (p ^ k : ℤ))

lemma primePowCoordinateSubmodule_rank (p k : ℕ) [Fact (Nat.Prime p)] :
    Module.finrank ℤ (primePowCoordinateSubmodule (n := n) p k) = n := by
  have hp_pos : 0 < p ^ k := pow_pos (Fact.out : Nat.Prime p).pos k
  have hp_ne : (p ^ k : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt hp_pos)
  simpa [primePowCoordinateSubmodule, Module.finrank_fintype_fun_eq_card,
    Fintype.card_fin] using
      (LinearMap.finrank_range_of_inj
        (LinearMap.lsmul_injective (R := ℤ) (M := Fin n → ℤ) hp_ne))

lemma primePowCoordinateSubmodule_subquotient_card
    (p k a : ℕ) [Fact (Nat.Prime p)] (ha : a ≤ k) :
    Nat.card (primePowCoordinateSubmodule (n := n) p (k - a) ⧸
      (primePowCoordinateSubmodule (n := n) p k).comap
        (primePowCoordinateSubmodule (n := n) p (k - a)).subtype) =
      p ^ (n * a) := by
  classical
  let E : Submodule ℤ (Fin n → ℤ) := primePowCoordinateSubmodule (n := n) p (k - a)
  let D : Submodule ℤ (Fin n → ℤ) := primePowCoordinateSubmodule (n := n) p k
  let N : Submodule ℤ E := D.comap E.subtype
  have hmem_smul : ∀ x : E, ((p ^ a : ℤ) • x : E) ∈ N := by
    intro x
    change ((p ^ a : ℤ) • (x : Fin n → ℤ)) ∈ D
    rcases x.2 with ⟨z, hz⟩
    refine ⟨z, ?_⟩
    ext i
    have hi := congr_fun hz i
    have hi' : (p ^ (k - a) : ℤ) * z i = (x : Fin n → ℤ) i := by
      simpa [Pi.smul_apply, smul_eq_mul] using hi
    have hpowNat : p ^ k = p ^ a * p ^ (k - a) := by
      rw [← Nat.pow_add, Nat.add_sub_of_le ha]
    have hpowInt : (p ^ k : ℤ) = (p ^ a : ℤ) * (p ^ (k - a) : ℤ) := by
      exact_mod_cast hpowNat
    calc
      ((LinearMap.lsmul ℤ (Fin n → ℤ) (p ^ k : ℤ)) z) i =
          (p ^ k : ℤ) * z i := by simp
      _ = (p ^ a : ℤ) * ((p ^ (k - a) : ℤ) * z i) := by rw [hpowInt]; ring
      _ = (p ^ a : ℤ) * (x : Fin n → ℤ) i := by rw [hi']
      _ = ((p ^ a : ℤ) • (x : Fin n → ℤ)) i := by simp [Pi.smul_apply]
  let f : E →ₗ[ℤ] N :=
    LinearMap.codRestrict N (LinearMap.lsmul ℤ E (p ^ a : ℤ)) hmem_smul
  have hpowa_ne : (p ^ a : ℤ) ≠ 0 := by
    have hpowa_pos : (0 : ℤ) < (p ^ a : ℕ) := by
      exact_mod_cast (pow_pos (Fact.out : Nat.Prime p).pos a)
    exact ne_of_gt hpowa_pos
  have hf_inj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    have hxyE : ((p ^ a : ℤ) • x : E) = (p ^ a : ℤ) • y := by
      exact congrArg (fun z : N => (z : E)) hxy
    exact congrArg Subtype.val
      ((LinearMap.lsmul_injective (R := ℤ) (M := E) hpowa_ne) hxyE)
  have hf_surj : Function.Surjective f := by
    intro y
    rcases y.2 with ⟨z, hz⟩
    have hx_mem : ((LinearMap.lsmul ℤ (Fin n → ℤ) (p ^ (k - a) : ℤ)) z) ∈ E :=
      ⟨z, rfl⟩
    let x : E := ⟨(LinearMap.lsmul ℤ (Fin n → ℤ) (p ^ (k - a) : ℤ)) z, hx_mem⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    ext i
    have hi := congr_fun hz i
    have hpowNat : p ^ k = p ^ a * p ^ (k - a) := by
      rw [← Nat.pow_add, Nat.add_sub_of_le ha]
    have hpowInt : (p ^ k : ℤ) = (p ^ a : ℤ) * (p ^ (k - a) : ℤ) := by
      exact_mod_cast hpowNat
    calc
      ((f x : N) : E).1 i = ((p ^ a : ℤ) • (x : E) : E).1 i := rfl
      _ = (p ^ a : ℤ) * ((p ^ (k - a) : ℤ) * z i) := by simp [x]
      _ = (p ^ k : ℤ) * z i := by rw [hpowInt]; ring
      _ = y.1.1 i := by simpa [Pi.smul_apply, smul_eq_mul] using hi
  let e : E ≃ₗ[ℤ] N := LinearEquiv.ofBijective f ⟨hf_inj, hf_surj⟩
  have hcomp : N.subtype ∘ₗ (e : E →ₗ[ℤ] N) = LinearMap.lsmul ℤ E (p ^ a : ℤ) := by
    ext x
    rfl
  have hdet : LinearMap.det (N.subtype ∘ₗ (e : E →ₗ[ℤ] N)) =
      (p ^ a : ℤ) ^ Module.finrank ℤ E := by
    rw [hcomp]
    change LinearMap.det ((p ^ a : ℤ) • (LinearMap.id : E →ₗ[ℤ] E)) = _
    rw [LinearMap.det_smul, LinearMap.det_id, mul_one]
  have hrank : Module.finrank ℤ E = n := by
    simpa [E] using primePowCoordinateSubmodule_rank (n := n) p (k - a)
  have hcard := (Submodule.natAbs_det_equiv N e).symm
  change Nat.card (E ⧸ N) = p ^ (n * a)
  rw [hcard]
  change (LinearMap.det (N.subtype ∘ₗ (e : E →ₗ[ℤ] N))).natAbs = p ^ (n * a)
  rw [hdet, hrank]
  have hbase : ((p : ℤ) ^ a).natAbs = p ^ a := by
    rw [Int.natAbs_pow, Int.natAbs_natCast]
  rw [Int.natAbs_pow, hbase, ← Nat.pow_mul]
  congr 1
  exact Nat.mul_comm a n

/-- The `i`th coordinate, reduced modulo `p^k`, as a `ℤ`-linear map. -/
def coordinateModLinearMap (p k : ℕ) [Fact (Nat.Prime p)] (i : Fin n) :
    (Fin n → ℤ) →ₗ[ℤ] ZMod (primePowModulus p k : ℕ) where
  toFun x := (x i : ZMod (primePowModulus p k : ℕ))
  map_add' x y := by simp
  map_smul' a x := by simp

/-- The integral coordinate map `x ↦ A x mod p^k` attached to an integral
matrix `A`. -/
def matrixModLinearMap (A : Matrix (Fin n) (Fin n) ℤ)
    (p k : ℕ) [Fact (Nat.Prime p)] :
    (Fin n → ℤ) →ₗ[ℤ] (Fin n → ZMod (primePowModulus p k : ℕ)) where
  toFun x :=
    (matrixMod A (primePowModulus p k)).mulVec
      (fun i : Fin n => (x i : ZMod (primePowModulus p k : ℕ)))
  map_add' x y := by
    ext i
    simp [Matrix.mulVec, dotProduct, Finset.sum_add_distrib, mul_add]
  map_smul' a x := by
    ext i
    simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_left_comm]

lemma primePowCoordinateSubmodule_le_coordinateModLinearMap_ker
    (p k : ℕ) [Fact (Nat.Prime p)] (i : Fin n) :
    primePowCoordinateSubmodule (n := n) p k ≤
      LinearMap.ker (coordinateModLinearMap (n := n) p k i) := by
  intro x hx
  rcases hx with ⟨z, hz⟩
  rw [LinearMap.mem_ker]
  have hi := congr_fun hz i
  have hxcoord : x i = (p ^ k : ℤ) * z i := by
    simpa [Pi.smul_apply, smul_eq_mul] using hi.symm
  have hpz : ((p ^ k : ℤ) : ZMod (primePowModulus p k : ℕ)) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact dvd_rfl
  change ((x i : ℤ) : ZMod (primePowModulus p k : ℕ)) = 0
  rw [hxcoord]
  simp [Int.cast_mul, hpz]

/-- The coordinate identification
`ℤ^n / p^kℤ^n → ZMod (p^k)` on one coordinate. -/
def primePowQuotientCoordinate (p k : ℕ) [Fact (Nat.Prime p)] (i : Fin n) :
    localDualQuotientTarget (primePowCoordinateSubmodule (n := n) p k) →ₗ[ℤ]
      ZMod (primePowModulus p k : ℕ) :=
  (primePowCoordinateSubmodule (n := n) p k).liftQ
    (coordinateModLinearMap (n := n) p k i)
    (primePowCoordinateSubmodule_le_coordinateModLinearMap_ker (n := n) p k i)

set_option backward.isDefEq.respectTransparency false in
@[simp] lemma primePowQuotientCoordinate_mkQ
    (p k : ℕ) [Fact (Nat.Prime p)] (i : Fin n) (x : Fin n → ℤ) :
    primePowQuotientCoordinate (n := n) p k i
        ((primePowCoordinateSubmodule (n := n) p k).mkQ x) =
      (x i : ZMod (primePowModulus p k : ℕ)) := by
  simp [primePowQuotientCoordinate, coordinateModLinearMap]

/-- The coordinate vector of a class in `ℤ^n / p^kℤ^n`, written in
`(ZMod (p^k))^n`. -/
def primePowQuotientVector (p k : ℕ) [Fact (Nat.Prime p)]
    (q : localDualQuotientTarget (primePowCoordinateSubmodule (n := n) p k)) :
    Fin n → ZMod (primePowModulus p k : ℕ) :=
  fun i => primePowQuotientCoordinate (n := n) p k i q

@[simp] lemma primePowQuotientVector_mkQ
    (p k : ℕ) [Fact (Nat.Prime p)] (x : Fin n → ℤ) :
    primePowQuotientVector (n := n) p k
        ((primePowCoordinateSubmodule (n := n) p k).mkQ x) =
      fun i : Fin n => (x i : ZMod (primePowModulus p k : ℕ)) := by
  ext i
  exact primePowQuotientCoordinate_mkQ (n := n) p k i x

lemma mem_primePowCoordinateSubmodule_iff_coordinate_zmod_eq_zero
    (p k : ℕ) [Fact (Nat.Prime p)] (x : Fin n → ℤ) :
    x ∈ primePowCoordinateSubmodule (n := n) p k ↔
      ∀ i : Fin n, (x i : ZMod (primePowModulus p k : ℕ)) = 0 := by
  constructor
  · intro hx i
    have hker :=
      primePowCoordinateSubmodule_le_coordinateModLinearMap_ker (n := n) p k i hx
    simpa [coordinateModLinearMap] using hker
  · intro hx
    classical
    have hdiv : ∀ i : Fin n, (p ^ k : ℤ) ∣ x i := by
      intro i
      have hi := hx i
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hi
      simpa [primePowModulus] using hi
    choose z hz using hdiv
    refine ⟨z, ?_⟩
    ext i
    simpa [Pi.smul_apply, smul_eq_mul] using (hz i).symm

lemma zmod_pow_mul_eq_zero_iff_of_le
    (p k v : ℕ) [Fact (Nat.Prime p)] (hv : v ≤ k) (a : ℤ) :
    (((p ^ v : ℤ) * a : ℤ) : ZMod (primePowModulus p k : ℕ)) = 0 ↔
      ((a : ℤ) : ZMod (primePowModulus p (k - v) : ℕ)) = 0 := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd, ZMod.intCast_zmod_eq_zero_iff_dvd]
  change (p ^ k : ℤ) ∣ (p ^ v : ℤ) * a ↔ (p ^ (k - v) : ℤ) ∣ a
  have hpowNat : p ^ k = p ^ v * p ^ (k - v) := by
    rw [← Nat.pow_add, Nat.add_sub_of_le hv]
  have hpowInt : (p ^ k : ℤ) = (p ^ v : ℤ) * (p ^ (k - v) : ℤ) := by
    exact_mod_cast hpowNat
  rw [hpowInt]
  have hpv_ne : (p ^ v : ℤ) ≠ 0 := by
    have hpv_pos : (0 : ℤ) < (p ^ v : ℕ) := by
      exact_mod_cast (pow_pos (Fact.out : Nat.Prime p).pos v)
    exact ne_of_gt hpv_pos
  exact mul_dvd_mul_iff_left hpv_ne

/-- The coordinatewise diagonal denominator
`{x : ℤ^n | x_i ≡ 0 mod p^(k - v_i)}`.  This is the expected kernel for a
diagonal form matrix with diagonal entries `p^(v_i)`, under `v_i ≤ k`. -/
def diagonalPrimePowCoordinateSubmodule
    (p k : ℕ) [Fact (Nat.Prime p)] (v : Fin n → ℕ) :
    Submodule ℤ (Fin n → ℤ) where
  carrier := {x | ∀ i : Fin n,
    (x i : ZMod (primePowModulus p (k - v i) : ℕ)) = 0}
  zero_mem' := by
    intro i
    simp
  add_mem' := by
    intro x y hx hy i
    simp [hx i, hy i]
  smul_mem' := by
    intro a x hx i
    simp [hx i]

lemma mem_diagonalPrimePowCoordinateSubmodule_iff
    (p k : ℕ) [Fact (Nat.Prime p)] (v : Fin n → ℕ) (x : Fin n → ℤ) :
    x ∈ diagonalPrimePowCoordinateSubmodule (n := n) p k v ↔
      ∀ i : Fin n, (x i : ZMod (primePowModulus p (k - v i) : ℕ)) = 0 :=
  Iff.rfl

lemma primePowCoordinateSubmodule_le_diagonalPrimePowCoordinateSubmodule
    (p k : ℕ) [Fact (Nat.Prime p)] (v : Fin n → ℕ) (hv : ∀ i, v i ≤ k) :
    primePowCoordinateSubmodule (n := n) p k ≤
      diagonalPrimePowCoordinateSubmodule (n := n) p k v := by
  intro x hx
  rcases hx with ⟨z, hz⟩
  rw [mem_diagonalPrimePowCoordinateSubmodule_iff]
  intro i
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  refine ⟨(p ^ v i : ℤ) * z i, ?_⟩
  have hi := congr_fun hz i
  have hpowNat : p ^ k = p ^ (k - v i) * p ^ v i := by
    rw [← Nat.pow_add, Nat.sub_add_cancel (hv i)]
  have hpowInt : (p ^ k : ℤ) = (p ^ (k - v i) : ℤ) * (p ^ v i : ℤ) := by
    exact_mod_cast hpowNat
  calc
    x i = (p ^ k : ℤ) * z i := by
      simpa [Pi.smul_apply, smul_eq_mul] using hi.symm
    _ = ((p ^ (k - v i) : ℤ) * (p ^ v i : ℤ)) * z i := by rw [hpowInt]
    _ = (p ^ (k - v i) : ℤ) * ((p ^ v i : ℤ) * z i) := by ring

/-- The coordinate kernel
`{x : ℤ^n | F x ≡ 0 mod p^k}` for the stored form matrix `F`.

This is the integral-coordinate integral model expected from
`p^k L_p# ∩ L`: in coordinates, local-dual denominator vectors are those whose
form-matrix products vanish modulo `p^k`. -/
def pairingMatrixLocalDualCoordinateSubmodule
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] :
    Submodule ℤ (Fin n → ℤ) :=
  LinearMap.ker (matrixModLinearMap (n := n) L.pairingMatrix p k)

/-- Quotient cardinality is unchanged after transporting a coordinate
submodule by a linear equivalence. -/
lemma coordinateSubmodule_quotient_card_eq_map_linearEquiv
    (D : Submodule ℤ (Fin n → ℤ))
    (e : (Fin n → ℤ) ≃ₗ[ℤ] (Fin n → ℤ)) :
    Nat.card ((Fin n → ℤ) ⧸ Submodule.map e.toLinearMap D) =
      Nat.card ((Fin n → ℤ) ⧸ D) := by
  exact
    (Nat.card_congr
      (Submodule.Quotient.equiv D (Submodule.map e.toLinearMap D) e rfl).toEquiv).symm

@[simp] lemma intMatrixLinearEquivOfIsUnit_apply
    (U : Matrix (Fin n) (Fin n) ℤ) (hU : IsUnit U) (x : Fin n → ℤ) :
    intMatrixLinearEquivOfIsUnit U hU x = U.mulVec x := rfl

@[simp] lemma intMatrixLinearEquivOfIsUnit_symm_apply
    (U : Matrix (Fin n) (Fin n) ℤ) (hU : IsUnit U) (x : Fin n → ℤ) :
    (intMatrixLinearEquivOfIsUnit U hU).symm x = U⁻¹.mulVec x := rfl

lemma matrixModLinearMap_mul_apply
    (A B : Matrix (Fin n) (Fin n) ℤ)
    (p k : ℕ) [Fact (Nat.Prime p)] (x : Fin n → ℤ) :
    matrixModLinearMap (n := n) (A * B) p k x =
      (matrixMod A (primePowModulus p k)).mulVec
        (matrixModLinearMap (n := n) B p k x) := by
  change (matrixMod (A * B) (primePowModulus p k)).mulVec
      (fun i : Fin n => (x i : ZMod (primePowModulus p k : ℕ))) =
    (matrixMod A (primePowModulus p k)).mulVec
      ((matrixMod B (primePowModulus p k)).mulVec
        (fun i : Fin n => (x i : ZMod (primePowModulus p k : ℕ))))
  rw [show matrixMod (A * B) (primePowModulus p k) =
      matrixMod A (primePowModulus p k) * matrixMod B (primePowModulus p k) by
    simpa [matrixMod] using
      (Matrix.map_mul_intCast
        (α := ZMod (primePowModulus p k : ℕ)) A B)]
  ext i
  simp [Matrix.mulVec_mulVec]

lemma matrixModLinearMap_ker_left_mul_isUnit
    (A P : Matrix (Fin n) (Fin n) ℤ)
    (p k : ℕ) [Fact (Nat.Prime p)] (hP : IsUnit P) :
    LinearMap.ker (matrixModLinearMap (n := n) (P * A) p k) =
      LinearMap.ker (matrixModLinearMap (n := n) A p k) := by
  ext x
  constructor
  · intro hx
    have hdet : IsUnit P.det := by
      rwa [Matrix.isUnit_iff_isUnit_det] at hP
    have hx' :
        matrixModLinearMap (n := n) (P⁻¹ * (P * A)) p k x = 0 := by
      rw [matrixModLinearMap_mul_apply]
      rw [hx]
      simp
    have hmul : P⁻¹ * (P * A) = A := by
      rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul P hdet]
      simp
    simpa [hmul] using hx'
  · intro hx
    rw [LinearMap.mem_ker] at hx ⊢
    rw [matrixModLinearMap_mul_apply, hx]
    simp

lemma matrixModLinearMap_ker_mul_right_isUnit
    (A Q : Matrix (Fin n) (Fin n) ℤ)
    (p k : ℕ) [Fact (Nat.Prime p)] (hQ : IsUnit Q) :
    LinearMap.ker (matrixModLinearMap (n := n) (A * Q) p k) =
      Submodule.map (intMatrixLinearEquivOfIsUnit Q hQ).symm.toLinearMap
        (LinearMap.ker (matrixModLinearMap (n := n) A p k)) := by
  ext x
  let e := intMatrixLinearEquivOfIsUnit Q hQ
  constructor
  · intro hx
    change matrixModLinearMap (n := n) (A * Q) p k x = 0 at hx
    refine ⟨e x, ?_, ?_⟩
    · change matrixModLinearMap (n := n) A p k (e x) = 0
      rw [matrixModLinearMap_mul_apply] at hx
      have hQx :
          matrixModLinearMap (n := n) Q p k x =
            fun i : Fin n => ((Q.mulVec x) i : ZMod (primePowModulus p k : ℕ)) := by
        ext i
        simp [matrixModLinearMap, matrixMod, Matrix.mulVec, dotProduct]
      rw [hQx] at hx
      simpa [matrixModLinearMap, Matrix.toLin'_apply] using hx
    · exact e.symm_apply_apply x
  · intro hx
    rcases hx with ⟨y, hy, hxy⟩
    change matrixModLinearMap (n := n) A p k y = 0 at hy
    change matrixModLinearMap (n := n) (A * Q) p k x = 0
    rw [matrixModLinearMap_mul_apply]
    have hQx : Matrix.toLin' Q x = y := by
      rw [← hxy]
      exact e.apply_symm_apply y
    have hQx_mod :
        matrixModLinearMap (n := n) Q p k x =
          fun i : Fin n => ((Matrix.toLin' Q x) i :
            ZMod (primePowModulus p k : ℕ)) := by
      ext i
      simp [matrixModLinearMap, matrixMod, Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
    rw [hQx_mod, hQx]
    simpa [matrixModLinearMap] using hy

lemma matrixModLinearMap_ker_left_right_mul_isUnit
    (A P Q : Matrix (Fin n) (Fin n) ℤ)
    (p k : ℕ) [Fact (Nat.Prime p)] (hP : IsUnit P) (hQ : IsUnit Q) :
    LinearMap.ker (matrixModLinearMap (n := n) (P * A * Q) p k) =
      Submodule.map (intMatrixLinearEquivOfIsUnit Q hQ).symm.toLinearMap
        (LinearMap.ker (matrixModLinearMap (n := n) A p k)) := by
  rw [Matrix.mul_assoc]
  rw [
    matrixModLinearMap_ker_left_mul_isUnit (n := n) (A * Q) P p k hP,
    matrixModLinearMap_ker_mul_right_isUnit (n := n) A Q p k hQ]

/-- The ambient quotient index of the kernel of `x ↦ A x mod p^k` is invariant
under integral unimodular row and column operations.  This is the normal-form
transport needed before reducing the local-dual denominator index to the
diagonal/Smith case. -/
lemma matrixModLinearMap_ker_left_right_mul_quotient_card_eq
    (A P Q : Matrix (Fin n) (Fin n) ℤ)
    (p k : ℕ) [Fact (Nat.Prime p)] (hP : IsUnit P) (hQ : IsUnit Q) :
    Nat.card
        ((Fin n → ℤ) ⧸
          LinearMap.ker (matrixModLinearMap (n := n) (P * A * Q) p k)) =
      Nat.card
        ((Fin n → ℤ) ⧸
          LinearMap.ker (matrixModLinearMap (n := n) A p k)) := by
  rw [matrixModLinearMap_ker_left_right_mul_isUnit (n := n) A P Q p k hP hQ]
  exact coordinateSubmodule_quotient_card_eq_map_linearEquiv
    (n := n) (LinearMap.ker (matrixModLinearMap (n := n) A p k))
    (intMatrixLinearEquivOfIsUnit Q hQ).symm

/-- A sharper unit-times-prime-power diagonal kernel criterion: diagonal
entries with exponent exactly `k` are already zero modulo `p^k`, so their unit
factor need not be a unit modulo `p^k`.  Unit certificates are only required
for the nonzero modulo-`p^k` diagonal entries `v_i < k`. -/
lemma matrixModLinearMap_ker_eq_diagonal_units_prime_pows_of_lt
    (p k : ℕ) [Fact (Nat.Prime p)]
    (u : Fin n → ℤ) (v : Fin n → ℕ) (hv : ∀ i, v i ≤ k)
    (hunit : ∀ i : Fin n, v i < k →
      IsUnit (((u i : ℤ) : ZMod (primePowModulus p k : ℕ)))) :
    LinearMap.ker
        (matrixModLinearMap (n := n)
          (Matrix.diagonal (fun i : Fin n => u i * (p ^ v i : ℤ))) p k) =
      diagonalPrimePowCoordinateSubmodule (n := n) p k v := by
  let m : ℕ+ := primePowModulus p k
  ext x
  rw [mem_diagonalPrimePowCoordinateSubmodule_iff, LinearMap.mem_ker]
  constructor
  · intro hx i
    have hi := congr_fun hx i
    change ((matrixMod (Matrix.diagonal fun i : Fin n => u i * (p ^ v i : ℤ)) m).mulVec
        (fun i : Fin n => (x i : ZMod (m : ℕ)))) i = 0 at hi
    by_cases hlt : v i < k
    · have hzeroUnit :
          (((u i : ℤ) : ZMod (m : ℕ)) *
            (((p ^ v i : ℤ) * x i : ℤ) : ZMod (m : ℕ))) = 0 := by
        simpa [matrixMod, Matrix.mulVec_diagonal, m, mul_assoc] using hi
      have hzero :
          (((p ^ v i : ℤ) * x i : ℤ) : ZMod (primePowModulus p k : ℕ)) = 0 := by
        simpa [m] using (IsUnit.mul_right_eq_zero (hunit i hlt)).mp hzeroUnit
      exact (zmod_pow_mul_eq_zero_iff_of_le p k (v i) (hv i) (x i)).mp hzero
    · have htop : v i = k := le_antisymm (hv i) (Nat.le_of_not_gt hlt)
      have hmod : (primePowModulus p (k - v i) : ℕ) = 1 := by
        simp [primePowModulus, htop]
      change ((x i : ℤ) : ZMod (primePowModulus p (k - v i) : ℕ)) = 0
      rw [hmod]
      exact Subsingleton.elim _ _
  · intro hx
    ext i
    have hzero :=
      (zmod_pow_mul_eq_zero_iff_of_le p k (v i) (hv i) (x i)).mpr (hx i)
    change ((matrixMod (Matrix.diagonal fun i : Fin n => u i * (p ^ v i : ℤ)) m).mulVec
        (fun i : Fin n => (x i : ZMod (m : ℕ)))) i = 0
    have hzeroUnit :
        (((u i : ℤ) : ZMod (m : ℕ)) *
          (((p ^ v i : ℤ) * x i : ℤ) : ZMod (m : ℕ))) = 0 := by
      simp [m, hzero]
    simpa [matrixMod, Matrix.mulVec_diagonal, m, mul_assoc] using hzeroUnit

/-- The diagonal denominator subquotient has the expected product cardinal.

For `E = {x | x_i ≡ 0 mod p^(k-v_i)}` and `D = p^kℤ^n`, the quotient
`E / (D ∩ E)` has one independent factor of size `p^(v_i)` in each
coordinate. -/
lemma diagonalPrimePowCoordinateSubmodule_subquotient_card
    (p k : ℕ) [Fact (Nat.Prime p)]
    (v : Fin n → ℕ) (hv : ∀ i, v i ≤ k) :
    Nat.card (diagonalPrimePowCoordinateSubmodule (n := n) p k v ⧸
      (primePowCoordinateSubmodule (n := n) p k).comap
        (diagonalPrimePowCoordinateSubmodule (n := n) p k v).subtype) =
      p ^ (∑ i : Fin n, v i) := by
  classical
  let E : Submodule ℤ (Fin n → ℤ) :=
    diagonalPrimePowCoordinateSubmodule (n := n) p k v
  let D : Submodule ℤ (Fin n → ℤ) := primePowCoordinateSubmodule (n := n) p k
  let N : Submodule ℤ E := D.comap E.subtype
  let scaleToE : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℤ) :=
    Matrix.toLin' (Matrix.diagonal fun i : Fin n => (p ^ (k - v i) : ℤ))
  have scaleToE_mem : ∀ z, scaleToE z ∈ E := by
    intro z
    change scaleToE z ∈ diagonalPrimePowCoordinateSubmodule (n := n) p k v
    rw [show scaleToE z =
        (fun i : Fin n => (p ^ (k - v i) : ℤ) * z i) by
      ext i
      simp [scaleToE, Matrix.toLin'_apply, Matrix.mulVec_diagonal]]
    rw [mem_diagonalPrimePowCoordinateSubmodule_iff]
    intro i
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact ⟨z i, rfl⟩
  let toEMap : (Fin n → ℤ) →ₗ[ℤ] E :=
    LinearMap.codRestrict E scaleToE scaleToE_mem
  have toEMap_inj : Function.Injective toEMap := by
    intro x y hxy
    ext i
    have hi := congr_fun (congrArg Subtype.val hxy) i
    change (scaleToE x) i = (scaleToE y) i at hi
    change
      ((Matrix.diagonal fun i : Fin n => (p ^ (k - v i) : ℤ)).mulVec x) i =
        ((Matrix.diagonal fun i : Fin n => (p ^ (k - v i) : ℤ)).mulVec y) i at hi
    rw [Matrix.mulVec_diagonal, Matrix.mulVec_diagonal] at hi
    have hp_ne : (p ^ (k - v i) : ℤ) ≠ 0 := by
      have hp_pos : (0 : ℤ) < (p ^ (k - v i) : ℕ) := by
        exact_mod_cast (pow_pos (Fact.out : Nat.Prime p).pos (k - v i))
      exact ne_of_gt hp_pos
    exact mul_left_cancel₀ hp_ne hi
  have toEMap_surj : Function.Surjective toEMap := by
    intro x
    have hx : ∀ i : Fin n, (p ^ (k - v i) : ℤ) ∣ (x : Fin n → ℤ) i := by
      intro i
      have hi := (mem_diagonalPrimePowCoordinateSubmodule_iff
        (n := n) p k v (x : Fin n → ℤ)).mp x.2 i
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hi
      simpa [primePowModulus] using hi
    choose z hz using hx
    refine ⟨z, ?_⟩
    apply Subtype.ext
    change scaleToE z = x
    ext i
    simp [scaleToE, Matrix.toLin'_apply, Matrix.mulVec_diagonal, (hz i).symm]
  let toE : (Fin n → ℤ) ≃ₗ[ℤ] E :=
    LinearEquiv.ofBijective toEMap ⟨toEMap_inj, toEMap_surj⟩
  let scaleToN_E : (Fin n → ℤ) →ₗ[ℤ] E :=
    LinearMap.codRestrict E (LinearMap.lsmul ℤ (Fin n → ℤ) (p ^ k : ℤ))
      (fun z =>
        (primePowCoordinateSubmodule_le_diagonalPrimePowCoordinateSubmodule
          (n := n) p k v hv) ⟨z, rfl⟩)
  have scaleToN_mem : ∀ z, scaleToN_E z ∈ N := by
    intro z
    exact ⟨z, rfl⟩
  let toNMap : (Fin n → ℤ) →ₗ[ℤ] N :=
    LinearMap.codRestrict N scaleToN_E scaleToN_mem
  have toNMap_inj : Function.Injective toNMap := by
    intro x y hxy
    ext i
    have hi := congr_fun (congrArg (fun z : N => ((z : E) : Fin n → ℤ)) hxy) i
    have hp_ne : (p ^ k : ℤ) ≠ 0 := by
      have hp_pos : (0 : ℤ) < (p ^ k : ℕ) := by
        exact_mod_cast (pow_pos (Fact.out : Nat.Prime p).pos k)
      exact ne_of_gt hp_pos
    exact mul_left_cancel₀ hp_ne hi
  have toNMap_surj : Function.Surjective toNMap := by
    intro y
    rcases y.2 with ⟨z, hz⟩
    refine ⟨z, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    ext i
    exact congr_fun hz i
  let toN : (Fin n → ℤ) ≃ₗ[ℤ] N :=
    LinearEquiv.ofBijective toNMap ⟨toNMap_inj, toNMap_surj⟩
  let e : E ≃ₗ[ℤ] N := toE.symm.trans toN
  let bE : Module.Basis (Fin n) ℤ E := (Pi.basisFun ℤ (Fin n)).map toE
  let f : E →ₗ[ℤ] E := N.subtype ∘ₗ (e : E →ₗ[ℤ] N)
  have hf_basis : ∀ i : Fin n, f (bE i) = (p ^ v i : ℤ) • bE i := by
    intro i
    apply Subtype.ext
    ext j
    by_cases hji : j = i
    · subst j
      have hpowNat : p ^ k = p ^ v i * p ^ (k - v i) := by
        rw [← Nat.pow_add, Nat.add_sub_of_le (hv i)]
      have hpowInt : (p ^ k : ℤ) =
          (p ^ v i : ℤ) * (p ^ (k - v i) : ℤ) := by
        exact_mod_cast hpowNat
      simp [f, e, bE, toE, toEMap, toN, toNMap, scaleToN_E, scaleToE,
        Matrix.toLin'_apply, hpowInt]
    · simp [f, e, bE, toE, toEMap, toN, toNMap, scaleToN_E, scaleToE,
        Matrix.toLin'_apply, Pi.basisFun, hji]
  have hmatrix :
      LinearMap.toMatrix bE bE f =
        Matrix.diagonal (fun i : Fin n => (p ^ v i : ℤ)) := by
    ext i j
    rw [LinearMap.toMatrix_apply, hf_basis, map_smul, bE.repr_self,
      Finsupp.smul_single, smul_eq_mul, mul_one]
    by_cases hij : i = j
    · subst i
      rw [Matrix.diagonal_apply_eq, Finsupp.single_eq_same]
    · rw [Matrix.diagonal_apply_ne _ hij, Finsupp.single_eq_of_ne hij]
  have hcard := (Submodule.natAbs_det_equiv N e).symm
  change Nat.card (E ⧸ N) = p ^ (∑ i : Fin n, v i)
  rw [hcard]
  change (LinearMap.det f).natAbs = p ^ (∑ i : Fin n, v i)
  rw [← LinearMap.det_toMatrix bE f, hmatrix, Matrix.det_diagonal]
  have hnonneg : 0 ≤ ∏ i : Fin n, (p ^ v i : ℤ) := by
    exact Finset.prod_nonneg fun i _ =>
      pow_nonneg (Int.natCast_nonneg p) (v i)
  apply Nat.cast_injective (R := ℤ)
  rw [Int.natAbs_of_nonneg hnonneg]
  change (∏ i : Fin n, (p ^ v i : ℤ)) =
    ((p ^ (∑ i : Fin n, v i) : ℕ) : ℤ)
  exact_mod_cast (Finset.prod_pow_eq_pow_sum Finset.univ v p)

/-- The coordinate submodule cut out by Schulze--Pillot's local-dual pairing
condition: all pairings with integral lattice vectors vanish modulo `p^k`.

This is the purely coordinate integral model of the condition
`d ∈ p^k L_p# ∩ L`; the equality with
`pairingMatrixLocalDualCoordinateSubmodule` below turns the source-side pairing
condition into the matrix-kernel condition used by the finite quotient count. -/
def localDualPairingCoordinateSubmodule
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] :
    Submodule ℤ (Fin n → ℤ) where
  carrier := {d | ∀ x : Fin n → ℤ,
    ((L.bilinearFormValue x d : ℤ) :
      ZMod (primePowModulus p k : ℕ)) = 0}
  zero_mem' := by
    intro x
    simp [bilinearFormValue]
  add_mem' := by
    intro d e hd he x
    have hB :
        L.bilinearFormValue x (d + e) =
          L.bilinearFormValue x d + L.bilinearFormValue x e := by
      simp [bilinearFormValue, Matrix.mulVec_add, dotProduct,
        Finset.sum_add_distrib, mul_add]
    rw [hB]
    simp [hd x, he x]
  smul_mem' := by
    intro a d hd x
    have hB :
        L.bilinearFormValue x (a • d) =
          a * L.bilinearFormValue x d := by
      simp [bilinearFormValue, Matrix.mulVec, dotProduct, Finset.mul_sum,
        mul_assoc, mul_comm, mul_left_comm]
    rw [hB]
    simp [hd x]

lemma mem_localDualPairingCoordinateSubmodule_iff
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (d : Fin n → ℤ) :
    d ∈ localDualPairingCoordinateSubmodule L p k ↔
      ∀ x : Fin n → ℤ,
        ((L.bilinearFormValue x d : ℤ) :
          ZMod (primePowModulus p k : ℕ)) = 0 := Iff.rfl

lemma padicInt_primePow_dvd_intCast_iff_zmod_eq_zero
    (p k : ℕ) [Fact (Nat.Prime p)] (a : ℤ) :
    ((p : ℤ_[p]) ^ k ∣ (a : ℤ_[p])) ↔
      ((a : ℤ) : ZMod (primePowModulus p k : ℕ)) = 0 := by
  rw [PadicInt.pow_p_dvd_int_iff]
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  rfl

/-- The p-adic pairing-divisibility condition expected from membership in
`p^k L_p# ∩ L`, written in the current coordinate model. -/
def localDualPadicPairingCondition
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (d : Fin n → ℤ) : Prop :=
  ∀ x : Fin n → ℤ,
    ((p : ℤ_[p]) ^ k ∣
      ((L.bilinearFormValue x d : ℤ) : ℤ_[p]))

lemma localDualPadicPairingCondition_iff_pairing_zmod_zero
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (d : Fin n → ℤ) :
    localDualPadicPairingCondition L p k d ↔
      ∀ x : Fin n → ℤ,
        ((L.bilinearFormValue x d : ℤ) :
          ZMod (primePowModulus p k : ℕ)) = 0 := by
  constructor
  · intro h x
    exact (padicInt_primePow_dvd_intCast_iff_zmod_eq_zero p k
      (L.bilinearFormValue x d)).mp (h x)
  · intro h x
    exact (padicInt_primePow_dvd_intCast_iff_zmod_eq_zero p k
      (L.bilinearFormValue x d)).mpr (h x)

lemma mem_localDualPairingCoordinateSubmodule_iff_padic_pairingCondition
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (d : Fin n → ℤ) :
    d ∈ localDualPairingCoordinateSubmodule L p k ↔
      localDualPadicPairingCondition L p k d := by
  rw [mem_localDualPairingCoordinateSubmodule_iff,
    localDualPadicPairingCondition_iff_pairing_zmod_zero]

/-- Cast an integral coordinate vector into the `p`-adic scalar extension. -/
def integralVectorToPadic (p : ℕ) [Fact (Nat.Prime p)]
    (x : Fin n → ℤ) : Fin n → ℤ_[p] :=
  fun i => (x i : ℤ_[p])

/-- Cast a vector over the local integer ring into the `p`-adic field. -/
def padicIntVectorToPadic (p : ℕ) [Fact (Nat.Prime p)]
    (x : Fin n → ℤ_[p]) : Fin n → ℚ_[p] :=
  fun i => (x i : ℚ_[p])

/-- The form matrix over the `p`-adic field. -/
def pairingMatrix_padicField (L : PositiveDefiniteIntegralLattice n)
    (p : ℕ) [Fact (Nat.Prime p)] : Matrix (Fin n) (Fin n) ℚ_[p] :=
  (L.pairingMatrix_padic p).map PadicInt.Coe.ringHom

/-- The associated-bilinear Gram matrix over the local integer ring. -/
def polarGramMatrix_padic (L : PositiveDefiniteIntegralLattice n)
    (p : ℕ) [Fact (Nat.Prime p)] : Matrix (Fin n) (Fin n) ℤ_[p] :=
  L.polarGramMatrix.map (Int.cast : ℤ → ℤ_[p])

/-- The associated-bilinear Gram matrix over the `p`-adic field. -/
def polarGramMatrix_padicField (L : PositiveDefiniteIntegralLattice n)
    (p : ℕ) [Fact (Nat.Prime p)] : Matrix (Fin n) (Fin n) ℚ_[p] :=
  L.polarGramMatrix.map (Int.cast : ℤ → ℚ_[p])

lemma polarGramMatrix_padic_eq_two_smul_pairingMatrix_padic
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    L.polarGramMatrix_padic p = (2 : ℤ_[p]) • L.pairingMatrix_padic p := by
  ext i j
  simp [polarGramMatrix_padic, pairingMatrix_padic, polarGramMatrix,
    Matrix.transpose_apply, L.form_symm.apply, two_mul]

lemma polarGramMatrix_padicField_eq_two_smul_pairingMatrix_padicField
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    L.polarGramMatrix_padicField p =
      (2 : ℚ_[p]) • L.pairingMatrix_padicField p := by
  ext i j
  simp [polarGramMatrix_padicField, pairingMatrix_padicField, pairingMatrix_padic,
    polarGramMatrix, Matrix.transpose_apply, L.form_symm.apply, two_mul]

lemma two_mul_mem_padicInt_subring_iff_of_ne_two
    (p : ℕ) [Fact (Nat.Prime p)] (hp_two : p ≠ 2) (z : ℚ_[p]) :
    (2 : ℚ_[p]) * z ∈ PadicInt.subring p ↔ z ∈ PadicInt.subring p := by
  have hp_not_dvd_two : ¬ p ∣ 2 := by
    intro hp_dvd
    have hp_eq_two_rev : 2 = p :=
      (Nat.Prime.dvd_iff_eq Nat.prime_two (Fact.out : Nat.Prime p).ne_one).mp
        hp_dvd
    exact hp_two hp_eq_two_rev.symm
  have hpcoprime : Nat.Coprime p 2 :=
    (Fact.out : Nat.Prime p).coprime_iff_not_dvd.mpr hp_not_dvd_two
  have htwo_norm : ‖(2 : ℚ_[p])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.mpr hpcoprime
  rw [PadicInt.mem_subring_iff, PadicInt.mem_subring_iff, norm_mul,
    htwo_norm, one_mul]

lemma two_isUnit_padicInt_of_ne_two
    (p : ℕ) [Fact (Nat.Prime p)] (hp_two : p ≠ 2) :
    IsUnit (2 : ℤ_[p]) := by
  rw [PadicInt.isUnit_iff]
  have hcoprime : Nat.Coprime p 2 :=
    (Fact.out : Nat.Prime p).coprime_iff_not_dvd.mpr fun hp_dvd =>
    hp_two ((Nat.dvd_prime Nat.prime_two).mp hp_dvd |>.resolve_left
      (Fact.out : Nat.Prime p).ne_one)
  exact (PadicInt.norm_natCast_eq_one_iff (p := p)).2 hcoprime

/-- The rational `p`-adic quadratic value in the current coordinate model. -/
def quadForm_padicField (L : PositiveDefiniteIntegralLattice n)
    (p : ℕ) [Fact (Nat.Prime p)] (y : Fin n → ℚ_[p]) : ℚ_[p] :=
  dotProduct y ((L.pairingMatrix_padicField p).mulVec y)

/-- A field-valued vector belongs to the local dual lattice `L_p#` when its
pairing with every standard integral basis vector is integral.  In the based
coordinate model this is exactly the condition that `F y` is coordinatewise
in `ℤ_p`. -/
def IsLocalDualPadicVector (L : PositiveDefiniteIntegralLattice n)
    (p : ℕ) [Fact (Nat.Prime p)] (y : Fin n → ℚ_[p]) : Prop :=
  ∀ i : Fin n, (L.pairingMatrix_padicField p).mulVec y i ∈ PadicInt.subring p

/-- The local dual lattice `L_p#` as a `ℤ_p`-submodule of the local rational
vector space. -/
def localDualPadicSubmodule
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    Submodule ℤ_[p] (Fin n → ℚ_[p]) where
  carrier := {y | L.IsLocalDualPadicVector p y}
  zero_mem' := by
    intro i
    simp [pairingMatrix_padicField, Matrix.mulVec]
  add_mem' := by
    intro x y hx hy i
    have h := (PadicInt.subring p).add_mem (hx i) (hy i)
    simpa [IsLocalDualPadicVector, Matrix.mulVec] using h
  smul_mem' := by
    intro a y hy i
    have h := (PadicInt.subring p).mul_mem a.property (hy i)
    change (∑ j, L.pairingMatrix_padicField p i j * ((a : ℚ_[p]) * y j)) ∈
      PadicInt.subring p
    rw [show (∑ j, L.pairingMatrix_padicField p i j * ((a : ℚ_[p]) * y j)) =
      (a : ℚ_[p]) * ∑ j, L.pairingMatrix_padicField p i j * y j by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring]
    exact h

/-- Membership in the source-side dual lattice formed with the associated
bilinear form `b(x,y) = Q(x+y)-Q(x)-Q(y)`, whose matrix is `2F`. -/
def IsAssociatedBilinearDualPadicVector (L : PositiveDefiniteIntegralLattice n)
    (p : ℕ) [Fact (Nat.Prime p)] (y : Fin n → ℚ_[p]) : Prop :=
  ∀ i : Fin n, (L.polarGramMatrix_padicField p).mulVec y i ∈ PadicInt.subring p

/-- Schulze--Pillot's local dual, formed using the associated bilinear
matrix `2F` rather than the half-polar matrix `F`. -/
def associatedBilinearDualPadicSubmodule
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    Submodule ℤ_[p] (Fin n → ℚ_[p]) where
  carrier := {y | L.IsAssociatedBilinearDualPadicVector p y}
  zero_mem' := by
    intro i
    simp [polarGramMatrix_padicField, Matrix.mulVec]
  add_mem' := by
    intro x y hx hy i
    have h := (PadicInt.subring p).add_mem (hx i) (hy i)
    simpa [IsAssociatedBilinearDualPadicVector, Matrix.mulVec] using h
  smul_mem' := by
    intro a y hy i
    have h := (PadicInt.subring p).mul_mem a.property (hy i)
    change (∑ j, L.polarGramMatrix_padicField p i j * ((a : ℚ_[p]) * y j)) ∈
      PadicInt.subring p
    rw [show (∑ j, L.polarGramMatrix_padicField p i j * ((a : ℚ_[p]) * y j)) =
      (a : ℚ_[p]) * ∑ j, L.polarGramMatrix_padicField p i j * y j by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring]
    exact h

lemma isAssociatedBilinearDualPadicVector_iff_of_ne_two
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (hp_two : p ≠ 2) (y : Fin n → ℚ_[p]) :
    L.IsAssociatedBilinearDualPadicVector p y ↔
      L.IsLocalDualPadicVector p y := by
  unfold IsAssociatedBilinearDualPadicVector IsLocalDualPadicVector
  rw [L.polarGramMatrix_padicField_eq_two_smul_pairingMatrix_padicField p]
  simp only [Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul]
  exact forall_congr' fun i =>
    two_mul_mem_padicInt_subring_iff_of_ne_two p hp_two _

/-- Away from `2`, the source associated-bilinear dual and the current
half-polar dual are the same local lattice. -/
lemma associatedBilinearDualPadicSubmodule_eq_localDualPadicSubmodule_of_ne_two
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (hp_two : p ≠ 2) :
    associatedBilinearDualPadicSubmodule L p =
      localDualPadicSubmodule L p := by
  ext y
  change L.IsAssociatedBilinearDualPadicVector p y ↔
    L.IsLocalDualPadicVector p y
  exact L.isAssociatedBilinearDualPadicVector_iff_of_ne_two p hp_two y

/-- The exact source condition `p^k L_p# ⊆ L_p`. -/
def IsHenselLatticeDepth (L : PositiveDefiniteIntegralLattice n)
    (p k : ℕ) [Fact (Nat.Prime p)] : Prop :=
  ∀ y : Fin n → ℚ_[p], L.IsLocalDualPadicVector p y →
    ∀ i : Fin n, (p : ℚ_[p]) ^ k * y i ∈ PadicInt.subring p

/-- The exact source condition `p^k Q(L_p#) ⊆ p ℤ_p`. -/
def IsHenselQuadraticDepth (L : PositiveDefiniteIntegralLattice n)
    (p k : ℕ) [Fact (Nat.Prime p)] : Prop :=
  ∀ y : Fin n → ℚ_[p], L.IsLocalDualPadicVector p y →
    ∃ a : ℤ_[p],
      (p : ℚ_[p]) ^ k * L.quadForm_padicField p y =
        (((p : ℤ_[p]) * a : ℤ_[p]) : ℚ_[p])

/-- The source lattice-depth condition using the associated-bilinear dual. -/
def IsAssociatedBilinearHenselLatticeDepth (L : PositiveDefiniteIntegralLattice n)
    (p k : ℕ) [Fact (Nat.Prime p)] : Prop :=
  ∀ y : Fin n → ℚ_[p], L.IsAssociatedBilinearDualPadicVector p y →
    ∀ i : Fin n, (p : ℚ_[p]) ^ k * y i ∈ PadicInt.subring p

/-- The source quadratic-depth condition using the associated-bilinear dual. -/
def IsAssociatedBilinearHenselQuadraticDepth (L : PositiveDefiniteIntegralLattice n)
    (p k : ℕ) [Fact (Nat.Prime p)] : Prop :=
  ∀ y : Fin n → ℚ_[p], L.IsAssociatedBilinearDualPadicVector p y →
    ∃ a : ℤ_[p],
      (p : ℚ_[p]) ^ k * L.quadForm_padicField p y =
        (((p : ℤ_[p]) * a : ℤ_[p]) : ℚ_[p])

lemma isAssociatedBilinearHenselQuadraticDepth_iff_of_ne_two
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hp_two : p ≠ 2) :
    L.IsAssociatedBilinearHenselQuadraticDepth p k ↔
      L.IsHenselQuadraticDepth p k := by
  unfold IsAssociatedBilinearHenselQuadraticDepth IsHenselQuadraticDepth
  constructor
  · intro h y hy
    exact h y ((L.isAssociatedBilinearDualPadicVector_iff_of_ne_two
      p hp_two y).mpr hy)
  · intro h y hy
    exact h y ((L.isAssociatedBilinearDualPadicVector_iff_of_ne_two
      p hp_two y).mp hy)

lemma isLocalDualPadicVector_two_smul_of_isAssociatedBilinearDualPadicVector
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (y : Fin n → ℚ_[p])
    (hy : L.IsAssociatedBilinearDualPadicVector p y) :
    L.IsLocalDualPadicVector p ((2 : ℚ_[p]) • y) := by
  intro i
  have hi := hy i
  rw [L.polarGramMatrix_padicField_eq_two_smul_pairingMatrix_padicField p,
    Matrix.smul_mulVec] at hi
  simpa [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, Finset.mul_sum,
    mul_assoc, mul_comm, mul_left_comm] using hi

lemma quadForm_padicField_two_smul
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (y : Fin n → ℚ_[p]) :
    L.quadForm_padicField p ((2 : ℚ_[p]) • y) =
      (4 : ℚ_[p]) * L.quadForm_padicField p y := by
  simp only [quadForm_padicField, dotProduct, Matrix.mulVec, Pi.smul_apply,
    smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  calc
    (∑ x, 2 * y i * (L.pairingMatrix_padicField p i x * (2 * y x))) =
        ∑ x, (4 * y i) * (L.pairingMatrix_padicField p i x * y x) := by
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = 4 * (y i * ∑ x, L.pairingMatrix_padicField p i x * y x) := by
      rw [← Finset.mul_sum]
      ring

/-- At the dyadic prime, two extra powers convert the current half-polar
quadratic-depth condition into Schulze--Pillot's associated-bilinear one. -/
lemma IsHenselQuadraticDepth.associatedBilinear_add_two_dyadic
    (L : PositiveDefiniteIntegralLattice n) (k : ℕ)
    (h : L.IsHenselQuadraticDepth 2 k) :
    L.IsAssociatedBilinearHenselQuadraticDepth 2 (k + 2) := by
  intro y hy
  obtain ⟨a, ha⟩ := h ((2 : ℚ_[2]) • y)
    (L.isLocalDualPadicVector_two_smul_of_isAssociatedBilinearDualPadicVector
      2 y hy)
  refine ⟨a, ?_⟩
  calc
    (2 : ℚ_[2]) ^ (k + 2) * L.quadForm_padicField 2 y =
        (2 : ℚ_[2]) ^ k *
          L.quadForm_padicField 2 ((2 : ℚ_[2]) • y) := by
      rw [L.quadForm_padicField_two_smul 2 y, pow_add]
      norm_num
      ring
    _ = ((((2 : ℤ_[2]) * a : ℤ_[2]) : ℚ_[2])) := ha

/-- The `ℤ`-linear map casting integral coordinate vectors into the `p`-adic
scalar extension. -/
def integralVectorToPadicLinearMap (p : ℕ) [Fact (Nat.Prime p)] :
    (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℤ_[p]) where
  toFun := integralVectorToPadic (n := n) p
  map_add' := by
    intro x y
    ext i
    simp [integralVectorToPadic]
  map_smul' := by
    intro a x
    ext i
    simp [integralVectorToPadic]

@[simp] lemma integralVectorToPadicLinearMap_apply
    (p : ℕ) [Fact (Nat.Prime p)] (x : Fin n → ℤ) :
    integralVectorToPadicLinearMap (n := n) p x =
      integralVectorToPadic (n := n) p x := rfl

/-- A unimodular matrix over `ℤ_[p]` acts as a linear equivalence on the
`p`-adic coordinate module. -/
noncomputable def padicMatrixLinearEquivOfIsUnit
    (p : ℕ) [Fact (Nat.Prime p)]
    (U : Matrix (Fin n) (Fin n) ℤ_[p]) (hU : IsUnit U) :
    (Fin n → ℤ_[p]) ≃ₗ[ℤ_[p]] (Fin n → ℤ_[p]) := by
  have hdet : IsUnit U.det := by
    rwa [Matrix.isUnit_iff_isUnit_det] at hU
  refine LinearEquiv.ofLinear (Matrix.toLin' U) (Matrix.toLin' U⁻¹) ?_ ?_
  · rw [← Matrix.toLin'_mul, Matrix.mul_nonsing_inv U hdet]
    ext v i
    simp
  · rw [← Matrix.toLin'_mul, Matrix.nonsing_inv_mul U hdet]
    ext v i
    simp

@[simp] lemma padicMatrixLinearEquivOfIsUnit_apply
    (p : ℕ) [Fact (Nat.Prime p)]
    (U : Matrix (Fin n) (Fin n) ℤ_[p]) (hU : IsUnit U)
    (x : Fin n → ℤ_[p]) :
    padicMatrixLinearEquivOfIsUnit (n := n) p U hU x = U.mulVec x := rfl

@[simp] lemma padicMatrixLinearEquivOfIsUnit_symm_apply
    (p : ℕ) [Fact (Nat.Prime p)]
    (U : Matrix (Fin n) (Fin n) ℤ_[p]) (hU : IsUnit U)
    (x : Fin n → ℤ_[p]) :
    (padicMatrixLinearEquivOfIsUnit (n := n) p U hU).symm x = U⁻¹.mulVec x := rfl

/-- The integral preimage of a `p`-adic coordinate submodule. -/
def padicSubmoduleIntegralPreimage
    (p : ℕ) [Fact (Nat.Prime p)]
    (D : Submodule ℤ_[p] (Fin n → ℤ_[p])) :
    Submodule ℤ (Fin n → ℤ) where
  carrier := {x | integralVectorToPadic (n := n) p x ∈ D}
  zero_mem' := by
    change integralVectorToPadic (n := n) p 0 ∈ D
    exact D.zero_mem
  add_mem' := by
    intro x y hx hy
    have hcast :
        integralVectorToPadic (n := n) p (x + y) =
          integralVectorToPadic (n := n) p x +
            integralVectorToPadic (n := n) p y := by
      ext i
      simp [integralVectorToPadic]
    change integralVectorToPadic (n := n) p (x + y) ∈ D
    rw [hcast]
    exact D.add_mem hx hy
  smul_mem' := by
    intro a x hx
    have hcast :
        integralVectorToPadic (n := n) p (a • x) =
          (a : ℤ_[p]) • integralVectorToPadic (n := n) p x := by
      ext i
      simp [integralVectorToPadic]
    change integralVectorToPadic (n := n) p (a • x) ∈ D
    rw [hcast]
    exact D.smul_mem (a : ℤ_[p]) hx

lemma mem_padicSubmoduleIntegralPreimage_iff
    (p : ℕ) [Fact (Nat.Prime p)]
    (D : Submodule ℤ_[p] (Fin n → ℤ_[p])) (x : Fin n → ℤ) :
    x ∈ padicSubmoduleIntegralPreimage (n := n) p D ↔
      integralVectorToPadic (n := n) p x ∈ D := Iff.rfl

lemma padicSubmoduleIntegralPreimage_mkQ_eq_iff
    (p : ℕ) [Fact (Nat.Prime p)]
    (D : Submodule ℤ_[p] (Fin n → ℤ_[p])) (x y : Fin n → ℤ) :
    (padicSubmoduleIntegralPreimage (n := n) p D).mkQ x =
        (padicSubmoduleIntegralPreimage (n := n) p D).mkQ y ↔
      D.mkQ (integralVectorToPadic (n := n) p x) =
        D.mkQ (integralVectorToPadic (n := n) p y) := by
  constructor
  · intro hxy
    change (Submodule.Quotient.mk x :
        (Fin n → ℤ) ⧸ padicSubmoduleIntegralPreimage (n := n) p D) =
      Submodule.Quotient.mk y at hxy
    rw [Submodule.Quotient.eq] at hxy
    change (Submodule.Quotient.mk (integralVectorToPadic (n := n) p x) :
        (Fin n → ℤ_[p]) ⧸ D) =
      Submodule.Quotient.mk (integralVectorToPadic (n := n) p y)
    rw [Submodule.Quotient.eq]
    have hsub :
        integralVectorToPadic (n := n) p (x - y) =
          integralVectorToPadic (n := n) p x -
            integralVectorToPadic (n := n) p y := by
      ext i
      simp [integralVectorToPadic]
    rwa [← hsub]
  · intro hxy
    change (Submodule.Quotient.mk (integralVectorToPadic (n := n) p x) :
        (Fin n → ℤ_[p]) ⧸ D) =
      Submodule.Quotient.mk (integralVectorToPadic (n := n) p y) at hxy
    rw [Submodule.Quotient.eq] at hxy
    change (Submodule.Quotient.mk x :
        (Fin n → ℤ) ⧸ padicSubmoduleIntegralPreimage (n := n) p D) =
      Submodule.Quotient.mk y
    rw [Submodule.Quotient.eq]
    rw [mem_padicSubmoduleIntegralPreimage_iff]
    have hsub :
        integralVectorToPadic (n := n) p (x - y) =
          integralVectorToPadic (n := n) p x -
            integralVectorToPadic (n := n) p y := by
      ext i
      simp [integralVectorToPadic]
    rwa [hsub]

/-- Cast integral coordinate vectors into a fixed `p`-adic quotient. -/
def integralVectorToPadicQuotientLinearMap
    (p : ℕ) [Fact (Nat.Prime p)]
    (D : Submodule ℤ_[p] (Fin n → ℤ_[p])) :
    (Fin n → ℤ) →ₗ[ℤ] ((Fin n → ℤ_[p]) ⧸ D) where
  toFun := fun x => D.mkQ (integralVectorToPadic (n := n) p x)
  map_add' := by
    intro x y
    have hcast :
        integralVectorToPadic (n := n) p (x + y) =
          integralVectorToPadic (n := n) p x +
            integralVectorToPadic (n := n) p y := by
      ext i
      simp [integralVectorToPadic]
    rw [hcast]
    exact map_add D.mkQ
      (integralVectorToPadic (n := n) p x)
      (integralVectorToPadic (n := n) p y)
  map_smul' := by
    intro a x
    have hcast :
        integralVectorToPadic (n := n) p (a • x) =
          (a : ℤ_[p]) • integralVectorToPadic (n := n) p x := by
      ext i
      simp [integralVectorToPadic]
    rw [hcast, map_smul]
    exact Int.cast_smul_eq_zsmul (R := ℤ_[p]) a
      (D.mkQ (integralVectorToPadic (n := n) p x))

@[simp] lemma integralVectorToPadicQuotientLinearMap_apply
    (p : ℕ) [Fact (Nat.Prime p)]
    (D : Submodule ℤ_[p] (Fin n → ℤ_[p])) (x : Fin n → ℤ) :
    integralVectorToPadicQuotientLinearMap (n := n) p D x =
      D.mkQ (integralVectorToPadic (n := n) p x) := rfl

lemma padicSubmoduleIntegralPreimage_le_ker_quotient_cast
    (p : ℕ) [Fact (Nat.Prime p)]
    (D : Submodule ℤ_[p] (Fin n → ℤ_[p])) :
    padicSubmoduleIntegralPreimage (n := n) p D ≤
      LinearMap.ker (integralVectorToPadicQuotientLinearMap (n := n) p D) := by
  intro x hx
  rw [LinearMap.mem_ker]
  change (Submodule.Quotient.mk (integralVectorToPadic (n := n) p x) :
      (Fin n → ℤ_[p]) ⧸ D) = Submodule.Quotient.mk 0
  rw [Submodule.Quotient.eq]
  simpa using ((mem_padicSubmoduleIntegralPreimage_iff (n := n) p D x).mp hx)

/-- The integral-integral model quotient maps to the corresponding `p`-adic quotient by
casting representatives.  The previous equality bridge proves this map is
injective; future local-isometry numerator transport can factor through this
map before using the `ℤ_[p]`-linear quotient equivalence. -/
def padicSubmoduleIntegralPreimageQuotientMap
    (p : ℕ) [Fact (Nat.Prime p)]
    (D : Submodule ℤ_[p] (Fin n → ℤ_[p])) :
    ((Fin n → ℤ) ⧸ padicSubmoduleIntegralPreimage (n := n) p D) →ₗ[ℤ]
      ((Fin n → ℤ_[p]) ⧸ D) :=
  (padicSubmoduleIntegralPreimage (n := n) p D).liftQ
    (integralVectorToPadicQuotientLinearMap (n := n) p D)
    (padicSubmoduleIntegralPreimage_le_ker_quotient_cast (n := n) p D)

set_option backward.isDefEq.respectTransparency false in
@[simp] lemma padicSubmoduleIntegralPreimageQuotientMap_mkQ
    (p : ℕ) [Fact (Nat.Prime p)]
    (D : Submodule ℤ_[p] (Fin n → ℤ_[p])) (x : Fin n → ℤ) :
    padicSubmoduleIntegralPreimageQuotientMap (n := n) p D
        ((padicSubmoduleIntegralPreimage (n := n) p D).mkQ x) =
      D.mkQ (integralVectorToPadic (n := n) p x) := by
  simp [padicSubmoduleIntegralPreimageQuotientMap]

lemma padicSubmoduleIntegralPreimageQuotientMap_injective
    (p : ℕ) [Fact (Nat.Prime p)]
    (D : Submodule ℤ_[p] (Fin n → ℤ_[p])) :
    Function.Injective (padicSubmoduleIntegralPreimageQuotientMap (n := n) p D) := by
  intro q r hqr
  induction q using Quotient.inductionOn with
  | h x =>
      induction r using Quotient.inductionOn with
      | h y =>
          change (padicSubmoduleIntegralPreimage (n := n) p D).mkQ x =
            (padicSubmoduleIntegralPreimage (n := n) p D).mkQ y
          rw [padicSubmoduleIntegralPreimage_mkQ_eq_iff (n := n) p D]
          simpa using hqr

/-- The quotient map induced by an inclusion of `p`-adic submodules. -/
noncomputable def padicSubmoduleQuotientMapOfLE
    {p : ℕ} [Fact (Nat.Prime p)]
    {D E : Submodule ℤ_[p] (Fin n → ℤ_[p])} (hDE : D ≤ E) :
    ((Fin n → ℤ_[p]) ⧸ D) →ₗ[ℤ_[p]] ((Fin n → ℤ_[p]) ⧸ E) :=
  D.mapQ E LinearMap.id hDE

@[simp] lemma padicSubmoduleQuotientMapOfLE_mkQ
    {p : ℕ} [Fact (Nat.Prime p)]
    {D E : Submodule ℤ_[p] (Fin n → ℤ_[p])} (hDE : D ≤ E)
    (x : Fin n → ℤ_[p]) :
    padicSubmoduleQuotientMapOfLE (n := n) hDE (D.mkQ x) = E.mkQ x := rfl

/-- The canonical map from the denominator subquotient into the kernel of the
ambient quotient map. This direction has a useful computation rule on actual
denominator representatives. -/
noncomputable def padicSubmoduleSubquotientToQuotientMapKer
    {p : ℕ} [Fact (Nat.Prime p)]
    {D E : Submodule ℤ_[p] (Fin n → ℤ_[p])} (hDE : D ≤ E) :
    (E ⧸ D.comap E.subtype) →ₗ[ℤ_[p]]
      LinearMap.ker (padicSubmoduleQuotientMapOfLE (n := n) hDE) := by
  let f : E →ₗ[ℤ_[p]]
      LinearMap.ker (padicSubmoduleQuotientMapOfLE (n := n) hDE) :=
    { toFun := fun x => ⟨D.mkQ x.1, by
        rw [LinearMap.mem_ker]
        exact (Submodule.Quotient.mk_eq_zero E).mpr x.2⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        simp
      map_smul' := by
        intro a x
        apply Subtype.ext
        simp }
  refine (D.comap E.subtype).liftQ f ?_
  intro x hx
  apply Subtype.ext
  exact (Submodule.Quotient.mk_eq_zero D).mpr hx

@[simp] lemma padicSubmoduleSubquotientToQuotientMapKer_mkQ
    {p : ℕ} [Fact (Nat.Prime p)]
    {D E : Submodule ℤ_[p] (Fin n → ℤ_[p])} (hDE : D ≤ E)
    (x : E) :
    padicSubmoduleSubquotientToQuotientMapKer (n := n) hDE
        ((D.comap E.subtype).mkQ x) =
      ⟨D.mkQ x.1, by
        rw [LinearMap.mem_ker]
        exact (Submodule.Quotient.mk_eq_zero E).mpr x.2⟩ := rfl

lemma padicSubmoduleSubquotientToQuotientMapKer_injective
    {p : ℕ} [Fact (Nat.Prime p)]
    {D E : Submodule ℤ_[p] (Fin n → ℤ_[p])} (hDE : D ≤ E) :
    Function.Injective
      (padicSubmoduleSubquotientToQuotientMapKer (n := n) hDE) := by
  intro q r hqr
  induction q using Quotient.inductionOn with
  | h x =>
    induction r using Quotient.inductionOn with
    | h y =>
      change (Submodule.Quotient.mk x :
          E ⧸ (D.comap E.subtype)) = Submodule.Quotient.mk y
      rw [Submodule.Quotient.eq]
      have hval := congrArg Subtype.val hqr
      change (Submodule.Quotient.mk x.1 :
          (Fin n → ℤ_[p]) ⧸ D) = Submodule.Quotient.mk y.1 at hval
      rw [Submodule.Quotient.eq] at hval
      exact hval

lemma padicSubmoduleSubquotientToQuotientMapKer_surjective
    {p : ℕ} [Fact (Nat.Prime p)]
    {D E : Submodule ℤ_[p] (Fin n → ℤ_[p])} (hDE : D ≤ E) :
    Function.Surjective
      (padicSubmoduleSubquotientToQuotientMapKer (n := n) hDE) := by
  intro q
  let x : Fin n → ℤ_[p] := Quotient.out q.1
  have hxE : x ∈ E := by
    rw [← Submodule.Quotient.mk_eq_zero E]
    calc
      E.mkQ x = padicSubmoduleQuotientMapOfLE (n := n) hDE (D.mkQ x) := rfl
      _ = padicSubmoduleQuotientMapOfLE (n := n) hDE q.1 := by
        exact congrArg
          (padicSubmoduleQuotientMapOfLE (n := n) hDE)
          (Submodule.Quotient.mk_out q.1)
      _ = 0 := LinearMap.mem_ker.mp q.2
  refine ⟨(D.comap E.subtype).mkQ ⟨x, hxE⟩, ?_⟩
  apply Subtype.ext
  exact Submodule.Quotient.mk_out q.1

/-- The kernel of a `p`-adic quotient map is the subquotient of the larger
submodule by the smaller one. -/
noncomputable def padicSubmoduleQuotientMapOfLEKerEquivSubquotient
    {p : ℕ} [Fact (Nat.Prime p)]
    {D E : Submodule ℤ_[p] (Fin n → ℤ_[p])} (hDE : D ≤ E) :
    LinearMap.ker (padicSubmoduleQuotientMapOfLE (n := n) hDE) ≃ₗ[ℤ_[p]]
      E ⧸ D.comap E.subtype :=
  (LinearEquiv.ofBijective
    (padicSubmoduleSubquotientToQuotientMapKer (n := n) hDE)
    ⟨padicSubmoduleSubquotientToQuotientMapKer_injective (n := n) hDE,
      padicSubmoduleSubquotientToQuotientMapKer_surjective (n := n) hDE⟩).symm

lemma padicSubmoduleQuotientMapOfLEKerEquivSubquotient_mkQ
    {p : ℕ} [Fact (Nat.Prime p)]
    {D E : Submodule ℤ_[p] (Fin n → ℤ_[p])} (hDE : D ≤ E)
    (x : E) :
    padicSubmoduleQuotientMapOfLEKerEquivSubquotient (n := n) hDE
        ⟨D.mkQ x.1, by
          rw [LinearMap.mem_ker]
          exact (Submodule.Quotient.mk_eq_zero E).mpr x.2⟩ =
      (D.comap E.subtype).mkQ x := by
  let e := padicSubmoduleQuotientMapOfLEKerEquivSubquotient (n := n) hDE
  apply e.symm.injective
  rw [e.symm_apply_apply]
  exact padicSubmoduleSubquotientToQuotientMapKer_mkQ (n := n) hDE x

lemma padicInt_exists_int_sub_mem_span_primePow
    (p k : ℕ) [Fact (Nat.Prime p)] (a : ℤ_[p]) :
    ∃ z : ℤ, ((p : ℤ_[p]) ^ k ∣ a - (z : ℤ_[p])) := by
  refine ⟨(PadicInt.appr a k : ℤ), ?_⟩
  simpa using (Ideal.mem_span_singleton.mp (PadicInt.appr_spec k a))

lemma padicBilinearFormValue_integral_right
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (x d : Fin n → ℤ) :
    dotProduct (integralVectorToPadic (n := n) p x)
        ((L.pairingMatrix_padic p).mulVec (integralVectorToPadic (n := n) p d)) =
      ((L.bilinearFormValue x d : ℤ) : ℤ_[p]) := by
  simp [integralVectorToPadic, pairingMatrix_padic, bilinearFormValue,
    dotProduct, Matrix.mulVec]

/-- The `p`-adic local-dual denominator cut out by the condition
`p^k ∣ B(x,d)` for all integral coordinate vectors `x`.

This is the local scalar-extension object whose integral-coordinate integral model is
`p^k L_p# ∩ L` in the current based model. -/
def localDualPadicDenominator
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] :
    Submodule ℤ_[p] (Fin n → ℤ_[p]) where
  carrier := {d | ∀ x : Fin n → ℤ,
    ((p : ℤ_[p]) ^ k ∣
      dotProduct (integralVectorToPadic (n := n) p x)
        ((L.pairingMatrix_padic p).mulVec d))}
  zero_mem' := by
    intro x
    simp [dotProduct]
  add_mem' := by
    intro d e hd he x
    have hsum :
        dotProduct (integralVectorToPadic (n := n) p x)
            ((L.pairingMatrix_padic p).mulVec (d + e)) =
          dotProduct (integralVectorToPadic (n := n) p x)
              ((L.pairingMatrix_padic p).mulVec d) +
            dotProduct (integralVectorToPadic (n := n) p x)
              ((L.pairingMatrix_padic p).mulVec e) := by
      simp [Matrix.mulVec_add, dotProduct, Finset.sum_add_distrib, mul_add]
    rw [hsum]
    exact dvd_add (hd x) (he x)
  smul_mem' := by
    intro a d hd x
    have hsmul :
        dotProduct (integralVectorToPadic (n := n) p x)
            ((L.pairingMatrix_padic p).mulVec (a • d)) =
          a * dotProduct (integralVectorToPadic (n := n) p x)
            ((L.pairingMatrix_padic p).mulVec d) := by
      simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]
    rw [hsmul]
    exact dvd_mul_of_dvd_right (hd x) a

lemma mem_localDualPadicDenominator_iff
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (d : Fin n → ℤ_[p]) :
    d ∈ localDualPadicDenominator L p k ↔
      ∀ x : Fin n → ℤ,
        ((p : ℤ_[p]) ^ k ∣
          dotProduct (integralVectorToPadic (n := n) p x)
            ((L.pairingMatrix_padic p).mulVec d)) := Iff.rfl

/-- The source local-dual denominator `p^k Lambda#`, cut out using the
associated-bilinear Gram matrix `2F`. -/
def associatedBilinearDualPadicDenominator
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] :
    Submodule ℤ_[p] (Fin n → ℤ_[p]) where
  carrier := {d | ∀ x : Fin n → ℤ,
    ((p : ℤ_[p]) ^ k ∣
      dotProduct (integralVectorToPadic (n := n) p x)
        ((L.polarGramMatrix_padic p).mulVec d))}
  zero_mem' := by
    intro x
    simp [dotProduct]
  add_mem' := by
    intro d e hd he x
    rw [Matrix.mulVec_add, dotProduct_add]
    exact dvd_add (hd x) (he x)
  smul_mem' := by
    intro a d hd x
    have hsmul :
        dotProduct (integralVectorToPadic (n := n) p x)
            ((L.polarGramMatrix_padic p).mulVec (a • d)) =
          a * dotProduct (integralVectorToPadic (n := n) p x)
            ((L.polarGramMatrix_padic p).mulVec d) := by
      rw [Matrix.mulVec_smul, dotProduct_smul]
      rfl
    rw [hsmul]
    exact dvd_mul_of_dvd_right (hd x) a

lemma mem_associatedBilinearDualPadicDenominator_iff
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (d : Fin n → ℤ_[p]) :
    d ∈ associatedBilinearDualPadicDenominator L p k ↔
      ∀ x : Fin n → ℤ,
        ((p : ℤ_[p]) ^ k ∣
          dotProduct (integralVectorToPadic (n := n) p x)
            ((L.polarGramMatrix_padic p).mulVec d)) := Iff.rfl

/-- At odd primes, the source denominator formed with `2F` is exactly the
current denominator formed with `F`. -/
lemma associatedBilinearDualPadicDenominator_eq_localDualPadicDenominator_of_ne_two
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hp_two : p ≠ 2) :
    associatedBilinearDualPadicDenominator L p k =
      localDualPadicDenominator L p k := by
  ext d
  change (∀ x : Fin n → ℤ,
      ((p : ℤ_[p]) ^ k ∣
        dotProduct (integralVectorToPadic (n := n) p x)
          ((L.polarGramMatrix_padic p).mulVec d))) ↔
    ∀ x : Fin n → ℤ,
      ((p : ℤ_[p]) ^ k ∣
        dotProduct (integralVectorToPadic (n := n) p x)
          ((L.pairingMatrix_padic p).mulVec d))
  rw [L.polarGramMatrix_padic_eq_two_smul_pairingMatrix_padic p]
  have htwo := two_isUnit_padicInt_of_ne_two p hp_two
  apply forall_congr'
  intro x
  have hdot :
      dotProduct (integralVectorToPadic (n := n) p x)
          (((2 : ℤ_[p]) • L.pairingMatrix_padic p).mulVec d) =
        (2 : ℤ_[p]) *
          dotProduct (integralVectorToPadic (n := n) p x)
            ((L.pairingMatrix_padic p).mulVec d) := by
    rw [Matrix.smul_mulVec]
    change (∑ i, integralVectorToPadic (n := n) p x i *
        (2 * (L.pairingMatrix_padic p).mulVec d i)) =
      2 * ∑ i, integralVectorToPadic (n := n) p x i *
        (L.pairingMatrix_padic p).mulVec d i
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hdot]
  exact htwo.dvd_mul_left

/-- At the dyadic prime, the source denominator at depth `k+1` is the current
half-polar denominator at depth `k`. -/
lemma associatedBilinearDualPadicDenominator_succ_eq_localDualPadicDenominator_dyadic
    (L : PositiveDefiniteIntegralLattice n) (k : ℕ) :
    associatedBilinearDualPadicDenominator L 2 (k + 1) =
      localDualPadicDenominator L 2 k := by
  ext d
  change (∀ x : Fin n → ℤ,
      ((2 : ℤ_[2]) ^ (k + 1) ∣
        dotProduct (integralVectorToPadic (n := n) 2 x)
          ((L.polarGramMatrix_padic 2).mulVec d))) ↔
    ∀ x : Fin n → ℤ,
      ((2 : ℤ_[2]) ^ k ∣
        dotProduct (integralVectorToPadic (n := n) 2 x)
          ((L.pairingMatrix_padic 2).mulVec d))
  rw [L.polarGramMatrix_padic_eq_two_smul_pairingMatrix_padic 2]
  apply forall_congr'
  intro x
  have hdot :
      dotProduct (integralVectorToPadic (n := n) 2 x)
          (((2 : ℤ_[2]) • L.pairingMatrix_padic 2).mulVec d) =
        (2 : ℤ_[2]) *
          dotProduct (integralVectorToPadic (n := n) 2 x)
            ((L.pairingMatrix_padic 2).mulVec d) := by
    rw [Matrix.smul_mulVec]
    change (∑ i, integralVectorToPadic (n := n) 2 x i *
        (2 * (L.pairingMatrix_padic 2).mulVec d i)) =
      2 * ∑ i, integralVectorToPadic (n := n) 2 x i *
        (L.pairingMatrix_padic 2).mulVec d i
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hdot]
  simpa [pow_succ, mul_comm] using
    (mul_dvd_mul_iff_left
      (show (2 : ℤ_[2]) ≠ 0 by norm_num)
      (a := (2 : ℤ_[2]))
      (b := (2 : ℤ_[2]) ^ k)
      (c := dotProduct (integralVectorToPadic (n := n) 2 x)
        ((L.pairingMatrix_padic 2).mulVec d)))

lemma associatedBilinearDualPadicDenominator_zero_eq_top
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    associatedBilinearDualPadicDenominator L p 0 = ⊤ := by
  ext d
  simp [associatedBilinearDualPadicDenominator]

lemma mem_localDualPadicDenominator_of_forall_coord_primePow_dvd
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    {d : Fin n → ℤ_[p]} (hd : ∀ i : Fin n, ((p : ℤ_[p]) ^ k ∣ d i)) :
    d ∈ localDualPadicDenominator L p k := by
  rw [mem_localDualPadicDenominator_iff]
  intro x
  have hmul :
      ∀ i : Fin n, ((p : ℤ_[p]) ^ k ∣ ((L.pairingMatrix_padic p).mulVec d) i) := by
    intro i
    rw [Matrix.mulVec, dotProduct]
    exact Finset.dvd_sum fun j _ =>
      dvd_mul_of_dvd_right (hd j) ((L.pairingMatrix_padic p) i j)
  rw [dotProduct]
  exact Finset.dvd_sum fun i _ =>
    dvd_mul_of_dvd_right (hmul i) (integralVectorToPadic (n := n) p x i)

lemma primePow_smul_mem_localDualPadicDenominator
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (v : Fin n → ℤ_[p]) :
    ((p : ℤ_[p]) ^ k) • v ∈ localDualPadicDenominator L p k := by
  refine mem_localDualPadicDenominator_of_forall_coord_primePow_dvd
    (n := n) L p k ?_
  intro i
  exact dvd_mul_right ((p : ℤ_[p]) ^ k) (v i)

lemma exists_integralVectorToPadic_sub_mem_localDualPadicDenominator
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (v : Fin n → ℤ_[p]) :
    ∃ x : Fin n → ℤ,
      v - integralVectorToPadic (n := n) p x ∈
        localDualPadicDenominator L p k := by
  classical
  choose z hz using fun i : Fin n =>
    padicInt_exists_int_sub_mem_span_primePow p k (v i)
  refine ⟨z, ?_⟩
  refine mem_localDualPadicDenominator_of_forall_coord_primePow_dvd
    (n := n) L p k ?_
  intro i
  simpa [Pi.sub_apply, integralVectorToPadic] using hz i

lemma padicSubmoduleIntegralPreimageQuotientMap_surjective_localDualPadicDenominator
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] :
    Function.Surjective
      (padicSubmoduleIntegralPreimageQuotientMap (n := n) p
        (localDualPadicDenominator L p k)) := by
  intro q
  induction q using Quotient.inductionOn with
  | h v =>
      rcases exists_integralVectorToPadic_sub_mem_localDualPadicDenominator
        (n := n) L p k v with ⟨x, hx⟩
      refine ⟨(padicSubmoduleIntegralPreimage (n := n) p
        (localDualPadicDenominator L p k)).mkQ x, ?_⟩
      rw [padicSubmoduleIntegralPreimageQuotientMap_mkQ]
      change (Submodule.Quotient.mk (integralVectorToPadic (n := n) p x) :
          (Fin n → ℤ_[p]) ⧸ localDualPadicDenominator L p k) =
        Submodule.Quotient.mk v
      rw [Submodule.Quotient.eq]
      simpa [sub_eq_add_neg, add_comm] using
        (localDualPadicDenominator L p k).neg_mem hx

lemma mem_localDualPadicDenominator_iff_forall_padic
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (d : Fin n → ℤ_[p]) :
    d ∈ localDualPadicDenominator L p k ↔
      ∀ x : Fin n → ℤ_[p],
        ((p : ℤ_[p]) ^ k ∣
          dotProduct x ((L.pairingMatrix_padic p).mulVec d)) := by
  constructor
  · intro hd x
    let v := (L.pairingMatrix_padic p).mulVec d
    have hbasis : ∀ i : Fin n, ((p : ℤ_[p]) ^ k ∣ v i) := by
      intro i
      have hi := (mem_localDualPadicDenominator_iff L p k d).mp hd
        ((Pi.basisFun ℤ (Fin n)) i)
      have hdot :
          dotProduct (integralVectorToPadic (n := n) p ((Pi.basisFun ℤ (Fin n)) i)) v =
            v i := by
        rw [dotProduct]
        calc
          (∑ j : Fin n,
              integralVectorToPadic (n := n) p ((Pi.basisFun ℤ (Fin n)) i) j *
                v j) =
              integralVectorToPadic (n := n) p ((Pi.basisFun ℤ (Fin n)) i) i *
                v i := by
                exact Finset.sum_eq_single i
                  (by
                    intro b _ hb
                    have hbasis_zero :
                        integralVectorToPadic (n := n) p ((Pi.basisFun ℤ (Fin n)) i) b = 0 := by
                      simp [integralVectorToPadic, Pi.basisFun, hb]
                    rw [hbasis_zero, zero_mul])
                  (by simp)
          _ = v i := by simp [integralVectorToPadic, Pi.basisFun]
      have hi' : ((p : ℤ_[p]) ^ k ∣
          dotProduct (integralVectorToPadic (n := n) p ((Pi.basisFun ℤ (Fin n)) i)) v) := by
        simpa [v] using hi
      rwa [hdot] at hi'
    have hsum :
        dotProduct x ((L.pairingMatrix_padic p).mulVec d) = ∑ i : Fin n, x i * v i := by
      rfl
    rw [hsum]
    exact Finset.dvd_sum fun i _ => dvd_mul_of_dvd_right (hbasis i) (x i)
  · intro h
    rw [mem_localDualPadicDenominator_iff]
    intro x
    exact h (integralVectorToPadic (n := n) p x)

lemma padic_dotProduct_mulVec_eq_of_local_isometry_matrix
    {L₀ L₁ : PositiveDefiniteIntegralLattice n} (p : ℕ) [Fact (Nat.Prime p)]
    {U : Matrix (Fin n) (Fin n) ℤ_[p]}
    (hU : Uᵀ * L₁.pairingMatrix_padic p * U = L₀.pairingMatrix_padic p)
    (x d : Fin n → ℤ_[p]) :
    dotProduct x ((L₀.pairingMatrix_padic p).mulVec d) =
      dotProduct (U.mulVec x) ((L₁.pairingMatrix_padic p).mulVec (U.mulVec d)) := by
  calc
    dotProduct x ((L₀.pairingMatrix_padic p).mulVec d) =
        dotProduct x (((Uᵀ * L₁.pairingMatrix_padic p * U).mulVec d)) := by rw [hU]
    _ = dotProduct (U.mulVec x) ((L₁.pairingMatrix_padic p).mulVec (U.mulVec d)) := by
        calc
          dotProduct x (((Uᵀ * L₁.pairingMatrix_padic p * U).mulVec d)) =
              (x ᵥ* (Uᵀ * L₁.pairingMatrix_padic p * U)) ⬝ᵥ d := by
                rw [Matrix.dotProduct_mulVec]
          _ = (((x ᵥ* Uᵀ) ᵥ* L₁.pairingMatrix_padic p) ᵥ* U) ⬝ᵥ d := by
                simp [Matrix.mul_assoc]
          _ = ((U *ᵥ x) ᵥ* L₁.pairingMatrix_padic p) ⬝ᵥ (U *ᵥ d) := by
                rw [← Matrix.dotProduct_mulVec]
                rw [Matrix.vecMul_transpose]
          _ = dotProduct (U.mulVec x) ((L₁.pairingMatrix_padic p).mulVec (U.mulVec d)) := by
                exact (Matrix.dotProduct_mulVec (U *ᵥ x)
                  (L₁.pairingMatrix_padic p) (U *ᵥ d)).symm

lemma local_isometry_padic_matrix_inv
    {L₀ L₁ : PositiveDefiniteIntegralLattice n} (p : ℕ) [Fact (Nat.Prime p)]
    {U : Matrix (Fin n) (Fin n) ℤ_[p]}
    (hU_unit : IsUnit U)
    (hU : Uᵀ * L₁.pairingMatrix_padic p * U = L₀.pairingMatrix_padic p) :
    (U⁻¹)ᵀ * L₀.pairingMatrix_padic p * U⁻¹ = L₁.pairingMatrix_padic p := by
  have hdet : IsUnit U.det := by
    rwa [Matrix.isUnit_iff_isUnit_det] at hU_unit
  have hmul : U * U⁻¹ = 1 := Matrix.mul_nonsing_inv U hdet
  have hleft : (U⁻¹)ᵀ * Uᵀ = 1 := by
    rw [← Matrix.transpose_mul, hmul, Matrix.transpose_one]
  calc
    (U⁻¹)ᵀ * L₀.pairingMatrix_padic p * U⁻¹ =
        (U⁻¹)ᵀ * (Uᵀ * L₁.pairingMatrix_padic p * U) * U⁻¹ := by rw [hU]
    _ = ((U⁻¹)ᵀ * Uᵀ) * L₁.pairingMatrix_padic p * (U * U⁻¹) := by
          simp [Matrix.mul_assoc]
    _ = L₁.pairingMatrix_padic p := by
          rw [hleft, hmul]
          simp

lemma localDualPadicDenominator_mulVec_iff_of_local_isometry_matrix
    {L₀ L₁ : PositiveDefiniteIntegralLattice n} (p k : ℕ) [Fact (Nat.Prime p)]
    {U : Matrix (Fin n) (Fin n) ℤ_[p]}
    (hU_unit : IsUnit U)
    (hU : Uᵀ * L₁.pairingMatrix_padic p * U = L₀.pairingMatrix_padic p)
    (d : Fin n → ℤ_[p]) :
    U.mulVec d ∈ localDualPadicDenominator L₁ p k ↔
      d ∈ localDualPadicDenominator L₀ p k := by
  constructor
  · intro hd
    rw [mem_localDualPadicDenominator_iff_forall_padic]
    intro x
    have hx := (mem_localDualPadicDenominator_iff_forall_padic L₁ p k
      (U.mulVec d)).mp hd (U.mulVec x)
    rwa [← padic_dotProduct_mulVec_eq_of_local_isometry_matrix
      (L₀ := L₀) (L₁ := L₁) p hU x d] at hx
  · intro hd
    rw [mem_localDualPadicDenominator_iff_forall_padic]
    intro y
    have hdet : IsUnit U.det := by
      rwa [Matrix.isUnit_iff_isUnit_det] at hU_unit
    have hmul : U * U⁻¹ = 1 := Matrix.mul_nonsing_inv U hdet
    have hy : U.mulVec (U⁻¹ *ᵥ y) = y := by
      have happ := congrArg (fun M : Matrix (Fin n) (Fin n) ℤ_[p] => M.mulVec y) hmul
      simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply, Finset.sum_mul,
        Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm] using happ
    have hx := (mem_localDualPadicDenominator_iff_forall_padic L₀ p k d).mp hd
      (U⁻¹ *ᵥ y)
    rw [← hy]
    simpa [padic_dotProduct_mulVec_eq_of_local_isometry_matrix
      (L₀ := L₀) (L₁ := L₁) p hU (U⁻¹ *ᵥ y) d] using hx

lemma localDualPadicDenominator_map_of_local_isometry_matrix
    {L₀ L₁ : PositiveDefiniteIntegralLattice n} (p k : ℕ) [Fact (Nat.Prime p)]
    {U : Matrix (Fin n) (Fin n) ℤ_[p]}
    (hU_unit : IsUnit U)
    (hU : Uᵀ * L₁.pairingMatrix_padic p * U = L₀.pairingMatrix_padic p) :
    Submodule.map (Matrix.toLin' U)
        (localDualPadicDenominator L₀ p k) =
      localDualPadicDenominator L₁ p k := by
  ext y
  constructor
  · intro hy
    rcases hy with ⟨d, hd, rfl⟩
    exact (localDualPadicDenominator_mulVec_iff_of_local_isometry_matrix
      (L₀ := L₀) (L₁ := L₁) p k hU_unit hU d).mpr hd
  · intro hy
    have hdet : IsUnit U.det := by
      rwa [Matrix.isUnit_iff_isUnit_det] at hU_unit
    have hmul : U * U⁻¹ = 1 := Matrix.mul_nonsing_inv U hdet
    have hU_inv :=
      local_isometry_padic_matrix_inv (L₀ := L₀) (L₁ := L₁) p hU_unit hU
    refine ⟨U⁻¹ *ᵥ y, ?_, ?_⟩
    · exact (localDualPadicDenominator_mulVec_iff_of_local_isometry_matrix
        (L₀ := L₁) (L₁ := L₀) p k (by rwa [Matrix.isUnit_nonsing_inv_iff]) hU_inv y).mpr hy
    · have happ := congrArg (fun M : Matrix (Fin n) (Fin n) ℤ_[p] => M.mulVec y) hmul
      simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply, Finset.sum_mul,
        Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm] using happ

/-- The integral preimage of the `p`-adic local-dual denominator. -/
def localDualPadicDenominatorIntegralPreimage
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] :
    Submodule ℤ (Fin n → ℤ) where
  carrier := {d | integralVectorToPadic (n := n) p d ∈
    localDualPadicDenominator L p k}
  zero_mem' := by
    change integralVectorToPadic (n := n) p 0 ∈ localDualPadicDenominator L p k
    exact (localDualPadicDenominator L p k).zero_mem
  add_mem' := by
    intro d e hd he
    have hcast :
        integralVectorToPadic (n := n) p (d + e) =
          integralVectorToPadic (n := n) p d +
            integralVectorToPadic (n := n) p e := by
      ext i
      simp [integralVectorToPadic]
    change integralVectorToPadic (n := n) p (d + e) ∈
      localDualPadicDenominator L p k
    rw [hcast]
    exact (localDualPadicDenominator L p k).add_mem hd he
  smul_mem' := by
    intro a d hd
    have hcast :
        integralVectorToPadic (n := n) p (a • d) =
          (a : ℤ_[p]) • integralVectorToPadic (n := n) p d := by
      ext i
      simp [integralVectorToPadic]
    change integralVectorToPadic (n := n) p (a • d) ∈
      localDualPadicDenominator L p k
    rw [hcast]
    exact (localDualPadicDenominator L p k).smul_mem (a : ℤ_[p]) hd

/-- The integral-coordinate integral model of the associated-bilinear source
denominator. -/
def associatedBilinearDualPadicDenominatorIntegralPreimage
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] :
    Submodule ℤ (Fin n → ℤ) :=
  padicSubmoduleIntegralPreimage (n := n) p
    (associatedBilinearDualPadicDenominator L p k)

/-- The source and current integral quotient denominators agree away from
the dyadic prime. -/
lemma associatedBilinearDualPadicDenominatorIntegralPreimage_eq_localDualPadicDenominatorIntegralPreimage_of_ne_two
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hp_two : p ≠ 2) :
    associatedBilinearDualPadicDenominatorIntegralPreimage L p k =
      localDualPadicDenominatorIntegralPreimage L p k := by
  rw [associatedBilinearDualPadicDenominatorIntegralPreimage,
    L.associatedBilinearDualPadicDenominator_eq_localDualPadicDenominator_of_ne_two
      p k hp_two]
  ext d
  rfl

/-- Integral-integral model form of the exact dyadic denominator shift. -/
lemma associatedBilinearDualPadicDenominatorIntegralPreimage_succ_eq_localDualPadicDenominatorIntegralPreimage_dyadic
    (L : PositiveDefiniteIntegralLattice n) (k : ℕ) :
    associatedBilinearDualPadicDenominatorIntegralPreimage L 2 (k + 1) =
      localDualPadicDenominatorIntegralPreimage L 2 k := by
  rw [associatedBilinearDualPadicDenominatorIntegralPreimage,
    L.associatedBilinearDualPadicDenominator_succ_eq_localDualPadicDenominator_dyadic]
  ext d
  rfl

lemma associatedBilinearDualPadicDenominatorIntegralPreimage_zero_eq_top
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    associatedBilinearDualPadicDenominatorIntegralPreimage L p 0 = ⊤ := by
  rw [associatedBilinearDualPadicDenominatorIntegralPreimage,
    L.associatedBilinearDualPadicDenominator_zero_eq_top]
  ext d
  simp [padicSubmoduleIntegralPreimage]

lemma mem_associatedBilinearDualPadicDenominator_of_forall_coord_primePow_dvd
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    {d : Fin n → ℤ_[p]} (hd : ∀ i : Fin n, ((p : ℤ_[p]) ^ k ∣ d i)) :
    d ∈ associatedBilinearDualPadicDenominator L p k := by
  rw [mem_associatedBilinearDualPadicDenominator_iff]
  intro x
  have hmul : ∀ i : Fin n,
      ((p : ℤ_[p]) ^ k ∣ ((L.polarGramMatrix_padic p).mulVec d) i) := by
    intro i
    rw [Matrix.mulVec, dotProduct]
    exact Finset.dvd_sum fun j _ =>
      dvd_mul_of_dvd_right (hd j) ((L.polarGramMatrix_padic p) i j)
  rw [dotProduct]
  exact Finset.dvd_sum fun i _ =>
    dvd_mul_of_dvd_right (hmul i)
      (integralVectorToPadic (n := n) p x i)

/-- Coordinatewise multiples of `p^k` lie in the depth-`k`
associated-bilinear source denominator. -/
lemma primePowCoordinateSubmodule_le_associatedBilinearDualPadicDenominatorIntegralPreimage
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] :
    primePowCoordinateSubmodule (n := n) p k ≤
      associatedBilinearDualPadicDenominatorIntegralPreimage L p k := by
  intro d hd
  unfold associatedBilinearDualPadicDenominatorIntegralPreimage
  rw [mem_padicSubmoduleIntegralPreimage_iff]
  apply L.mem_associatedBilinearDualPadicDenominator_of_forall_coord_primePow_dvd
  obtain ⟨z, hz⟩ := hd
  intro i
  refine ⟨(z i : ℤ_[p]), ?_⟩
  have hi := congrFun hz i
  simpa [integralVectorToPadic, Pi.smul_apply, smul_eq_mul] using
    congrArg (fun a : ℤ => (a : ℤ_[p])) hi.symm

lemma exists_integralVectorToPadic_sub_mem_associatedBilinearDualPadicDenominator
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (v : Fin n → ℤ_[p]) :
    ∃ x : Fin n → ℤ,
      v - integralVectorToPadic (n := n) p x ∈
        associatedBilinearDualPadicDenominator L p k := by
  classical
  choose z hz using fun i : Fin n =>
    padicInt_exists_int_sub_mem_span_primePow p k (v i)
  refine ⟨z, ?_⟩
  refine
    mem_associatedBilinearDualPadicDenominator_of_forall_coord_primePow_dvd
      (n := n) L p k ?_
  intro i
  simpa [Pi.sub_apply, integralVectorToPadic] using hz i

lemma padicSubmoduleIntegralPreimageQuotientMap_surjective_associatedBilinearDualPadicDenominator
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] :
    Function.Surjective
      (padicSubmoduleIntegralPreimageQuotientMap (n := n) p
        (associatedBilinearDualPadicDenominator L p k)) := by
  intro q
  induction q using Quotient.inductionOn with
  | h v =>
      rcases
          exists_integralVectorToPadic_sub_mem_associatedBilinearDualPadicDenominator
            (n := n) L p k v with
        ⟨x, hx⟩
      refine ⟨(associatedBilinearDualPadicDenominatorIntegralPreimage
        L p k).mkQ x, ?_⟩
      change (padicSubmoduleIntegralPreimageQuotientMap (n := n) p
          (associatedBilinearDualPadicDenominator L p k))
          ((padicSubmoduleIntegralPreimage (n := n) p
            (associatedBilinearDualPadicDenominator L p k)).mkQ x) = _
      rw [padicSubmoduleIntegralPreimageQuotientMap_mkQ]
      change (Submodule.Quotient.mk (integralVectorToPadic (n := n) p x) :
          (Fin n → ℤ_[p]) ⧸
            associatedBilinearDualPadicDenominator L p k) =
        Submodule.Quotient.mk v
      rw [Submodule.Quotient.eq]
      simpa [sub_eq_add_neg, add_comm] using
        (associatedBilinearDualPadicDenominator L p k).neg_mem hx

/-- The source integral-integral model quotient is canonically its p-adic quotient. -/
noncomputable def
    associatedBilinearDualPadicDenominatorIntegralPreimageQuotientEquiv
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] :
    ((Fin n → ℤ) ⧸
        associatedBilinearDualPadicDenominatorIntegralPreimage L p k) ≃ₗ[ℤ]
      ((Fin n → ℤ_[p]) ⧸
        associatedBilinearDualPadicDenominator L p k) :=
  LinearEquiv.ofBijective
    (padicSubmoduleIntegralPreimageQuotientMap (n := n) p
      (associatedBilinearDualPadicDenominator L p k))
    ⟨padicSubmoduleIntegralPreimageQuotientMap_injective (n := n) p _,
      padicSubmoduleIntegralPreimageQuotientMap_surjective_associatedBilinearDualPadicDenominator
        (n := n) L p k⟩

@[simp] lemma
    associatedBilinearDualPadicDenominatorIntegralPreimageQuotientEquiv_apply
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (q : (Fin n → ℤ) ⧸
      associatedBilinearDualPadicDenominatorIntegralPreimage L p k) :
    associatedBilinearDualPadicDenominatorIntegralPreimageQuotientEquiv
        L p k q =
      padicSubmoduleIntegralPreimageQuotientMap (n := n) p
        (associatedBilinearDualPadicDenominator L p k) q := rfl

/-- Every quotient class for a local-dual denominator has an integral
representative, so the integral-integral model quotient cast is an equivalence. -/
noncomputable def localDualPadicDenominatorIntegralPreimageQuotientEquiv
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] :
    ((Fin n → ℤ) ⧸ localDualPadicDenominatorIntegralPreimage L p k) ≃ₗ[ℤ]
      ((Fin n → ℤ_[p]) ⧸ localDualPadicDenominator L p k) :=
  LinearEquiv.ofBijective
    (padicSubmoduleIntegralPreimageQuotientMap (n := n) p
      (localDualPadicDenominator L p k))
    ⟨padicSubmoduleIntegralPreimageQuotientMap_injective (n := n) p _,
      padicSubmoduleIntegralPreimageQuotientMap_surjective_localDualPadicDenominator
        (n := n) L p k⟩

@[simp] lemma localDualPadicDenominatorIntegralPreimageQuotientEquiv_apply
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (q : (Fin n → ℤ) ⧸ localDualPadicDenominatorIntegralPreimage L p k) :
    localDualPadicDenominatorIntegralPreimageQuotientEquiv L p k q =
      padicSubmoduleIntegralPreimageQuotientMap (n := n) p
        (localDualPadicDenominator L p k) q := rfl

/-- Dividing a depth-`k` local-dual denominator vector by `p^k` produces an
actual vector in the local dual lattice. -/
lemma isLocalDualPadicVector_div_primePow_of_mem_localDualPadicDenominator
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (d : Fin n → ℤ_[p])
    (hd : d ∈ localDualPadicDenominator L p k) :
    L.IsLocalDualPadicVector p
      (fun i => (d i : ℚ_[p]) / (p : ℚ_[p]) ^ k) := by
  have hd' :=
    (mem_localDualPadicDenominator_iff_forall_padic L p k d).mp hd
  have hcoord : ∀ i : Fin n,
      ((p : ℤ_[p]) ^ k ∣ (L.pairingMatrix_padic p).mulVec d i) := by
    intro i
    have hi := hd' ((Pi.basisFun ℤ_[p] (Fin n)) i)
    have hdot :
        dotProduct ((Pi.basisFun ℤ_[p] (Fin n)) i)
            ((L.pairingMatrix_padic p).mulVec d) =
          (L.pairingMatrix_padic p).mulVec d i := by
      rw [dotProduct]
      calc
        (∑ j, ((Pi.basisFun ℤ_[p] (Fin n)) i) j *
            ((L.pairingMatrix_padic p).mulVec d) j) =
            ((Pi.basisFun ℤ_[p] (Fin n)) i) i *
              ((L.pairingMatrix_padic p).mulVec d) i := by
                exact Finset.sum_eq_single i
                  (by
                    intro j _ hji
                    have hz : ((Pi.basisFun ℤ_[p] (Fin n)) i) j = 0 := by
                      simp [Pi.basisFun, hji]
                    rw [hz, zero_mul])
                  (by simp)
        _ = (L.pairingMatrix_padic p).mulVec d i := by
              simp [Pi.basisFun]
    rwa [hdot] at hi
  intro i
  rcases hcoord i with ⟨a, ha⟩
  have hp : (p : ℚ_[p]) ^ k ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero)
  have hvalue :
      (L.pairingMatrix_padicField p).mulVec
          (fun j => (d j : ℚ_[p]) / (p : ℚ_[p]) ^ k) i =
        (a : ℚ_[p]) := by
    rw [Matrix.mulVec, dotProduct]
    calc
      (∑ j, (L.pairingMatrix_padicField p) i j *
          ((d j : ℚ_[p]) / (p : ℚ_[p]) ^ k)) =
          (∑ j, (L.pairingMatrix_padicField p) i j * (d j : ℚ_[p])) /
            (p : ℚ_[p]) ^ k := by
              rw [Finset.sum_div]
              apply Finset.sum_congr rfl
              intro j _
              ring
      _ = (((L.pairingMatrix_padic p).mulVec d i : ℤ_[p]) : ℚ_[p]) /
            (p : ℚ_[p]) ^ k := by
              congr 1
              change (∑ j, ((L.pairingMatrix_padic p) i j : ℚ_[p]) *
                (d j : ℚ_[p])) = _
              rw [Matrix.mulVec, dotProduct]
              change (∑ j, PadicInt.Coe.ringHom
                ((L.pairingMatrix_padic p) i j * d j)) =
                PadicInt.Coe.ringHom (∑ j, (L.pairingMatrix_padic p) i j * d j)
              rw [map_sum]
      _ = (a : ℚ_[p]) := by
              rw [ha]
              push_cast
              field_simp
  rw [hvalue]
  exact a.property

/-- Dividing a depth-`k` source denominator vector by `p^k` produces a
vector in the associated-bilinear local dual. -/
lemma isAssociatedBilinearDualPadicVector_div_primePow_of_mem_associatedBilinearDualPadicDenominator
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (d : Fin n → ℤ_[p])
    (hd : d ∈ associatedBilinearDualPadicDenominator L p k) :
    L.IsAssociatedBilinearDualPadicVector p
      (fun i => (d i : ℚ_[p]) / (p : ℚ_[p]) ^ k) := by
  intro i
  have hi := (mem_associatedBilinearDualPadicDenominator_iff L p k d).mp hd
    ((Pi.basisFun ℤ (Fin n)) i)
  have hdot :
      dotProduct (integralVectorToPadic (n := n) p ((Pi.basisFun ℤ (Fin n)) i))
          ((L.polarGramMatrix_padic p).mulVec d) =
        (L.polarGramMatrix_padic p).mulVec d i := by
    rw [dotProduct, Finset.sum_eq_single i]
    · simp [integralVectorToPadic, Pi.basisFun]
    · intro j _ hji
      simp [integralVectorToPadic, Pi.basisFun, hji]
    · simp
  rw [hdot] at hi
  rcases hi with ⟨a, ha⟩
  have hvalue :
      (L.polarGramMatrix_padicField p).mulVec
          (fun j => (d j : ℚ_[p]) / (p : ℚ_[p]) ^ k) i =
        (a : ℚ_[p]) := by
    rw [Matrix.mulVec, dotProduct]
    calc
      (∑ j, L.polarGramMatrix_padicField p i j *
          ((d j : ℚ_[p]) / (p : ℚ_[p]) ^ k)) =
          (∑ j, L.polarGramMatrix_padicField p i j * (d j : ℚ_[p])) /
            (p : ℚ_[p]) ^ k := by
              rw [Finset.sum_div]
              apply Finset.sum_congr rfl
              intro j _
              ring
      _ = (((L.polarGramMatrix_padic p).mulVec d i : ℤ_[p]) : ℚ_[p]) /
            (p : ℚ_[p]) ^ k := by
              congr 1
              simp [polarGramMatrix_padicField, polarGramMatrix_padic, Matrix.mulVec,
                dotProduct]
      _ = (a : ℚ_[p]) := by
              rw [ha]
              push_cast
              field_simp [pow_ne_zero k
                (by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero :
                  (p : ℚ_[p]) ≠ 0)]
  rw [hvalue]
  exact a.property

/-- Exact source lattice depth lets one divide every depth-`k+1`
associated-bilinear denominator vector by `p` inside the depth-`k`
denominator. -/
lemma exists_prime_smul_eq_of_mem_associatedBilinearDualPadicDenominator_succ
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : L.IsAssociatedBilinearHenselLatticeDepth p k)
    (d : Fin n → ℤ_[p])
    (hd : d ∈ associatedBilinearDualPadicDenominator L p (k + 1)) :
    ∃ e ∈ associatedBilinearDualPadicDenominator L p k,
      (p : ℤ_[p]) • e = d := by
  let y : Fin n → ℚ_[p] :=
    fun i => (d i : ℚ_[p]) / (p : ℚ_[p]) ^ (k + 1)
  have hy : L.IsAssociatedBilinearDualPadicVector p y := by
    exact
      isAssociatedBilinearDualPadicVector_div_primePow_of_mem_associatedBilinearDualPadicDenominator
        L p (k + 1) d hd
  let e : Fin n → ℤ_[p] := fun i => ⟨(p : ℚ_[p]) ^ k * y i, hk y hy i⟩
  have hpe : (p : ℤ_[p]) • e = d := by
    ext i
    apply PadicInt.ext
    change (p : ℚ_[p]) * ((p : ℚ_[p]) ^ k * y i) = (d i : ℚ_[p])
    dsimp [y]
    have hp : (p : ℚ_[p]) ≠ 0 := by
      exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
    rw [pow_succ]
    field_simp
  refine ⟨e, ?_, hpe⟩
  rw [mem_associatedBilinearDualPadicDenominator_iff]
  intro x
  rcases (mem_associatedBilinearDualPadicDenominator_iff
      L p (k + 1) d).mp hd x with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  have hdot :
      dotProduct (integralVectorToPadic (n := n) p x)
          ((L.polarGramMatrix_padic p).mulVec d) =
        (p : ℤ_[p]) *
          dotProduct (integralVectorToPadic (n := n) p x)
            ((L.polarGramMatrix_padic p).mulVec e) := by
    rw [← hpe]
    simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_left_comm]
  rw [hdot] at ha
  rw [pow_succ] at ha
  have hp : (p : ℤ_[p]) ≠ 0 := by
    exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
  apply mul_left_cancel₀ hp
  simpa [mul_assoc, mul_comm, mul_left_comm] using ha

/-- The depth-`k+1` source associated-bilinear denominator is contained in
its depth-`k` counterpart. -/
lemma associatedBilinearDualPadicDenominator_succ_le
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] :
    associatedBilinearDualPadicDenominator L p (k + 1) ≤
      associatedBilinearDualPadicDenominator L p k := by
  intro d hd x
  rcases hd x with ⟨a, ha⟩
  refine ⟨(p : ℤ_[p]) * a, ?_⟩
  rw [pow_succ] at ha
  rw [ha]
  ring

/-- Under exact source lattice depth, the successor associated-bilinear
denominator is multiplication by `p` of the preceding denominator. -/
lemma associatedBilinearDualPadicDenominator_succ_eq_map_prime_smul
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : L.IsAssociatedBilinearHenselLatticeDepth p k) :
    associatedBilinearDualPadicDenominator L p (k + 1) =
      Submodule.map ((LinearMap.lsmul ℤ_[p] (Fin n → ℤ_[p])) (p : ℤ_[p]))
        (associatedBilinearDualPadicDenominator L p k) := by
  ext d
  constructor
  · intro hd
    obtain ⟨e, he, hpe⟩ :=
      exists_prime_smul_eq_of_mem_associatedBilinearDualPadicDenominator_succ
        L p k hk d hd
    exact ⟨e, he, hpe⟩
  · intro hd
    obtain ⟨e, he, rfl⟩ := hd
    change (p : ℤ_[p]) • e ∈
      associatedBilinearDualPadicDenominator L p (k + 1)
    rw [mem_associatedBilinearDualPadicDenominator_iff]
    intro x
    rcases (mem_associatedBilinearDualPadicDenominator_iff
      L p k e).mp he x with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    have h := congrArg (fun z : ℤ_[p] => (p : ℤ_[p]) * z) ha
    simpa [pow_succ, Matrix.mulVec, dotProduct, Finset.mul_sum,
      mul_assoc, mul_comm, mul_left_comm] using h

/-- The submodule `p S_k` inside the source depth-`k` denominator. -/
def associatedBilinearDualPadicDenominatorPrimeSubmodule
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] :
    Submodule ℤ_[p] (associatedBilinearDualPadicDenominator L p k) :=
  (Submodule.map
    ((LinearMap.lsmul ℤ_[p] (Fin n → ℤ_[p])) (p : ℤ_[p]))
    (associatedBilinearDualPadicDenominator L p k)).comap
      (associatedBilinearDualPadicDenominator L p k).subtype

/-- Exact local lattice depth lets one divide every depth-`k+1` denominator
vector by `p` inside the depth-`k` denominator. -/
lemma exists_prime_smul_eq_of_mem_localDualPadicDenominator_succ
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : L.IsHenselLatticeDepth p k)
    (d : Fin n → ℤ_[p])
    (hd : d ∈ localDualPadicDenominator L p (k + 1)) :
    ∃ e ∈ localDualPadicDenominator L p k, (p : ℤ_[p]) • e = d := by
  let y : Fin n → ℚ_[p] :=
    fun i => (d i : ℚ_[p]) / (p : ℚ_[p]) ^ (k + 1)
  have hy : L.IsLocalDualPadicVector p y := by
    exact isLocalDualPadicVector_div_primePow_of_mem_localDualPadicDenominator
      L p (k + 1) d hd
  let e : Fin n → ℤ_[p] := fun i => ⟨(p : ℚ_[p]) ^ k * y i, hk y hy i⟩
  have hpe : (p : ℤ_[p]) • e = d := by
    ext i
    apply PadicInt.ext
    change (p : ℚ_[p]) * ((p : ℚ_[p]) ^ k * y i) = (d i : ℚ_[p])
    dsimp [y]
    have hp : (p : ℚ_[p]) ≠ 0 := by
      exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
    rw [pow_succ]
    field_simp
  refine ⟨e, ?_, hpe⟩
  rw [mem_localDualPadicDenominator_iff_forall_padic]
  intro x
  rcases (mem_localDualPadicDenominator_iff_forall_padic
      L p (k + 1) d).mp hd x with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  have hdot :
      dotProduct x ((L.pairingMatrix_padic p).mulVec d) =
        (p : ℤ_[p]) * dotProduct x ((L.pairingMatrix_padic p).mulVec e) := by
    rw [← hpe]
    simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_left_comm]
  rw [hdot] at ha
  rw [pow_succ] at ha
  have hp : (p : ℤ_[p]) ≠ 0 := by
    exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
  apply mul_left_cancel₀ hp
  simpa [mul_assoc, mul_comm, mul_left_comm] using ha

/-- The depth-`k+1` local-dual denominator is contained in its depth-`k`
counterpart. -/
lemma localDualPadicDenominator_succ_le
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] :
    localDualPadicDenominator L p (k + 1) ≤
      localDualPadicDenominator L p k := by
  intro d hd x
  rcases hd x with ⟨a, ha⟩
  refine ⟨(p : ℤ_[p]) * a, ?_⟩
  rw [pow_succ] at ha
  rw [ha]
  ring

/-- Under the exact local lattice-depth hypothesis, the successor denominator
is precisely the image of the preceding denominator under multiplication by
`p`.  This is the scaling identity behind the adjacent residue quotient. -/
lemma localDualPadicDenominator_succ_eq_map_prime_smul
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : L.IsHenselLatticeDepth p k) :
    localDualPadicDenominator L p (k + 1) =
      Submodule.map ((LinearMap.lsmul ℤ_[p] (Fin n → ℤ_[p])) (p : ℤ_[p]))
        (localDualPadicDenominator L p k) := by
  ext d
  constructor
  · intro hd
    obtain ⟨e, he, hpe⟩ :=
      exists_prime_smul_eq_of_mem_localDualPadicDenominator_succ
        L p k hk d hd
    exact ⟨e, he, hpe⟩
  · intro hd
    obtain ⟨e, he, rfl⟩ := hd
    change (p : ℤ_[p]) • e ∈ localDualPadicDenominator L p (k + 1)
    rw [mem_localDualPadicDenominator_iff_forall_padic]
    intro x
    rcases (mem_localDualPadicDenominator_iff_forall_padic
      L p k e).mp he x with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    have h := congrArg (fun z : ℤ_[p] => (p : ℤ_[p]) * z) ha
    simpa [pow_succ, Matrix.mulVec, dotProduct, Finset.mul_sum,
      mul_assoc, mul_comm, mul_left_comm] using h

/-- The submodule `p D_k` inside the depth-`k` local-dual denominator. -/
def localDualPadicDenominatorPrimeSubmodule
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] :
    Submodule ℤ_[p] (localDualPadicDenominator L p k) :=
  (Submodule.map
    ((LinearMap.lsmul ℤ_[p] (Fin n → ℤ_[p])) (p : ℤ_[p]))
    (localDualPadicDenominator L p k)).comap
      (localDualPadicDenominator L p k).subtype

/-- The integral integral models inherit the successor-depth inclusion of the local
dual denominators. -/
lemma localDualPadicDenominatorIntegralPreimage_succ_le
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] :
    localDualPadicDenominatorIntegralPreimage L p (k + 1) ≤
      localDualPadicDenominatorIntegralPreimage L p k := by
  intro d hd
  exact localDualPadicDenominator_succ_le L p k hd

/-- The source integral integral models inherit the successor-depth inclusion. -/
lemma associatedBilinearDualPadicDenominatorIntegralPreimage_succ_le
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] :
    associatedBilinearDualPadicDenominatorIntegralPreimage L p (k + 1) ≤
      associatedBilinearDualPadicDenominatorIntegralPreimage L p k := by
  intro d hd
  exact associatedBilinearDualPadicDenominator_succ_le L p k hd

/-- Source integral denominators at later depths refine the initial
denominator. -/
lemma associatedBilinearDualPadicDenominatorIntegralPreimage_add_le
    (L : PositiveDefiniteIntegralLattice n) (p k r : ℕ) [Fact (Nat.Prime p)] :
    associatedBilinearDualPadicDenominatorIntegralPreimage L p (k + r) ≤
      associatedBilinearDualPadicDenominatorIntegralPreimage L p k := by
  induction r with
  | zero => simp
  | succ r ih =>
      have hs :
          associatedBilinearDualPadicDenominatorIntegralPreimage L p
              (k + (r + 1)) ≤
            associatedBilinearDualPadicDenominatorIntegralPreimage L p
              (k + r) := by
        simpa [Nat.add_assoc] using
          (L.associatedBilinearDualPadicDenominatorIntegralPreimage_succ_le
            p (k + r))
      exact hs.trans ih

/-- Integral-integral model inclusion underlying the dyadic source/current quotient
projection. -/
lemma localDualPadicDenominatorIntegralPreimage_le_associatedBilinearDualPadicDenominatorIntegralPreimage_dyadic
    (L : PositiveDefiniteIntegralLattice n) (k : ℕ) (hk : 1 ≤ k) :
    localDualPadicDenominatorIntegralPreimage L 2 k ≤
      associatedBilinearDualPadicDenominatorIntegralPreimage L 2 k := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [show 1 + r = r + 1 by omega,
    L.associatedBilinearDualPadicDenominatorIntegralPreimage_succ_eq_localDualPadicDenominatorIntegralPreimage_dyadic]
  exact localDualPadicDenominatorIntegralPreimage_succ_le L 2 r

lemma localDualPadicDenominatorIntegralPreimage_eq_padicSubmoduleIntegralPreimage
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] :
    localDualPadicDenominatorIntegralPreimage L p k =
      padicSubmoduleIntegralPreimage (n := n) p
        (localDualPadicDenominator L p k) := by
  ext d
  rfl

lemma mem_localDualPadicDenominatorIntegralPreimage_iff
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (d : Fin n → ℤ) :
    d ∈ localDualPadicDenominatorIntegralPreimage L p k ↔
      localDualPadicPairingCondition L p k d := by
  constructor
  · intro hd x
    have hx := (mem_localDualPadicDenominator_iff L p k
      (integralVectorToPadic (n := n) p d)).mp hd x
    rwa [padicBilinearFormValue_integral_right L p x d] at hx
  · intro hd
    change integralVectorToPadic (n := n) p d ∈ localDualPadicDenominator L p k
    rw [mem_localDualPadicDenominator_iff]
    intro x
    rw [padicBilinearFormValue_integral_right L p x d]
    exact hd x

/-- The integral-coordinate integral model of the local denominator
`p^k L_p# ∩ L`, expressed directly by p-adic divisibility of all pairings.

The later local scalar-extension construction should identify its coordinate
image with this submodule; the lemmas below already connect that source-facing
condition to the finite quotient denominator used for the Lean count. -/
def localDualPadicCoordinateSubmodule
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] :
    Submodule ℤ (Fin n → ℤ) where
  carrier := {d | localDualPadicPairingCondition L p k d}
  zero_mem' := by
    intro x
    simp [bilinearFormValue]
  add_mem' := by
    intro d e hd he x
    have hB :
        L.bilinearFormValue x (d + e) =
          L.bilinearFormValue x d + L.bilinearFormValue x e := by
      simp [bilinearFormValue, Matrix.mulVec_add, dotProduct,
        Finset.sum_add_distrib, mul_add]
    change ((p : ℤ_[p]) ^ k ∣
      ((L.bilinearFormValue x (d + e) : ℤ) : ℤ_[p]))
    rw [hB]
    rw [Int.cast_add]
    exact dvd_add (hd x) (he x)
  smul_mem' := by
    intro a d hd x
    have hB :
        L.bilinearFormValue x (a • d) =
          a * L.bilinearFormValue x d := by
      simp [bilinearFormValue, Matrix.mulVec, dotProduct, Finset.mul_sum,
        mul_assoc, mul_comm, mul_left_comm]
    change ((p : ℤ_[p]) ^ k ∣
      ((L.bilinearFormValue x (a • d) : ℤ) : ℤ_[p]))
    rw [hB]
    rw [Int.cast_mul]
    exact dvd_mul_of_dvd_right (hd x) (a : ℤ_[p])

lemma mem_localDualPadicCoordinateSubmodule_iff
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (d : Fin n → ℤ) :
    d ∈ localDualPadicCoordinateSubmodule L p k ↔
      localDualPadicPairingCondition L p k d := Iff.rfl

/-- The local scalar-extension denominator has the same integral coordinate
integral model as the p-adic pairing denominator. -/
lemma localDualPadicDenominatorIntegralPreimage_eq_localDualPadicCoordinateSubmodule
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] :
    localDualPadicDenominatorIntegralPreimage L p k =
      localDualPadicCoordinateSubmodule L p k := by
  ext d
  rw [mem_localDualPadicDenominatorIntegralPreimage_iff,
    mem_localDualPadicCoordinateSubmodule_iff]

lemma localDualPadicCoordinateSubmodule_eq_localDualPairingCoordinateSubmodule
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] :
    localDualPadicCoordinateSubmodule L p k =
      localDualPairingCoordinateSubmodule L p k := by
  ext d
  rw [mem_localDualPadicCoordinateSubmodule_iff,
    mem_localDualPairingCoordinateSubmodule_iff_padic_pairingCondition]

lemma mem_pairingMatrixLocalDualCoordinateSubmodule_iff_pairing_zmod_zero
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (d : Fin n → ℤ) :
    d ∈ pairingMatrixLocalDualCoordinateSubmodule L p k ↔
      ∀ x : Fin n → ℤ,
        ((L.bilinearFormValue x d : ℤ) :
          ZMod (primePowModulus p k : ℕ)) = 0 := by
  constructor
  · intro hd x
    let m : ℕ+ := primePowModulus p k
    have hFd :
        (matrixMod L.pairingMatrix m).mulVec
          (fun j : Fin n => (d j : ZMod (m : ℕ))) = 0 := by
      simpa [pairingMatrixLocalDualCoordinateSubmodule, matrixModLinearMap, m]
        using hd
    calc
      ((L.bilinearFormValue x d : ℤ) :
          ZMod (primePowModulus p k : ℕ)) =
          dotProduct (fun i : Fin n => (x i : ZMod (m : ℕ)))
            ((matrixMod L.pairingMatrix m).mulVec
              (fun j : Fin n => (d j : ZMod (m : ℕ)))) := by
            simp [m, bilinearFormValue, matrixMod, dotProduct, Matrix.mulVec]
      _ = 0 := by rw [hFd]; simp [dotProduct]
  · intro hpair
    rw [pairingMatrixLocalDualCoordinateSubmodule, LinearMap.mem_ker]
    let m : ℕ+ := primePowModulus p k
    ext i
    have hi := hpair ((Pi.basisFun ℤ (Fin n)) i)
    let v : Fin n → ZMod (m : ℕ) := fun j => (d j : ZMod (m : ℕ))
    let w : Fin n → ZMod (m : ℕ) := (matrixMod L.pairingMatrix m).mulVec v
    have hrow :
        dotProduct (fun j : Fin n => (((Pi.basisFun ℤ (Fin n)) i) j :
          ZMod (m : ℕ))) w = w i := by
      rw [dotProduct]
      calc
        ∑ j : Fin n, (((Pi.basisFun ℤ (Fin n)) i) j : ZMod (m : ℕ)) * w j =
            (((Pi.basisFun ℤ (Fin n)) i) i : ZMod (m : ℕ)) * w i := by
              refine Finset.sum_eq_single (s := Finset.univ) (a := i)
                (f := fun j : Fin n =>
                  (((Pi.basisFun ℤ (Fin n)) i) j : ZMod (m : ℕ)) * w j) ?_ ?_
              · intro j _ hji
                simp [Pi.basisFun, Pi.single_eq_of_ne hji]
              · intro hi_mem
                simp at hi_mem
        _ = w i := by
              simp [Pi.basisFun]
    have hi' :
        dotProduct (fun j : Fin n => (((Pi.basisFun ℤ (Fin n)) i) j :
          ZMod (m : ℕ))) w = 0 := by
      simpa [m, v, w, bilinearFormValue, matrixMod, Matrix.mulVec,
        dotProduct] using hi
    simpa [m, v, w, matrixModLinearMap] using hrow.symm.trans hi'

lemma pairingMatrixLocalDualCoordinateSubmodule_eq_localDualPairingCoordinateSubmodule
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] :
    pairingMatrixLocalDualCoordinateSubmodule L p k =
      localDualPairingCoordinateSubmodule L p k := by
  ext d
  rw [mem_pairingMatrixLocalDualCoordinateSubmodule_iff_pairing_zmod_zero,
    mem_localDualPairingCoordinateSubmodule_iff]

lemma localDualPadicCoordinateSubmodule_eq_pairingMatrixLocalDualCoordinateSubmodule
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] :
    localDualPadicCoordinateSubmodule L p k =
      pairingMatrixLocalDualCoordinateSubmodule L p k := by
  rw [localDualPadicCoordinateSubmodule_eq_localDualPairingCoordinateSubmodule,
    pairingMatrixLocalDualCoordinateSubmodule_eq_localDualPairingCoordinateSubmodule]

lemma primePowCoordinateSubmodule_le_pairingMatrixLocalDualCoordinateSubmodule
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] :
    primePowCoordinateSubmodule (n := n) p k ≤
      pairingMatrixLocalDualCoordinateSubmodule L p k := by
  intro x hx
  rw [pairingMatrixLocalDualCoordinateSubmodule, LinearMap.mem_ker]
  ext i
  have hxzero :
      ∀ j : Fin n, (x j : ZMod (primePowModulus p k : ℕ)) = 0 :=
    (mem_primePowCoordinateSubmodule_iff_coordinate_zmod_eq_zero
      (n := n) p k x).mp hx
  simp [matrixModLinearMap, Matrix.mulVec, dotProduct, hxzero]

lemma pairingMatrixLocalDualCoordinateSubmodule_le_primePowCoordinateSubmodule_of_zmod_isUnit
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hF : IsUnit (matrixMod L.pairingMatrix (primePowModulus p k))) :
    pairingMatrixLocalDualCoordinateSubmodule L p k ≤
      primePowCoordinateSubmodule (n := n) p k := by
  intro x hx
  rw [mem_primePowCoordinateSubmodule_iff_coordinate_zmod_eq_zero]
  let m : ℕ+ := primePowModulus p k
  let F : Matrix (Fin n) (Fin n) (ZMod (m : ℕ)) := matrixMod L.pairingMatrix m
  let v : Fin n → ZMod (m : ℕ) := fun i => (x i : ZMod (m : ℕ))
  have hFx : F.mulVec v = 0 := by
    simpa [pairingMatrixLocalDualCoordinateSubmodule, matrixModLinearMap, F, v, m]
      using hx
  have hF_unit : IsUnit F := by
    simpa [F, m] using hF
  have hF_det : IsUnit F.det := by
    rwa [Matrix.isUnit_iff_isUnit_det] at hF_unit
  have hleft : F⁻¹ * F = 1 := Matrix.nonsing_inv_mul F hF_det
  have hv_zero : v = 0 := by
    calc
      v = (1 : Matrix (Fin n) (Fin n) (ZMod (m : ℕ))).mulVec v := by simp
      _ = (F⁻¹ * F).mulVec v := by rw [hleft]
      _ = F⁻¹.mulVec (F.mulVec v) := by rw [Matrix.mulVec_mulVec]
      _ = 0 := by rw [hFx]; simp
  intro i
  exact congr_fun hv_zero i

lemma pairingMatrixLocalDualCoordinateSubmodule_eq_primePowCoordinateSubmodule_of_zmod_isUnit
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hF : IsUnit (matrixMod L.pairingMatrix (primePowModulus p k))) :
    pairingMatrixLocalDualCoordinateSubmodule L p k =
      primePowCoordinateSubmodule (n := n) p k := by
  exact le_antisymm
    (pairingMatrixLocalDualCoordinateSubmodule_le_primePowCoordinateSubmodule_of_zmod_isUnit
      (n := n) L p k hF)
    (primePowCoordinateSubmodule_le_pairingMatrixLocalDualCoordinateSubmodule
      (n := n) L p k)

lemma pairingMatrixLocalDualCoordinateSubmodule_rank
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] :
    Module.finrank ℤ (pairingMatrixLocalDualCoordinateSubmodule L p k) = n := by
  have hmono := Submodule.finrank_mono
    (primePowCoordinateSubmodule_le_pairingMatrixLocalDualCoordinateSubmodule
      (n := n) L p k)
  have hupper :
      Module.finrank ℤ (pairingMatrixLocalDualCoordinateSubmodule L p k) ≤ n := by
    simpa [Module.finrank_pi] using
      (pairingMatrixLocalDualCoordinateSubmodule L p k).finrank_le
  have hlower :
      n ≤ Module.finrank ℤ (pairingMatrixLocalDualCoordinateSubmodule L p k) := by
    simpa [primePowCoordinateSubmodule_rank (n := n) p k] using hmono
  exact le_antisymm hupper hlower

lemma localDualPadicCoordinateSubmodule_rank
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] :
    Module.finrank ℤ (localDualPadicCoordinateSubmodule L p k) = n := by
  rw [localDualPadicCoordinateSubmodule_eq_pairingMatrixLocalDualCoordinateSubmodule]
  exact pairingMatrixLocalDualCoordinateSubmodule_rank (n := n) L p k

lemma localDualPadicDenominatorIntegralPreimage_rank
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] :
    Module.finrank ℤ (localDualPadicDenominatorIntegralPreimage L p k) = n := by
  rw [localDualPadicDenominatorIntegralPreimage_eq_localDualPadicCoordinateSubmodule]
  exact localDualPadicCoordinateSubmodule_rank (n := n) L p k

lemma associatedBilinearDualPadicDenominatorIntegralPreimage_rank
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] :
    Module.finrank ℤ
      (associatedBilinearDualPadicDenominatorIntegralPreimage L p k) = n := by
  by_cases hp_two : p = 2
  · subst p
    cases k with
    | zero =>
        rw [L.associatedBilinearDualPadicDenominatorIntegralPreimage_zero_eq_top]
        simp
    | succ k =>
        rw [L.associatedBilinearDualPadicDenominatorIntegralPreimage_succ_eq_localDualPadicDenominatorIntegralPreimage_dyadic]
        exact localDualPadicDenominatorIntegralPreimage_rank (n := n) L 2 k
  · rw [L.associatedBilinearDualPadicDenominatorIntegralPreimage_eq_localDualPadicDenominatorIntegralPreimage_of_ne_two
      p k hp_two]
    exact localDualPadicDenominatorIntegralPreimage_rank (n := n) L p k

lemma padicSubmoduleIntegralPreimage_localDualPadicDenominator_rank
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] :
    Module.finrank ℤ
        (padicSubmoduleIntegralPreimage (n := n) p
          (localDualPadicDenominator L p k)) = n := by
  rw [← localDualPadicDenominatorIntegralPreimage_eq_padicSubmoduleIntegralPreimage]
  exact localDualPadicDenominatorIntegralPreimage_rank (n := n) L p k

lemma primePowQuotientVector_injective
    (p k : ℕ) [Fact (Nat.Prime p)] :
    Function.Injective
      (primePowQuotientVector (n := n) p k :
        localDualQuotientTarget (primePowCoordinateSubmodule (n := n) p k) →
          Fin n → ZMod (primePowModulus p k : ℕ)) := by
  intro q r hqr
  revert r
  refine Quotient.inductionOn q ?_
  intro x r hxr
  revert hxr
  refine Quotient.inductionOn r ?_
  intro y hxy
  change (Submodule.Quotient.mk x :
      (Fin n → ℤ) ⧸ primePowCoordinateSubmodule (n := n) p k) =
    Submodule.Quotient.mk y
  rw [Submodule.Quotient.eq]
  rw [mem_primePowCoordinateSubmodule_iff_coordinate_zmod_eq_zero]
  intro i
  have hi := congr_fun hxy i
  simpa [primePowQuotientVector_mkQ, Int.cast_sub] using sub_eq_zero.mpr hi

/-- A family of images of the coordinate basis determines the corresponding
`ℤ`-linear map from the based lattice to the finite coordinate quotient. -/
def quotientBasisFamilyMap (D : Submodule ℤ (Fin n → ℤ))
    (Y : Fin n → localDualQuotientTarget D) (x : Fin n → ℤ) :
    localDualQuotientTarget D :=
  ∑ i : Fin n, (x i) • Y i

/-- The basis-image family of the quotient map induced by the identity
`ℤ^n → ℤ^n / D`. -/
def quotientIdentityBasisFamily (D : Submodule ℤ (Fin n → ℤ)) :
    Fin n → localDualQuotientTarget D :=
  fun i => D.mkQ ((Pi.basisFun ℤ (Fin n)) i)

lemma quotientBasisFamilyMap_identity (D : Submodule ℤ (Fin n → ℤ))
    (x : Fin n → ℤ) :
    quotientBasisFamilyMap D (quotientIdentityBasisFamily D) x = D.mkQ x := by
  classical
  have hsum :
      (∑ i : Fin n, (x i) • D.mkQ ((Pi.basisFun ℤ (Fin n)) i)) =
        D.mkQ (∑ i : Fin n, (x i) • (Pi.basisFun ℤ (Fin n)) i) := by
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    exact (map_zsmul D.mkQ (x i) ((Pi.basisFun ℤ (Fin n)) i)).symm
  have hrepr :
      (∑ i : Fin n, (x i) • (Pi.basisFun ℤ (Fin n)) i) = x := by
    simpa using (Pi.basisFun ℤ (Fin n)).sum_repr x
  calc
    quotientBasisFamilyMap D (quotientIdentityBasisFamily D) x =
        D.mkQ (∑ i : Fin n, (x i) • (Pi.basisFun ℤ (Fin n)) i) := by
          simpa [quotientBasisFamilyMap, quotientIdentityBasisFamily] using hsum
    _ = D.mkQ x := by rw [hrepr]

lemma quotientBasisFamilyMap_add (D : Submodule ℤ (Fin n → ℤ))
    (Y : Fin n → localDualQuotientTarget D) (x y : Fin n → ℤ) :
    quotientBasisFamilyMap D Y (x + y) =
      quotientBasisFamilyMap D Y x + quotientBasisFamilyMap D Y y := by
  classical
  simp [quotientBasisFamilyMap, Pi.add_apply, add_smul, Finset.sum_add_distrib]

set_option backward.isDefEq.respectTransparency false in
lemma quotientBasisFamilyMap_zsmul (D : Submodule ℤ (Fin n → ℤ))
    (Y : Fin n → localDualQuotientTarget D) (a : ℤ) (x : Fin n → ℤ) :
    quotientBasisFamilyMap D Y (a • x) =
      a • quotientBasisFamilyMap D Y x := by
  classical
  simp [quotientBasisFamilyMap, Pi.smul_apply, Finset.smul_sum, smul_smul]

/-- The quotient map induced by enlarging a coordinate denominator. -/
def localDualQuotientMapOfLE
    {D E : Submodule ℤ (Fin n → ℤ)} (hDE : D ≤ E) :
    localDualQuotientTarget D →ₗ[ℤ] localDualQuotientTarget E :=
  D.mapQ E LinearMap.id hDE

@[simp] lemma localDualQuotientMapOfLE_mkQ
    {D E : Submodule ℤ (Fin n → ℤ)} (hDE : D ≤ E)
    (x : Fin n → ℤ) :
    localDualQuotientMapOfLE (n := n) hDE (D.mkQ x) = E.mkQ x := rfl

lemma localDualQuotientMapOfLE_surjective
    {D E : Submodule ℤ (Fin n → ℤ)} (hDE : D ≤ E) :
    Function.Surjective (localDualQuotientMapOfLE (n := n) hDE) := by
  intro q
  refine Quotient.inductionOn q ?_
  intro x
  exact ⟨D.mkQ x, rfl⟩

/-- A nonempty fiber of a `ℤ`-linear map is a translate of its kernel. -/
def linearMapFiberEquivKerOfPreimage
    {A B : Type*} [AddCommGroup A] [AddCommGroup B] [Module ℤ A] [Module ℤ B]
    (f : A →ₗ[ℤ] B) (b : B) (a₀ : A) (ha₀ : f a₀ = b) :
    LinearMap.ker f ≃ {a : A // f a = b} where
  toFun k := ⟨a₀ + k.1, by simp [ha₀, LinearMap.mem_ker.mp k.2]⟩
  invFun a := ⟨a.1 - a₀, by simp [LinearMap.mem_ker, a.2, ha₀]⟩
  left_inv k := by
    ext
    simp
  right_inv a := by
    ext
    simp

lemma linearMap_fiber_card_eq_ker_of_preimage
    {A B : Type*} [AddCommGroup A] [AddCommGroup B] [Module ℤ A] [Module ℤ B]
    (f : A →ₗ[ℤ] B) (b : B) (a₀ : A) (ha₀ : f a₀ = b) :
    Nat.card {a : A // f a = b} = Nat.card (LinearMap.ker f) := by
  exact Nat.card_congr
    (linearMapFiberEquivKerOfPreimage f b a₀ ha₀).symm

/-- A finite type is the disjoint union of the fibers of any map out of it.
This is the cardinality bookkeeping used after the local-dual quotient fiber
has been computed uniformly. -/
lemma nat_card_eq_mul_of_fiber_card
    {α β : Type*} [Fintype α] [Fintype β] (f : α → β) (c : ℕ)
    (hfiber : ∀ b : β, Nat.card {a : α // f a = b} = c) :
    Nat.card α = Nat.card β * c := by
  classical
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  have hcard :
      Fintype.card α =
        ∑ b : β, ((Finset.univ : Finset α).filter fun a => f a = b).card := by
    simpa only [Finset.card_univ, Finset.mem_univ, true_implies] using
      (Finset.card_eq_sum_card_fiberwise
        (s := (Finset.univ : Finset α)) (t := (Finset.univ : Finset β))
        (f := f) (by intro a _ha; simp))
  calc
    Fintype.card α =
        ∑ b : β, ((Finset.univ : Finset α).filter fun a => f a = b).card := hcard
    _ = ∑ _b : β, c := by
          refine Finset.sum_congr rfl ?_
          intro b _hb
          rw [← hfiber b, Nat.card_eq_fintype_card]
          simp [Fintype.card_subtype]
    _ = Fintype.card β * c := by simp

/-- The fiber of a coordinatewise map on finite dependent functions is the
product of the one-coordinate fibers.  In the local-density application this
is the finite product over the `n` matrix columns. -/
lemma nat_card_pi_map_fiber_eq_pow
    {ι α β : Type*} [DecidableEq ι] [Fintype ι] [Fintype α] [Fintype β]
    (f : α → β) (y : ι → β) (c : ℕ)
    (hfiber : ∀ b : β, Nat.card {a : α // f a = b} = c) :
    Nat.card {x : ι → α // (fun i : ι => f (x i)) = y} =
      c ^ Fintype.card ι := by
  classical
  let e : {x : ι → α // (fun i : ι => f (x i)) = y} ≃
      ((i : ι) → {a : α // f a = y i}) :=
    { toFun := fun x => fun i => ⟨x.1 i, congr_fun x.2 i⟩
      invFun := fun g => ⟨fun i => (g i).1, by
        ext i
        exact (g i).2⟩
      left_inv := by
        intro x
        ext i
        rfl
      right_inv := by
        intro g
        ext i
        rfl }
  calc
    Nat.card {x : ι → α // (fun i : ι => f (x i)) = y} =
        Nat.card ((i : ι) → {a : α // f a = y i}) := Nat.card_congr e
    _ = Fintype.card ((i : ι) → {a : α // f a = y i}) := by
          rw [Nat.card_eq_fintype_card]
    _ = ∏ i : ι, Fintype.card {a : α // f a = y i} := by
          exact Fintype.card_pi
    _ = ∏ _i : ι, c := by
          refine Finset.prod_congr rfl ?_
          intro i _hi
          rw [← Nat.card_eq_fintype_card, hfiber]
    _ = c ^ Fintype.card ι := by
          simp

lemma localDualQuotientMapOfLE_fiber_card_eq_ker
    {D E : Submodule ℤ (Fin n → ℤ)} (hDE : D ≤ E)
    (q : localDualQuotientTarget E) :
    Nat.card
        {x : localDualQuotientTarget D //
          localDualQuotientMapOfLE (n := n) hDE x = q} =
      Nat.card
        (LinearMap.ker (localDualQuotientMapOfLE (n := n) hDE)) := by
  classical
  let q₀ := Classical.choose
    (localDualQuotientMapOfLE_surjective (n := n) hDE q)
  have hq₀ :
      localDualQuotientMapOfLE (n := n) hDE q₀ = q :=
    Classical.choose_spec
      (localDualQuotientMapOfLE_surjective (n := n) hDE q)
  exact linearMap_fiber_card_eq_ker_of_preimage
    (localDualQuotientMapOfLE (n := n) hDE) q q₀ hq₀

/-- The kernel of the quotient map `ℤ^n / D → ℤ^n / E` is the image of `E`
inside `ℤ^n / D`. -/
lemma localDualQuotientMapOfLE_ker_eq_map
    {D E : Submodule ℤ (Fin n → ℤ)} (hDE : D ≤ E) :
    LinearMap.ker (localDualQuotientMapOfLE (n := n) hDE) = E.map D.mkQ := by
  ext q
  refine Quotient.inductionOn q ?_
  intro x
  constructor
  · intro hx
    rw [LinearMap.mem_ker] at hx
    have hxE : x ∈ E := by
      simpa [Submodule.mkQ_apply] using (Submodule.Quotient.mk_eq_zero E).mp hx
    exact ⟨x, hxE, rfl⟩
  · intro hx
    rcases hx with ⟨y, hyE, hyq⟩
    rw [LinearMap.mem_ker]
    have hxyD : x - y ∈ D := by
      rw [← Submodule.Quotient.eq]
      exact hyq.symm
    have hxE : x ∈ E := by
      have hsum : x - y + y ∈ E := E.add_mem (hDE hxyD) hyE
      simpa [sub_add_cancel] using hsum
    exact (Submodule.Quotient.mk_eq_zero E).mpr hxE

set_option backward.isDefEq.respectTransparency false in
/-- The image of `E` in `ℤ^n / D` has the cardinality of the subquotient
`E / (D ∩ E)`, written as the comap of `D` along `E.subtype`. -/
lemma localDualQuotientMapOfLE_map_card_eq_subquotient
    (D E : Submodule ℤ (Fin n → ℤ)) :
    Nat.card (E.map D.mkQ) = Nat.card (E ⧸ D.comap E.subtype) := by
  let f : E →ₗ[ℤ] ((Fin n → ℤ) ⧸ D) := D.mkQ.domRestrict E
  have hfker : LinearMap.ker f = D.comap E.subtype := by
    ext x
    change D.mkQ x.1 = 0 ↔ x.1 ∈ D
    exact Submodule.Quotient.mk_eq_zero D
  have hfrange : LinearMap.range f = E.map D.mkQ := by
    ext q
    constructor
    · intro hq
      rcases hq with ⟨x, rfl⟩
      exact ⟨x.1, x.2, rfl⟩
    · intro hq
      rcases hq with ⟨x, hxE, rfl⟩
      exact ⟨⟨x, hxE⟩, rfl⟩
  calc
    Nat.card (E.map D.mkQ) = Nat.card (LinearMap.range f) := by rw [hfrange]
    _ = Nat.card (E ⧸ LinearMap.ker f) := by
      exact Nat.card_congr f.quotKerEquivRange.symm.toEquiv
    _ = Nat.card (E ⧸ D.comap E.subtype) := by rw [hfker]

/-- The kernel cardinal of `ℤ^n / D → ℤ^n / E` is the cardinality of the
denominator subquotient `E / (D ∩ E)`. -/
lemma localDualQuotientMapOfLE_ker_card_eq_subquotient
    {D E : Submodule ℤ (Fin n → ℤ)} (hDE : D ≤ E) :
    Nat.card (LinearMap.ker (localDualQuotientMapOfLE (n := n) hDE)) =
      Nat.card (E ⧸ D.comap E.subtype) := by
  rw [localDualQuotientMapOfLE_ker_eq_map (n := n) hDE]
  exact localDualQuotientMapOfLE_map_card_eq_subquotient (n := n) D E

/-- Casting the integral-integral model quotients to the corresponding `p`-adic
quotients commutes with the adjacent-depth quotient maps. -/
lemma localDualPadicDenominatorIntegralPreimageQuotientEquiv_commutes_succ
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (q : (Fin n → ℤ) ⧸ localDualPadicDenominatorIntegralPreimage L p (k + 1)) :
    padicSubmoduleQuotientMapOfLE (n := n)
        (localDualPadicDenominator_succ_le L p k)
        (localDualPadicDenominatorIntegralPreimageQuotientEquiv L p (k + 1) q) =
      localDualPadicDenominatorIntegralPreimageQuotientEquiv L p k
        (localDualQuotientMapOfLE (n := n)
          (localDualPadicDenominatorIntegralPreimage_succ_le L p k) q) := by
  induction q using Quotient.inductionOn with
  | h x => rfl

set_option backward.isDefEq.respectTransparency false in
/-- The one-column correction kernel in the finite integral-integral model quotient
is the kernel of the adjacent map between the corresponding `p`-adic
quotients. -/
noncomputable def
    localDualPadicDenominatorIntegralPreimageSuccKernelEquivPadic
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] :
    LinearMap.ker (localDualQuotientMapOfLE (n := n)
        (localDualPadicDenominatorIntegralPreimage_succ_le L p k)) ≃ₗ[ℤ]
      LinearMap.ker ((padicSubmoduleQuotientMapOfLE (n := n)
        (localDualPadicDenominator_succ_le L p k)).restrictScalars ℤ) where
  toFun q := ⟨
    localDualPadicDenominatorIntegralPreimageQuotientEquiv L p (k + 1) q.1,
    by
      rw [LinearMap.mem_ker]
      change padicSubmoduleQuotientMapOfLE (n := n)
        (localDualPadicDenominator_succ_le L p k)
          (localDualPadicDenominatorIntegralPreimageQuotientEquiv
            L p (k + 1) q.1) = 0
      rw [localDualPadicDenominatorIntegralPreimageQuotientEquiv_commutes_succ]
      rw [LinearMap.mem_ker.mp q.2]
      exact map_zero _⟩
  invFun q := ⟨
    (localDualPadicDenominatorIntegralPreimageQuotientEquiv
      L p (k + 1)).symm q.1,
    by
      rw [LinearMap.mem_ker]
      apply (localDualPadicDenominatorIntegralPreimageQuotientEquiv
        L p k).injective
      rw [map_zero]
      rw [← localDualPadicDenominatorIntegralPreimageQuotientEquiv_commutes_succ]
      rw [LinearEquiv.apply_symm_apply]
      exact LinearMap.mem_ker.mp q.2⟩
  left_inv q := by
    ext
    exact LinearEquiv.symm_apply_apply _ q.1
  right_inv q := by
    ext
    exact LinearEquiv.apply_symm_apply _ q.1
  map_add' q r := by
    ext
    simp
  map_smul' a q := by
    ext
    simp

/-- The integral-integral model correction kernel is the adjacent `p`-adic
denominator subquotient. -/
noncomputable def
    localDualPadicDenominatorIntegralPreimageSuccKernelEquivPadicSubquotient
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] :
    LinearMap.ker (localDualQuotientMapOfLE (n := n)
        (localDualPadicDenominatorIntegralPreimage_succ_le L p k)) ≃ₗ[ℤ]
      localDualPadicDenominator L p k ⧸
        (localDualPadicDenominator L p (k + 1)).comap
          (localDualPadicDenominator L p k).subtype :=
  (localDualPadicDenominatorIntegralPreimageSuccKernelEquivPadic L p k).trans
    ((padicSubmoduleQuotientMapOfLEKerEquivSubquotient (n := n)
      (localDualPadicDenominator_succ_le L p k)).restrictScalars ℤ)

/-- Under exact lattice depth, the one-column correction kernel is
`D_k / p D_k`. -/
noncomputable def
    localDualPadicDenominatorIntegralPreimageSuccKernelEquivPrimeSubquotient
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : L.IsHenselLatticeDepth p k) :
    LinearMap.ker (localDualQuotientMapOfLE (n := n)
        (localDualPadicDenominatorIntegralPreimage_succ_le L p k)) ≃ₗ[ℤ]
      localDualPadicDenominator L p k ⧸
        localDualPadicDenominatorPrimeSubmodule L p k := by
  unfold localDualPadicDenominatorPrimeSubmodule
  rw [← localDualPadicDenominator_succ_eq_map_prime_smul L p k hk]
  exact
    localDualPadicDenominatorIntegralPreimageSuccKernelEquivPadicSubquotient
      L p k

/-- Casting source integral-integral model quotients to their p-adic quotients
commutes with source adjacent reduction. -/
lemma
    associatedBilinearDualPadicDenominatorIntegralPreimageQuotientEquiv_commutes_succ
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (q : (Fin n → ℤ) ⧸
      associatedBilinearDualPadicDenominatorIntegralPreimage L p (k + 1)) :
    padicSubmoduleQuotientMapOfLE (n := n)
        (associatedBilinearDualPadicDenominator_succ_le L p k)
        (associatedBilinearDualPadicDenominatorIntegralPreimageQuotientEquiv
          L p (k + 1) q) =
      associatedBilinearDualPadicDenominatorIntegralPreimageQuotientEquiv
        L p k
        (localDualQuotientMapOfLE (n := n)
          (associatedBilinearDualPadicDenominatorIntegralPreimage_succ_le
            L p k) q) := by
  induction q using Quotient.inductionOn with
  | h x => rfl

set_option backward.isDefEq.respectTransparency false in
/-- The source integral-integral model correction kernel is its p-adic adjacent
quotient kernel. -/
noncomputable def
    associatedBilinearDualPadicDenominatorIntegralPreimageSuccKernelEquivPadic
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] :
    LinearMap.ker (localDualQuotientMapOfLE (n := n)
        (associatedBilinearDualPadicDenominatorIntegralPreimage_succ_le
          L p k)) ≃ₗ[ℤ]
      LinearMap.ker ((padicSubmoduleQuotientMapOfLE (n := n)
        (associatedBilinearDualPadicDenominator_succ_le L p k)).restrictScalars
          ℤ) where
  toFun q :=
    ⟨associatedBilinearDualPadicDenominatorIntegralPreimageQuotientEquiv
        L p (k + 1) q.1, by
      rw [LinearMap.mem_ker]
      change padicSubmoduleQuotientMapOfLE (n := n)
        (associatedBilinearDualPadicDenominator_succ_le L p k)
          (associatedBilinearDualPadicDenominatorIntegralPreimageQuotientEquiv
            L p (k + 1) q.1) = 0
      rw [associatedBilinearDualPadicDenominatorIntegralPreimageQuotientEquiv_commutes_succ]
      rw [LinearMap.mem_ker.mp q.2]
      exact map_zero _⟩
  invFun q :=
    ⟨(associatedBilinearDualPadicDenominatorIntegralPreimageQuotientEquiv
        L p (k + 1)).symm q.1, by
      rw [LinearMap.mem_ker]
      apply
        (associatedBilinearDualPadicDenominatorIntegralPreimageQuotientEquiv
          L p k).injective
      rw [map_zero]
      rw [←
        associatedBilinearDualPadicDenominatorIntegralPreimageQuotientEquiv_commutes_succ]
      rw [LinearEquiv.apply_symm_apply]
      exact LinearMap.mem_ker.mp q.2⟩
  left_inv q := by
    ext
    exact LinearEquiv.symm_apply_apply _ q.1
  right_inv q := by
    ext
    exact LinearEquiv.apply_symm_apply _ q.1
  map_add' q r := by
    ext
    simp
  map_smul' a q := by
    ext
    simp

/-- The source integral-integral model correction kernel is the adjacent source
p-adic denominator subquotient. -/
noncomputable def
    associatedBilinearDualPadicDenominatorIntegralPreimageSuccKernelEquivPadicSubquotient
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] :
    LinearMap.ker (localDualQuotientMapOfLE (n := n)
        (associatedBilinearDualPadicDenominatorIntegralPreimage_succ_le
          L p k)) ≃ₗ[ℤ]
      associatedBilinearDualPadicDenominator L p k ⧸
        (associatedBilinearDualPadicDenominator L p (k + 1)).comap
          (associatedBilinearDualPadicDenominator L p k).subtype :=
  (associatedBilinearDualPadicDenominatorIntegralPreimageSuccKernelEquivPadic
    L p k).trans
    ((padicSubmoduleQuotientMapOfLEKerEquivSubquotient (n := n)
      (associatedBilinearDualPadicDenominator_succ_le L p k)).restrictScalars
        ℤ)

/-- The quotient map `ℤ^n / D → ℤ^n / E` gives the cardinality product
`#(ℤ^n / D) = #(E / (D ∩ E)) * #(ℤ^n / E)`. -/
lemma localDualQuotientMapOfLE_domain_card_eq_subquotient_mul_codomain_card
    {D E : Submodule ℤ (Fin n → ℤ)} (hDE : D ≤ E) :
    Nat.card (localDualQuotientTarget D) =
      Nat.card (E ⧸ D.comap E.subtype) *
        Nat.card (localDualQuotientTarget E) := by
  classical
  let f := localDualQuotientMapOfLE (n := n) hDE
  have hker :
      Nat.card (LinearMap.ker f) =
        Nat.card (E ⧸ D.comap E.subtype) := by
    rw [localDualQuotientMapOfLE_ker_card_eq_subquotient (n := n) hDE]
  have hcard := AddSubgroup.card_mul_index (LinearMap.ker f).toAddSubgroup
  have hindex :
      (LinearMap.ker f).toAddSubgroup.index =
        Nat.card (localDualQuotientTarget E) := by
    have hker_add :
        (LinearMap.ker f).toAddSubgroup = f.toAddMonoidHom.ker := rfl
    rw [hker_add, AddSubgroup.index_ker f.toAddMonoidHom]
    have hrange_top : f.toAddMonoidHom.range = ⊤ := by
      exact AddMonoidHom.range_eq_top.mpr
        (localDualQuotientMapOfLE_surjective (n := n) hDE)
    rw [hrange_top]
    exact Nat.card_congr AddSubgroup.topEquiv.toEquiv
  rw [hindex] at hcard
  rw [← hcard]
  change Nat.card (LinearMap.ker f) * Nat.card (localDualQuotientTarget E) =
    Nat.card (E ⧸ D.comap E.subtype) * Nat.card (localDualQuotientTarget E)
  rw [hker]

lemma primePowCoordinateSubmodule_zero_eq_top
    (p : ℕ) [Fact (Nat.Prime p)] :
    primePowCoordinateSubmodule (n := n) p 0 = ⊤ := by
  ext x
  constructor
  · intro _
    trivial
  · intro _
    refine ⟨x, ?_⟩
    ext i
    simp

/-- The clean coordinate quotient `ℤ^n / p^kℤ^n` has cardinal `p^(n*k)`. -/
lemma primePowCoordinateSubmodule_quotient_card
    (p k : ℕ) [Fact (Nat.Prime p)] :
    Nat.card ((Fin n → ℤ) ⧸ primePowCoordinateSubmodule (n := n) p k) =
      p ^ (n * k) := by
  let D : Submodule ℤ (Fin n → ℤ) := primePowCoordinateSubmodule (n := n) p k
  let E : Submodule ℤ (Fin n → ℤ) := ⊤
  have hDE : D ≤ E := le_top
  have hexact :=
    localDualQuotientMapOfLE_domain_card_eq_subquotient_mul_codomain_card
      (n := n) hDE
  have hsub := primePowCoordinateSubmodule_subquotient_card (n := n) p k k le_rfl
  rw [Nat.sub_self] at hsub
  rw [primePowCoordinateSubmodule_zero_eq_top (n := n) p] at hsub
  have hEcard : Nat.card (localDualQuotientTarget E) = 1 := by
    exact nat_card_quotient_top_integral_coordinates (n := n)
  rw [hsub, hEcard, mul_one] at hexact
  simpa [D] using hexact

/-- If `E` is any coordinate denominator containing `p^kℤ^n`, then its
subquotient by `p^kℤ^n` and its ambient quotient index multiply to
`p^(n*k)`. -/
lemma primePowCoordinateSubmodule_subquotient_card_mul_quotient_card
    (p k : ℕ) [Fact (Nat.Prime p)]
    (E : Submodule ℤ (Fin n → ℤ))
    (hDE : primePowCoordinateSubmodule (n := n) p k ≤ E) :
    Nat.card (E ⧸ (primePowCoordinateSubmodule (n := n) p k).comap E.subtype) *
        Nat.card ((Fin n → ℤ) ⧸ E) =
      p ^ (n * k) := by
  have hexact :=
    localDualQuotientMapOfLE_domain_card_eq_subquotient_mul_codomain_card
      (n := n) hDE
  rw [primePowCoordinateSubmodule_quotient_card (n := n) p k] at hexact
  exact hexact.symm

/-- A quotient-index computation for a denominator `E` containing `p^kℤ^n`
determines the one-column denominator subquotient cardinal. -/
lemma primePowCoordinateSubmodule_subquotient_card_eq_prime_pow_of_quotient_card
    (p k : ℕ) [Fact (Nat.Prime p)]
    (E : Submodule ℤ (Fin n → ℤ))
    (hDE : primePowCoordinateSubmodule (n := n) p k ≤ E)
    (w : ℕ) (hw : w ≤ n * k)
    (hcard : Nat.card ((Fin n → ℤ) ⧸ E) = p ^ w) :
    Nat.card (E ⧸ (primePowCoordinateSubmodule (n := n) p k).comap E.subtype) =
      p ^ (n * k - w) := by
  have hmul :=
    primePowCoordinateSubmodule_subquotient_card_mul_quotient_card
      (n := n) p k E hDE
  rw [hcard] at hmul
  have hpw_pos : 0 < p ^ w := pow_pos (Fact.out : Nat.Prime p).pos w
  have hpow : p ^ (n * k) = p ^ (n * k - w) * p ^ w := by
    rw [← Nat.pow_add, Nat.sub_add_cancel hw]
  rw [hpow] at hmul
  exact Nat.eq_of_mul_eq_mul_right hpw_pos hmul

/-- A computed ambient index for the form-matrix local-dual denominator gives
the one-column correction cardinal needed by the odd-prime count comparison. -/
lemma pairingMatrixLocalDualCoordinateSubmodule_subquotient_card_eq_prime_pow_of_quotient_card
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (w : ℕ) (hw : w ≤ n * k)
    (hcard :
      Nat.card ((Fin n → ℤ) ⧸ pairingMatrixLocalDualCoordinateSubmodule L p k) =
        p ^ w) :
    Nat.card
        (pairingMatrixLocalDualCoordinateSubmodule L p k ⧸
          (primePowCoordinateSubmodule (n := n) p k).comap
            (pairingMatrixLocalDualCoordinateSubmodule L p k).subtype) =
      p ^ (n * k - w) :=
  primePowCoordinateSubmodule_subquotient_card_eq_prime_pow_of_quotient_card
    (n := n) p k (pairingMatrixLocalDualCoordinateSubmodule L p k)
    (primePowCoordinateSubmodule_le_pairingMatrixLocalDualCoordinateSubmodule
      (n := n) L p k)
    w hw hcard

/-- The ambient quotient index of the diagonal denominator is the product of
the remaining coordinate moduli `p^(k-v_i)`. -/
lemma diagonalPrimePowCoordinateSubmodule_quotient_card
    (p k : ℕ) [Fact (Nat.Prime p)]
    (v : Fin n → ℕ) (hv : ∀ i, v i ≤ k) :
    Nat.card
        ((Fin n → ℤ) ⧸ diagonalPrimePowCoordinateSubmodule (n := n) p k v) =
      p ^ (∑ i : Fin n, (k - v i)) := by
  let E : Submodule ℤ (Fin n → ℤ) :=
    diagonalPrimePowCoordinateSubmodule (n := n) p k v
  have hDE : primePowCoordinateSubmodule (n := n) p k ≤ E :=
    primePowCoordinateSubmodule_le_diagonalPrimePowCoordinateSubmodule
      (n := n) p k v hv
  have hmul :=
    primePowCoordinateSubmodule_subquotient_card_mul_quotient_card
      (n := n) p k E hDE
  have hsub :=
    diagonalPrimePowCoordinateSubmodule_subquotient_card (n := n) p k v hv
  let w : Fin n → ℕ := fun i => k - v i
  have hsum :
      (∑ i : Fin n, v i) + (∑ i : Fin n, w i) = n * k := by
    calc
      (∑ i : Fin n, v i) + (∑ i : Fin n, w i)
          = ∑ i : Fin n, (v i + w i) := by
              simpa using (Finset.sum_add_distrib (s := Finset.univ)
                (f := fun i : Fin n => v i) (g := fun i : Fin n => w i)).symm
      _ = ∑ _i : Fin n, k := by
              refine Finset.sum_congr rfl ?_
              intro i _hi
              simp [w, Nat.add_sub_of_le (hv i)]
      _ = n * k := by
              simp [Fintype.card_fin]
  have hpow : p ^ (n * k) =
      p ^ (∑ i : Fin n, v i) * p ^ (∑ i : Fin n, w i) := by
    rw [← hsum, Nat.pow_add]
  rw [hsub, hpow] at hmul
  simpa [w] using
    (Nat.eq_of_mul_eq_mul_left
      (pow_pos (Fact.out : Nat.Prime p).pos (∑ i : Fin n, v i)) hmul)

/-- Smith-normal-form input for diagonal entries whose `p`-primary exponent
has been truncated at `k`: unit factors are required only for entries with
exponent `< k`; entries with exponent `k` vanish modulo `p^k` regardless of
the remaining factor. -/
lemma matrixModLinearMap_ker_quotient_card_of_left_right_mul_eq_diagonal_units_prime_pows_of_lt
    (A P Q : Matrix (Fin n) (Fin n) ℤ)
    (p k : ℕ) [Fact (Nat.Prime p)]
    (u : Fin n → ℤ) (v : Fin n → ℕ) (hv : ∀ i, v i ≤ k)
    (hunit : ∀ i : Fin n, v i < k →
      IsUnit (((u i : ℤ) : ZMod (primePowModulus p k : ℕ))))
    (hP : IsUnit P) (hQ : IsUnit Q)
    (hdiag : P * A * Q = Matrix.diagonal (fun i : Fin n => u i * (p ^ v i : ℤ))) :
    Nat.card
        ((Fin n → ℤ) ⧸ LinearMap.ker (matrixModLinearMap (n := n) A p k)) =
      p ^ (∑ i : Fin n, (k - v i)) := by
  have htransport :=
    matrixModLinearMap_ker_left_right_mul_quotient_card_eq
      (n := n) A P Q p k hP hQ
  have hdiag_card :
      Nat.card
          ((Fin n → ℤ) ⧸
            LinearMap.ker (matrixModLinearMap (n := n) (P * A * Q) p k)) =
        p ^ (∑ i : Fin n, (k - v i)) := by
    rw [hdiag, matrixModLinearMap_ker_eq_diagonal_units_prime_pows_of_lt
      (n := n) p k u v hv hunit]
    exact diagonalPrimePowCoordinateSubmodule_quotient_card (n := n) p k v hv
  rwa [htransport] at hdiag_card

/-- Every integral diagonal coefficient can be written as a truncated
`p`-power times a coefficient that is a unit modulo `p^k` whenever the
truncated exponent is still `< k`.

For zero coefficients the exponent is chosen to be `k`, so no unit hypothesis
is needed. -/
lemma exists_truncated_padic_unit_factor
    (p k : ℕ) [Fact (Nat.Prime p)] (a : ℤ) :
    ∃ u : ℤ, ∃ v : ℕ,
      v ≤ k ∧
        (∀ _hv : v < k,
          IsUnit (((u : ℤ) : ZMod (primePowModulus p k : ℕ)))) ∧
        a = u * (p ^ v : ℤ) := by
  classical
  by_cases ha : a = 0
  · refine ⟨0, k, le_rfl, ?_, ?_⟩
    · intro hv
      exact (False.elim (Nat.lt_irrefl k hv))
    · simp [ha]
  · let v : ℕ := min k (padicValInt p a)
    have hv_le_k : v ≤ k := min_le_left _ _
    have hv_le_val : v ≤ padicValInt p a := min_le_right _ _
    have hpow_dvd : (p : ℤ) ^ v ∣ a := by
      exact (pow_dvd_pow (p : ℤ) hv_le_val).trans (padicValInt_dvd (p := p) a)
    rcases hpow_dvd with ⟨u, hu⟩
    refine ⟨u, v, hv_le_k, ?_, ?_⟩
    · intro hv_lt
      have hv_eq_val : v = padicValInt p a := by
        have hval_lt_k : padicValInt p a < k := by
          by_contra hnot
          have hk_le_val : k ≤ padicValInt p a := Nat.le_of_not_gt hnot
          have hv_eq_k : v = k := by
            exact Nat.min_eq_left hk_le_val
          exact Nat.lt_irrefl k (by simp [hv_eq_k] at hv_lt)
        exact Nat.min_eq_right (le_of_lt hval_lt_k)
      have hnot_dvd : ¬(p : ℤ) ∣ u := by
        intro hpu
        rcases hpu with ⟨b, hb⟩
        have hsucc_dvd : (p : ℤ) ^ (v + 1) ∣ a := by
          refine ⟨b, ?_⟩
          calc
            a = (p : ℤ) ^ v * u := hu
            _ = (p : ℤ) ^ v * ((p : ℤ) * b) := by rw [hb]
            _ = (p : ℤ) ^ (v + 1) * b := by
                rw [pow_succ']
                ring
        have hsucc_le : v + 1 ≤ padicValInt p a := by
          have hiff := (padicValInt_dvd_iff (p := p) (v + 1) a).mp hsucc_dvd
          exact hiff.resolve_left ha
        omega
      have hp_int : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp (Fact.out : Nat.Prime p)
      have hcop : IsCoprime (p : ℤ) u :=
        (Prime.coprime_iff_not_dvd hp_int).mpr hnot_dvd
      have hcop_pow : IsCoprime ((p : ℤ) ^ k) u := hcop.pow_left
      rw [ZMod.coe_int_isUnit_iff_isCoprime]
      simpa [primePowModulus, Int.natCast_pow] using hcop_pow
    · rw [hu, mul_comm]

/-- The truncated `p`-adic exponent used by the finite local-density Smith
normal form input.  The zero diagonal entry is assigned exponent `k`, so no
unit factor is required in that coordinate. -/
def truncatedPadicValInt (p k : ℕ) (a : ℤ) : ℕ :=
  if a = 0 then k else min k (padicValInt p a)

lemma truncatedPadicValInt_le (p k : ℕ) (a : ℤ) :
    truncatedPadicValInt p k a ≤ k := by
  by_cases ha : a = 0
  · simp [truncatedPadicValInt, ha]
  · simp [truncatedPadicValInt, ha]

lemma truncatedPadicValInt_eq_padicValInt_of_ne_zero_of_le
    {p k : ℕ} {a : ℤ} (ha : a ≠ 0) (hval : padicValInt p a ≤ k) :
    truncatedPadicValInt p k a = padicValInt p a := by
  simp [truncatedPadicValInt, ha, Nat.min_eq_right hval]

/-- Deterministic version of `exists_truncated_padic_unit_factor`, with the
truncated exponent named explicitly. -/
lemma exists_unit_factor_truncatedPadicValInt
    (p k : ℕ) [Fact (Nat.Prime p)] (a : ℤ) :
    ∃ u : ℤ,
      (∀ _hv : truncatedPadicValInt p k a < k,
        IsUnit (((u : ℤ) : ZMod (primePowModulus p k : ℕ)))) ∧
      a = u * (p ^ truncatedPadicValInt p k a : ℤ) := by
  classical
  by_cases ha : a = 0
  · refine ⟨0, ?_, ?_⟩
    · intro hv
      simp [truncatedPadicValInt, ha] at hv
    · simp [truncatedPadicValInt, ha]
  · let v : ℕ := truncatedPadicValInt p k a
    have hv_eq : v = min k (padicValInt p a) := by
      simp [v, truncatedPadicValInt, ha]
    have hv_le_val : v ≤ padicValInt p a := by
      rw [hv_eq]
      exact min_le_right _ _
    have hpow_dvd : (p : ℤ) ^ v ∣ a := by
      exact (pow_dvd_pow (p : ℤ) hv_le_val).trans (padicValInt_dvd (p := p) a)
    rcases hpow_dvd with ⟨u, hu⟩
    refine ⟨u, ?_, ?_⟩
    · intro hv_lt
      have hv_eq_val : v = padicValInt p a := by
        have hval_lt_k : padicValInt p a < k := by
          by_contra hnot
          have hk_le_val : k ≤ padicValInt p a := Nat.le_of_not_gt hnot
          have hv_eq_k : v = k := by
            rw [hv_eq]
            exact Nat.min_eq_left hk_le_val
          have hv_lt_v : v < k := by simpa [v] using hv_lt
          rw [hv_eq_k] at hv_lt_v
          exact Nat.lt_irrefl k hv_lt_v
        rw [hv_eq]
        exact Nat.min_eq_right (le_of_lt hval_lt_k)
      have hnot_dvd : ¬(p : ℤ) ∣ u := by
        intro hpu
        rcases hpu with ⟨b, hb⟩
        have hsucc_dvd : (p : ℤ) ^ (v + 1) ∣ a := by
          refine ⟨b, ?_⟩
          calc
            a = (p : ℤ) ^ v * u := hu
            _ = (p : ℤ) ^ v * ((p : ℤ) * b) := by rw [hb]
            _ = (p : ℤ) ^ (v + 1) * b := by
                rw [pow_succ']
                ring
        have hsucc_le : v + 1 ≤ padicValInt p a := by
          have hiff := (padicValInt_dvd_iff (p := p) (v + 1) a).mp hsucc_dvd
          exact hiff.resolve_left ha
        omega
      have hp_int : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp (Fact.out : Nat.Prime p)
      have hcop : IsCoprime (p : ℤ) u :=
        (Prime.coprime_iff_not_dvd hp_int).mpr hnot_dvd
      have hcop_pow : IsCoprime ((p : ℤ) ^ k) u := hcop.pow_left
      rw [ZMod.coe_int_isUnit_iff_isCoprime]
      simpa [primePowModulus, Int.natCast_pow] using hcop_pow
    · simpa [v, mul_comm] using hu

/-- Integral units have zero `p`-adic valuation. -/
lemma padicValInt_eq_zero_of_isUnit
    (p : ℕ) [Fact (Nat.Prime p)] {a : ℤ} (ha : IsUnit a) :
    padicValInt p a = 0 := by
  rcases ha with ⟨u, rfl⟩
  rcases Int.units_eq_one_or u with rfl | rfl
  · simp
  · change padicValInt p (-1) = 0
    simp [padicValInt]

lemma padicValInt_mul_isUnit_left
    (p : ℕ) [Fact (Nat.Prime p)] {u a : ℤ}
    (hu : IsUnit u) (ha : a ≠ 0) :
    padicValInt p (u * a) = padicValInt p a := by
  rw [padicValInt.mul hu.ne_zero ha, padicValInt_eq_zero_of_isUnit p hu, zero_add]

lemma padicValInt_mul_isUnit_right
    (p : ℕ) [Fact (Nat.Prime p)] {a u : ℤ}
    (ha : a ≠ 0) (hu : IsUnit u) :
    padicValInt p (a * u) = padicValInt p a := by
  rw [mul_comm, padicValInt_mul_isUnit_left p hu ha]

lemma padicValInt_prod
    (p : ℕ) [Fact (Nat.Prime p)] {ι : Type*} [Fintype ι]
    (a : ι → ℤ) (ha : ∀ i, a i ≠ 0) :
    padicValInt p (∏ i, a i) = ∑ i, padicValInt p (a i) := by
  classical
  let s : Finset ι := Finset.univ
  change padicValInt p (∏ i ∈ s, a i) = ∑ i ∈ s, padicValInt p (a i)
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro x s hxs ih
    have hx : a x ≠ 0 := ha x
    have hsprod : ∏ i ∈ s, a i ≠ 0 := by
      exact Finset.prod_ne_zero_iff.mpr (fun i _hi => ha i)
    rw [Finset.prod_insert hxs, Finset.sum_insert hxs,
      padicValInt.mul hx hsprod, ih]

lemma padicValInt_two_pow_eq_zero_of_ne_two
    (p n : ℕ) [Fact (Nat.Prime p)] (hp_two : p ≠ 2) :
    padicValInt p ((2 : ℤ) ^ n) = 0 := by
  refine padicValInt.eq_zero_of_not_dvd ?_
  intro hdiv
  have hnat : p ∣ 2 ^ n := by
    simpa using (Int.ofNat_dvd_left.mp hdiv)
  have hp_dvd_two : p ∣ 2 :=
    Nat.Prime.dvd_of_dvd_pow (Fact.out : Nat.Prime p) hnat
  have hp_eq_two : p = 2 := by
    have htwo_eq_p : 2 = p :=
      (Nat.Prime.dvd_iff_eq Nat.prime_two (Fact.out : Nat.Prime p).ne_one).mp
        hp_dvd_two
    exact htwo_eq_p.symm
  exact hp_two hp_eq_two

lemma padicInt_norm_intCast_eq_padicValInt
    (p : ℕ) [Fact (Nat.Prime p)] {z : ℤ} (hz : z ≠ 0) :
    ‖(z : ℤ_[p])‖ = (p : ℝ) ^ (-(padicValInt p z : ℝ)) := by
  rw [PadicInt.norm_eq_zpow_neg_valuation]
  · rw [show ((z : ℤ_[p]).valuation : ℤ) = (padicValInt p z : ℤ) by
      rw [← PadicInt.valuation_coe, PadicInt.coe_intCast, Padic.valuation_intCast]]
    norm_num
  · exact_mod_cast hz

lemma polarDeterminant_padic_norm_eq_padicValInt
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    ‖(L.polarDeterminant : ℤ_[p])‖ =
      (p : ℝ) ^ (-(padicValInt p L.polarDeterminant : ℝ)) := by
  exact padicInt_norm_intCast_eq_padicValInt p (by
    exact_mod_cast (ne_of_gt L.polarDeterminant_pos))

/-- At odd primes, the bilinear Gram discriminant and Schulze--Pillot's
`pairingDeterminant = det(F)` have the same `p`-adic valuation because
`polarDeterminant = 2^n * pairingDeterminant`. -/
lemma padicValInt_polarDeterminant_eq_padicValInt_pairingDeterminant_of_ne_two
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp_two : p ≠ 2) :
    padicValInt p L.polarDeterminant = padicValInt p L.pairingDeterminant := by
  rw [L.polarDeterminant_eq_two_pow_mul_pairingDeterminant]
  have htwo_ne : ((2 : ℤ) ^ n) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hform_ne : L.pairingDeterminant ≠ 0 := ne_of_gt L.pairingDeterminant_pos
  rw [padicValInt.mul htwo_ne hform_ne,
    padicValInt_two_pow_eq_zero_of_ne_two p n hp_two, zero_add]

lemma padicValInt_pairingDeterminant_le_polarDeterminant
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    padicValInt p L.pairingDeterminant ≤ padicValInt p L.polarDeterminant := by
  rw [L.polarDeterminant_eq_two_pow_mul_pairingDeterminant,
    padicValInt.mul (pow_ne_zero _ (by norm_num)) (ne_of_gt L.pairingDeterminant_pos)]
  omega

lemma primePow_mul_inv_intCast_mem_padicInt_subring_of_padicValInt_le
    (p k : ℕ) [Fact (Nat.Prime p)] (z : ℤ) (hz : z ≠ 0)
    (hval : padicValInt p z ≤ k) :
    (p : ℚ_[p]) ^ k * (z : ℚ_[p])⁻¹ ∈ PadicInt.subring p := by
  rw [PadicInt.mem_subring_iff, Padic.norm_le_one_iff_val_nonneg,
    Padic.valuation_mul
      (pow_ne_zero _ (by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero))
      (inv_ne_zero (by exact_mod_cast hz)),
    Padic.valuation_pow, Padic.valuation_p, Padic.valuation_inv,
    Padic.valuation_intCast]
  norm_num
  omega

lemma exists_padicInt_prime_mul_eq_primePow_mul_inv_intCast_of_padicValInt_lt
    (p k : ℕ) [Fact (Nat.Prime p)] (z : ℤ) (hz : z ≠ 0)
    (hval : padicValInt p z < k) :
    ∃ a : ℤ_[p],
      (p : ℚ_[p]) ^ k * (z : ℚ_[p])⁻¹ =
        (((p : ℤ_[p]) * a : ℤ_[p]) : ℚ_[p]) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  let a : ℤ_[p] :=
    ⟨(p : ℚ_[p]) ^ k * (z : ℚ_[p])⁻¹,
      primePow_mul_inv_intCast_mem_padicInt_subring_of_padicValInt_le
        p k z hz (by omega)⟩
  refine ⟨a, ?_⟩
  change (p : ℚ_[p]) ^ (k + 1) * (z : ℚ_[p])⁻¹ =
    (p : ℚ_[p]) * ((p : ℚ_[p]) ^ k * (z : ℚ_[p])⁻¹)
  rw [pow_succ]
  ring

@[simp] lemma pairingMatrix_padicField_det
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    (L.pairingMatrix_padicField p).det = (L.pairingDeterminant : ℚ_[p]) := by
  calc
    (L.pairingMatrix_padicField p).det =
        PadicInt.Coe.ringHom (L.pairingMatrix_padic p).det := by
      exact (PadicInt.Coe.ringHom.map_det _).symm
    _ = PadicInt.Coe.ringHom ((Int.castRingHom ℤ_[p]) L.pairingMatrix.det) := by
      rw [pairingMatrix_padic]
      exact congrArg PadicInt.Coe.ringHom
        ((Int.castRingHom ℤ_[p]).map_det _).symm
    _ = (L.pairingDeterminant : ℚ_[p]) := rfl

@[simp] lemma polarGramMatrix_padicField_det
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    (L.polarGramMatrix_padicField p).det =
      (2 : ℚ_[p]) ^ n * (L.pairingDeterminant : ℚ_[p]) := by
  rw [L.polarGramMatrix_padicField_eq_two_smul_pairingMatrix_padicField p,
    Matrix.det_smul]
  simp [L.pairingMatrix_padicField_det p]

/-- Polarization of the local quadratic form, expressed using its
associated-bilinear Gram matrix. -/
lemma quadForm_padicField_add_sub
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (y z : Fin n → ℚ_[p]) :
    L.quadForm_padicField p (y + z) - L.quadForm_padicField p y -
        L.quadForm_padicField p z =
      dotProduct y ((L.polarGramMatrix_padicField p).mulVec z) := by
  have hFsym : (L.pairingMatrix_padicField p)ᵀ = L.pairingMatrix_padicField p := by
    ext i j
    simp [pairingMatrix_padicField, pairingMatrix_padic, Matrix.transpose_apply,
      L.form_symm.apply]
  have hvec :
      Matrix.vecMul z (L.pairingMatrix_padicField p) =
        (L.pairingMatrix_padicField p).mulVec z := by
    calc
      Matrix.vecMul z (L.pairingMatrix_padicField p) =
          Matrix.vecMul z (L.pairingMatrix_padicField p)ᵀ := by rw [hFsym]
      _ = (L.pairingMatrix_padicField p).mulVec z :=
        Matrix.vecMul_transpose _ _
  have hcross :
      dotProduct z ((L.pairingMatrix_padicField p).mulVec y) =
        dotProduct y ((L.pairingMatrix_padicField p).mulVec z) := by
    calc
      dotProduct z ((L.pairingMatrix_padicField p).mulVec y) =
          Matrix.vecMul z (L.pairingMatrix_padicField p) ⬝ᵥ y :=
        Matrix.dotProduct_mulVec z _ y
      _ = (L.pairingMatrix_padicField p).mulVec z ⬝ᵥ y := by rw [hvec]
      _ = dotProduct y ((L.pairingMatrix_padicField p).mulVec z) :=
        dotProduct_comm _ _
  rw [L.polarGramMatrix_padicField_eq_two_smul_pairingMatrix_padicField p]
  simp only [quadForm_padicField, Matrix.mulVec_add, add_dotProduct,
    dotProduct_add, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  rw [hcross]
  ring

lemma quadForm_padicField_smul
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (c : ℚ_[p]) (y : Fin n → ℚ_[p]) :
    L.quadForm_padicField p (c • y) =
      c ^ 2 * L.quadForm_padicField p y := by
  simp only [quadForm_padicField, Matrix.mulVec_smul,
    smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

/-- Pairing by the associated-bilinear Gram matrix writes a source-dual
vector in integral coordinates. -/
noncomputable def associatedBilinearDualPadicToCoordinates
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    associatedBilinearDualPadicSubmodule L p →ₗ[ℤ_[p]] (Fin n → ℤ_[p]) where
  toFun y := fun i => ⟨(L.polarGramMatrix_padicField p).mulVec y.1 i, y.2 i⟩
  map_add' y z := by
    ext i
    change (L.polarGramMatrix_padicField p).mulVec (y.1 + z.1) i =
      (L.polarGramMatrix_padicField p).mulVec y.1 i +
        (L.polarGramMatrix_padicField p).mulVec z.1 i
    simp [Matrix.mulVec]
  map_smul' a y := by
    ext i
    change (L.polarGramMatrix_padicField p).mulVec ((a : ℚ_[p]) • y.1) i =
      (a : ℚ_[p]) * (L.polarGramMatrix_padicField p).mulVec y.1 i
    simp [Matrix.mulVec]

lemma associatedBilinearDualPadicToCoordinates_injective
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    Function.Injective (associatedBilinearDualPadicToCoordinates L p) := by
  intro y z hyz
  apply Subtype.ext
  have hG : (L.polarGramMatrix_padicField p).mulVec y.1 =
      (L.polarGramMatrix_padicField p).mulVec z.1 := by
    ext i
    have hi := congr_fun hyz i
    exact congrArg (fun a : ℤ_[p] => (a : ℚ_[p])) hi
  have hdet : (L.polarGramMatrix_padicField p).det ≠ 0 := by
    rw [L.polarGramMatrix_padicField_det p]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num))
      (by exact_mod_cast (ne_of_gt L.pairingDeterminant_pos))
  have hunit : IsUnit (L.polarGramMatrix_padicField p) := by
    rw [Matrix.isUnit_iff_isUnit_det]
    exact isUnit_iff_ne_zero.mpr hdet
  exact Matrix.mulVec_injective_of_isUnit hunit hG

lemma associatedBilinearDualPadicToCoordinates_surjective
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    Function.Surjective (associatedBilinearDualPadicToCoordinates L p) := by
  intro z
  let zQ : Fin n → ℚ_[p] := fun i => (z i : ℚ_[p])
  let y : Fin n → ℚ_[p] := (L.polarGramMatrix_padicField p)⁻¹.mulVec zQ
  have hdet : (L.polarGramMatrix_padicField p).det ≠ 0 := by
    rw [L.polarGramMatrix_padicField_det p]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num))
      (by exact_mod_cast (ne_of_gt L.pairingDeterminant_pos))
  have hunit : IsUnit (L.polarGramMatrix_padicField p).det :=
    isUnit_iff_ne_zero.mpr hdet
  have hGy : (L.polarGramMatrix_padicField p).mulVec y = zQ := by
    dsimp [y]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit, Matrix.one_mulVec]
  have hy : L.IsAssociatedBilinearDualPadicVector p y := by
    intro i
    rw [hGy]
    exact (z i).property
  refine ⟨⟨y, hy⟩, ?_⟩
  ext i
  apply PadicInt.ext
  exact congr_fun hGy i

/-- The associated-bilinear Gram matrix identifies the source dual with the
standard free `ℤ_p`-module. -/
noncomputable def associatedBilinearDualPadicEquivCoordinates
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    associatedBilinearDualPadicSubmodule L p ≃ₗ[ℤ_[p]] (Fin n → ℤ_[p]) :=
  LinearEquiv.ofBijective (associatedBilinearDualPadicToCoordinates L p)
    ⟨associatedBilinearDualPadicToCoordinates_injective L p,
      associatedBilinearDualPadicToCoordinates_surjective L p⟩

/-- Division by `p^k` maps the depth-`k` source denominator into the
associated-bilinear local dual. -/
noncomputable def associatedBilinearDualPadicDenominatorToLocalDual
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] :
    associatedBilinearDualPadicDenominator L p k →ₗ[ℤ_[p]]
      associatedBilinearDualPadicSubmodule L p where
  toFun d :=
    ⟨fun i => (d.1 i : ℚ_[p]) / (p : ℚ_[p]) ^ k,
      isAssociatedBilinearDualPadicVector_div_primePow_of_mem_associatedBilinearDualPadicDenominator
        L p k d.1 d.2⟩
  map_add' d e := by
    ext i
    change ((d.1 i + e.1 i : ℤ_[p]) : ℚ_[p]) / (p : ℚ_[p]) ^ k =
      (d.1 i : ℚ_[p]) / (p : ℚ_[p]) ^ k +
        (e.1 i : ℚ_[p]) / (p : ℚ_[p]) ^ k
    push_cast
    ring
  map_smul' a d := by
    ext i
    change (((a * d.1 i : ℤ_[p]) : ℚ_[p]) / (p : ℚ_[p]) ^ k) =
      (a : ℚ_[p]) * ((d.1 i : ℚ_[p]) / (p : ℚ_[p]) ^ k)
    push_cast
    ring

lemma associatedBilinearDualPadicDenominatorToLocalDual_injective
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] :
    Function.Injective
      (associatedBilinearDualPadicDenominatorToLocalDual L p k) := by
  intro d e hde
  apply Subtype.ext
  ext i
  apply PadicInt.ext
  have hi := congrArg
    (fun y : associatedBilinearDualPadicSubmodule L p => y.1 i) hde
  change (d.1 i : ℚ_[p]) / (p : ℚ_[p]) ^ k =
    (e.1 i : ℚ_[p]) / (p : ℚ_[p]) ^ k at hi
  have hp : (p : ℚ_[p]) ^ k ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero)
  field_simp at hi
  exact hi

lemma associatedBilinearDualPadicDenominatorToLocalDual_surjective
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : L.IsAssociatedBilinearHenselLatticeDepth p k) :
    Function.Surjective
      (associatedBilinearDualPadicDenominatorToLocalDual L p k) := by
  intro y
  let d : Fin n → ℤ_[p] := fun i => ⟨(p : ℚ_[p]) ^ k * y.1 i, hk y.1 y.2 i⟩
  let z : Fin n → ℤ_[p] := fun i =>
    ⟨(L.polarGramMatrix_padicField p).mulVec y.1 i, y.2 i⟩
  have hd : d ∈ associatedBilinearDualPadicDenominator L p k := by
    rw [mem_associatedBilinearDualPadicDenominator_iff]
    intro x
    refine ⟨dotProduct (integralVectorToPadic (n := n) p x) z, ?_⟩
    have hleft :
        ((dotProduct (integralVectorToPadic (n := n) p x)
            ((L.polarGramMatrix_padic p).mulVec d) : ℤ_[p]) : ℚ_[p]) =
          ∑ i, (x i : ℚ_[p]) *
            ∑ j, ((L.polarGramMatrix_padic p) i j : ℚ_[p]) *
              ((p : ℚ_[p]) ^ k * y.1 j) := by
      change PadicInt.Coe.ringHom
        (dotProduct (integralVectorToPadic (n := n) p x)
          ((L.polarGramMatrix_padic p).mulVec d)) = _
      rw [dotProduct, map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_mul, Matrix.mulVec, dotProduct, map_sum]
      apply congrArg
      apply Finset.sum_congr rfl
      intro j _
      rw [map_mul]
      rfl
    have hright :
        ((dotProduct (integralVectorToPadic (n := n) p x) z : ℤ_[p]) : ℚ_[p]) =
          ∑ i, (x i : ℚ_[p]) *
            ∑ j, ((L.polarGramMatrix_padic p) i j : ℚ_[p]) * y.1 j := by
      change PadicInt.Coe.ringHom
        (dotProduct (integralVectorToPadic (n := n) p x) z) = _
      rw [dotProduct, map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_mul]
      apply congrArg
      dsimp [z, polarGramMatrix_padicField]
      rw [Matrix.mulVec, dotProduct]
      rfl
    have hprod :
        ((((p : ℤ_[p]) ^ k *
            dotProduct (integralVectorToPadic (n := n) p x) z : ℤ_[p])) :
              ℚ_[p]) =
          (p : ℚ_[p]) ^ k *
            ((dotProduct (integralVectorToPadic (n := n) p x) z : ℤ_[p]) :
              ℚ_[p]) := by
      push_cast
      rfl
    apply PadicInt.ext
    rw [hleft, hprod, hright]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    calc
      (x i : ℚ_[p]) *
          ∑ j, ((L.polarGramMatrix_padic p) i j : ℚ_[p]) *
            ((p : ℚ_[p]) ^ k * y.1 j) =
          (x i : ℚ_[p]) * ((p : ℚ_[p]) ^ k *
            ∑ j, ((L.polarGramMatrix_padic p) i j : ℚ_[p]) * y.1 j) := by
              apply congrArg
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j _
              ring
      _ = (p : ℚ_[p]) ^ k * ((x i : ℚ_[p]) *
            ∑ j, ((L.polarGramMatrix_padic p) i j : ℚ_[p]) * y.1 j) := by ring
  refine ⟨⟨d, hd⟩, ?_⟩
  apply Subtype.ext
  ext i
  change ((p : ℚ_[p]) ^ k * y.1 i) / (p : ℚ_[p]) ^ k = y.1 i
  have hp : (p : ℚ_[p]) ^ k ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero)
  field_simp

/-- Exact source depth identifies the source denominator with the source dual. -/
noncomputable def associatedBilinearDualPadicDenominatorEquivLocalDual
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : L.IsAssociatedBilinearHenselLatticeDepth p k) :
    associatedBilinearDualPadicDenominator L p k ≃ₗ[ℤ_[p]]
      associatedBilinearDualPadicSubmodule L p :=
  LinearEquiv.ofBijective
    (associatedBilinearDualPadicDenominatorToLocalDual L p k)
    ⟨associatedBilinearDualPadicDenominatorToLocalDual_injective L p k,
      associatedBilinearDualPadicDenominatorToLocalDual_surjective L p k hk⟩

/-- Exact source depth gives standard coordinates on its denominator. -/
noncomputable def associatedBilinearDualPadicDenominatorEquivCoordinates
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : L.IsAssociatedBilinearHenselLatticeDepth p k) :
    associatedBilinearDualPadicDenominator L p k ≃ₗ[ℤ_[p]]
      (Fin n → ℤ_[p]) :=
  (associatedBilinearDualPadicDenominatorEquivLocalDual L p k hk).trans
    (associatedBilinearDualPadicEquivCoordinates L p)

/-- Schulze--Pillot's source quadratic-depth condition already implies its
source lattice-depth condition. The proof polarizes against source-dual
vectors corresponding to the standard coordinate functionals. -/
lemma IsAssociatedBilinearHenselQuadraticDepth.latticeDepth
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (h : L.IsAssociatedBilinearHenselQuadraticDepth p k) :
    L.IsAssociatedBilinearHenselLatticeDepth p k := by
  intro y hy i
  let ei : Fin n → ℤ_[p] := Pi.single i 1
  obtain ⟨z, hz⟩ :=
    associatedBilinearDualPadicToCoordinates_surjective L p ei
  have hzQ :
      (L.polarGramMatrix_padicField p).mulVec z.1 =
        fun j => (ei j : ℚ_[p]) := by
    ext j
    exact congrArg (fun a : ℤ_[p] => (a : ℚ_[p])) (congr_fun hz j)
  have hcoord :
      dotProduct y ((L.polarGramMatrix_padicField p).mulVec z.1) = y i := by
    rw [hzQ]
    rw [dotProduct, Finset.sum_eq_single i]
    · simp [ei]
    · intro j _ hji
      simp [ei, hji]
    · simp
  obtain ⟨ayz, hayz⟩ := h (y + z.1)
    ((associatedBilinearDualPadicSubmodule L p).add_mem hy z.2)
  obtain ⟨ay, hay⟩ := h y hy
  obtain ⟨az, haz⟩ := h z.1 z.2
  let a : ℤ_[p] := (p : ℤ_[p]) * (ayz - ay - az)
  have hvalue : (p : ℚ_[p]) ^ k * y i = (a : ℚ_[p]) := by
    calc
      (p : ℚ_[p]) ^ k * y i =
          (p : ℚ_[p]) ^ k *
            (L.quadForm_padicField p (y + z.1) -
              L.quadForm_padicField p y - L.quadForm_padicField p z.1) := by
        rw [L.quadForm_padicField_add_sub p y z.1, hcoord]
      _ = (p : ℚ_[p]) ^ k * L.quadForm_padicField p (y + z.1) -
          (p : ℚ_[p]) ^ k * L.quadForm_padicField p y -
          (p : ℚ_[p]) ^ k * L.quadForm_padicField p z.1 := by ring
      _ = (p : ℚ_[p]) * (ayz : ℚ_[p]) -
          (p : ℚ_[p]) * (ay : ℚ_[p]) - (p : ℚ_[p]) * (az : ℚ_[p]) := by
        rw [hayz, hay, haz]
        rfl
      _ = (a : ℚ_[p]) := by
        dsimp [a]
        ring
  rw [hvalue]
  exact a.property

/-- Source quadratic depth gives the stronger coordinate divisibility used
in the residue nondegeneracy argument: every scaled source-dual coordinate is
itself a multiple of `p` in `Z_p`. -/
lemma IsAssociatedBilinearHenselQuadraticDepth.coordinate_prime_mul
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (h : L.IsAssociatedBilinearHenselQuadraticDepth p k)
    (y : Fin n → ℚ_[p]) (hy : L.IsAssociatedBilinearDualPadicVector p y)
    (i : Fin n) :
    ∃ a : ℤ_[p],
      (p : ℚ_[p]) ^ k * y i = (((p : ℤ_[p]) * a : ℤ_[p]) : ℚ_[p]) := by
  let ei : Fin n → ℤ_[p] := Pi.single i 1
  obtain ⟨z, hz⟩ :=
    associatedBilinearDualPadicToCoordinates_surjective L p ei
  have hzQ :
      (L.polarGramMatrix_padicField p).mulVec z.1 =
        fun j => (ei j : ℚ_[p]) := by
    ext j
    exact congrArg (fun a : ℤ_[p] => (a : ℚ_[p])) (congr_fun hz j)
  have hcoord :
      dotProduct y ((L.polarGramMatrix_padicField p).mulVec z.1) = y i := by
    rw [hzQ]
    rw [dotProduct, Finset.sum_eq_single i]
    · simp [ei]
    · intro j _ hji
      simp [ei, hji]
    · simp
  obtain ⟨ayz, hayz⟩ := h (y + z.1)
    ((associatedBilinearDualPadicSubmodule L p).add_mem hy z.2)
  obtain ⟨ay, hay⟩ := h y hy
  obtain ⟨az, haz⟩ := h z.1 z.2
  refine ⟨ayz - ay - az, ?_⟩
  calc
    (p : ℚ_[p]) ^ k * y i =
        (p : ℚ_[p]) ^ k *
          (L.quadForm_padicField p (y + z.1) -
            L.quadForm_padicField p y - L.quadForm_padicField p z.1) := by
      rw [L.quadForm_padicField_add_sub p y z.1, hcoord]
    _ = (p : ℚ_[p]) ^ k * L.quadForm_padicField p (y + z.1) -
        (p : ℚ_[p]) ^ k * L.quadForm_padicField p y -
        (p : ℚ_[p]) ^ k * L.quadForm_padicField p z.1 := by ring
    _ = (p : ℚ_[p]) * (ayz : ℚ_[p]) -
        (p : ℚ_[p]) * (ay : ℚ_[p]) - (p : ℚ_[p]) * (az : ℚ_[p]) := by
      rw [hayz, hay, haz]
      rfl
    _ = ((((p : ℤ_[p]) * (ayz - ay - az) : ℤ_[p])) : ℚ_[p]) := by
      push_cast
      ring

/-- The source integral-integral model denominator lies in `p Z^n` whenever the
source quadratic-depth condition holds. -/
lemma
    associatedBilinearDualPadicDenominatorIntegralPreimage_le_primeCoordinateSubmodule
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : L.IsAssociatedBilinearHenselQuadraticDepth p k) :
    associatedBilinearDualPadicDenominatorIntegralPreimage L p k ≤
      primePowCoordinateSubmodule (n := n) p 1 := by
  intro d hd
  rw [mem_primePowCoordinateSubmodule_iff_coordinate_zmod_eq_zero]
  intro i
  let y : Fin n → ℚ_[p] :=
    fun j => ((integralVectorToPadic (n := n) p d j : ℤ_[p]) : ℚ_[p]) /
      (p : ℚ_[p]) ^ k
  have hy : L.IsAssociatedBilinearDualPadicVector p y :=
    isAssociatedBilinearDualPadicVector_div_primePow_of_mem_associatedBilinearDualPadicDenominator
      L p k (integralVectorToPadic (n := n) p d) hd
  obtain ⟨a, ha⟩ := hk.coordinate_prime_mul L p k y hy i
  have hcast : ((d i : ℤ) : ℤ_[p]) = (p : ℤ_[p]) * a := by
    apply PadicInt.ext
    change ((d i : ℤ_[p]) : ℚ_[p]) = (((p : ℤ_[p]) * a : ℤ_[p]) : ℚ_[p])
    rw [← ha]
    dsimp [y, integralVectorToPadic]
    have hp : (p : ℚ_[p]) ^ k ≠ 0 :=
      pow_ne_zero _ (by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero)
    field_simp
  have hdiv : ((p : ℤ_[p]) ^ 1 ∣ ((d i : ℤ) : ℤ_[p])) := by
    refine ⟨a, ?_⟩
    simpa using hcast
  exact (padicInt_primePow_dvd_intCast_iff_zmod_eq_zero p 1 (d i)).mp hdiv

/-- A source lattice depth one step deeper than a dyadic current depth
implies that current depth. This is the coordinate form of
`D_F = 2 Lambda#`. -/
lemma IsAssociatedBilinearHenselLatticeDepth.current_of_succ_dyadic
    (L : PositiveDefiniteIntegralLattice n) (k : ℕ)
    (h : L.IsAssociatedBilinearHenselLatticeDepth 2 (k + 1)) :
    L.IsHenselLatticeDepth 2 k := by
  intro y hy i
  let z : Fin n → ℚ_[2] := fun j => y j / 2
  have hz : L.IsAssociatedBilinearDualPadicVector 2 z := by
    intro j
    have hyj := hy j
    rw [L.polarGramMatrix_padicField_eq_two_smul_pairingMatrix_padicField 2,
      Matrix.smul_mulVec]
    have hvec : (2 : ℚ_[2]) • z = y := by
      ext a
      dsimp [z]
      ring
    have heq :
        (2 : ℚ_[2]) * (L.pairingMatrix_padicField 2).mulVec z j =
          (L.pairingMatrix_padicField 2).mulVec y j := by
      calc
        (2 : ℚ_[2]) * (L.pairingMatrix_padicField 2).mulVec z j =
            (L.pairingMatrix_padicField 2).mulVec ((2 : ℚ_[2]) • z) j := by
          rw [Matrix.mulVec_smul]
          rfl
        _ = (L.pairingMatrix_padicField 2).mulVec y j := by rw [hvec]
    change (2 : ℚ_[2]) * (L.pairingMatrix_padicField 2).mulVec z j ∈
      PadicInt.subring 2
    rw [heq]
    exact hyj
  have hzi := h z hz i
  have hvalue : (2 : ℚ_[2]) ^ k * y i =
      (2 : ℚ_[2]) ^ (k + 1) * z i := by
    dsimp [z]
    rw [pow_succ]
    ring
  change (2 : ℚ_[2]) ^ k * y i ∈ PadicInt.subring 2
  rw [hvalue]
  exact hzi

/-- Pairing with the standard basis writes a vector of `L_p#` in integral
coordinates. -/
noncomputable def localDualPadicToCoordinates
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    localDualPadicSubmodule L p →ₗ[ℤ_[p]] (Fin n → ℤ_[p]) where
  toFun y := fun i => ⟨(L.pairingMatrix_padicField p).mulVec y.1 i, y.2 i⟩
  map_add' y z := by
    ext i
    change (L.pairingMatrix_padicField p).mulVec (y.1 + z.1) i =
      (L.pairingMatrix_padicField p).mulVec y.1 i +
        (L.pairingMatrix_padicField p).mulVec z.1 i
    simp [Matrix.mulVec]
  map_smul' a y := by
    ext i
    change (L.pairingMatrix_padicField p).mulVec ((a : ℚ_[p]) • y.1) i =
      (a : ℚ_[p]) * (L.pairingMatrix_padicField p).mulVec y.1 i
    simp [Matrix.mulVec]

lemma localDualPadicToCoordinates_injective
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    Function.Injective (localDualPadicToCoordinates L p) := by
  intro y z hyz
  apply Subtype.ext
  have hF : (L.pairingMatrix_padicField p).mulVec y.1 =
      (L.pairingMatrix_padicField p).mulVec z.1 := by
    ext i
    have hi := congr_fun hyz i
    exact congrArg (fun a : ℤ_[p] => (a : ℚ_[p])) hi
  have hdet : (L.pairingMatrix_padicField p).det ≠ 0 := by
    rw [L.pairingMatrix_padicField_det p]
    exact_mod_cast (ne_of_gt L.pairingDeterminant_pos)
  have hunit : IsUnit (L.pairingMatrix_padicField p) := by
    rw [Matrix.isUnit_iff_isUnit_det]
    exact isUnit_iff_ne_zero.mpr hdet
  exact Matrix.mulVec_injective_of_isUnit hunit hF

lemma localDualPadicToCoordinates_surjective
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    Function.Surjective (localDualPadicToCoordinates L p) := by
  intro z
  let zQ : Fin n → ℚ_[p] := fun i => (z i : ℚ_[p])
  let y : Fin n → ℚ_[p] := (L.pairingMatrix_padicField p)⁻¹.mulVec zQ
  have hdet : (L.pairingMatrix_padicField p).det ≠ 0 := by
    rw [L.pairingMatrix_padicField_det p]
    exact_mod_cast (ne_of_gt L.pairingDeterminant_pos)
  have hunit : IsUnit (L.pairingMatrix_padicField p).det :=
    isUnit_iff_ne_zero.mpr hdet
  have hFy : (L.pairingMatrix_padicField p).mulVec y = zQ := by
    dsimp [y]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit, Matrix.one_mulVec]
  have hy : L.IsLocalDualPadicVector p y := by
    intro i
    rw [hFy]
    exact (z i).property
  refine ⟨⟨y, hy⟩, ?_⟩
  ext i
  apply PadicInt.ext
  exact congr_fun hFy i

/-- The form matrix identifies the local dual lattice with the standard free
`ℤ_p`-module. -/
noncomputable def localDualPadicEquivCoordinates
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    localDualPadicSubmodule L p ≃ₗ[ℤ_[p]] (Fin n → ℤ_[p]) :=
  LinearEquiv.ofBijective (localDualPadicToCoordinates L p)
    ⟨localDualPadicToCoordinates_injective L p,
      localDualPadicToCoordinates_surjective L p⟩

/-- Division by `p^k` maps the depth-`k` denominator module into the local
dual lattice. -/
noncomputable def localDualPadicDenominatorToLocalDual
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] :
    localDualPadicDenominator L p k →ₗ[ℤ_[p]]
      localDualPadicSubmodule L p where
  toFun d := ⟨fun i => (d.1 i : ℚ_[p]) / (p : ℚ_[p]) ^ k,
    isLocalDualPadicVector_div_primePow_of_mem_localDualPadicDenominator
      L p k d.1 d.2⟩
  map_add' d e := by
    ext i
    change ((d.1 i + e.1 i : ℤ_[p]) : ℚ_[p]) / (p : ℚ_[p]) ^ k =
      (d.1 i : ℚ_[p]) / (p : ℚ_[p]) ^ k +
        (e.1 i : ℚ_[p]) / (p : ℚ_[p]) ^ k
    push_cast
    ring
  map_smul' a d := by
    ext i
    change (((a * d.1 i : ℤ_[p]) : ℚ_[p]) / (p : ℚ_[p]) ^ k) =
      (a : ℚ_[p]) * ((d.1 i : ℚ_[p]) / (p : ℚ_[p]) ^ k)
    push_cast
    ring

@[simp] lemma localDualPadicDenominatorToLocalDual_apply
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (d : localDualPadicDenominator L p k) (i : Fin n) :
    (localDualPadicDenominatorToLocalDual L p k d).1 i =
      (d.1 i : ℚ_[p]) / (p : ℚ_[p]) ^ k := rfl

lemma localDualPadicDenominatorToLocalDual_injective
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] :
    Function.Injective (localDualPadicDenominatorToLocalDual L p k) := by
  intro d e hde
  apply Subtype.ext
  ext i
  apply PadicInt.ext
  have hi := congrArg
    (fun y : localDualPadicSubmodule L p => y.1 i) hde
  change (d.1 i : ℚ_[p]) / (p : ℚ_[p]) ^ k =
    (e.1 i : ℚ_[p]) / (p : ℚ_[p]) ^ k at hi
  have hp : (p : ℚ_[p]) ^ k ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero)
  field_simp at hi
  exact hi

lemma localDualPadicDenominatorToLocalDual_surjective
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : L.IsHenselLatticeDepth p k) :
    Function.Surjective (localDualPadicDenominatorToLocalDual L p k) := by
  intro y
  let d : Fin n → ℤ_[p] := fun i => ⟨(p : ℚ_[p]) ^ k * y.1 i, hk y.1 y.2 i⟩
  let z : Fin n → ℤ_[p] := fun i =>
    ⟨(L.pairingMatrix_padicField p).mulVec y.1 i, y.2 i⟩
  have hd : d ∈ localDualPadicDenominator L p k := by
    rw [mem_localDualPadicDenominator_iff_forall_padic]
    intro x
    refine ⟨dotProduct x z, ?_⟩
    have hleft :
        ((dotProduct x ((L.pairingMatrix_padic p).mulVec d) : ℤ_[p]) : ℚ_[p]) =
          ∑ i, (x i : ℚ_[p]) *
            ∑ j, ((L.pairingMatrix_padic p) i j : ℚ_[p]) *
              ((p : ℚ_[p]) ^ k * y.1 j) := by
      change PadicInt.Coe.ringHom
        (dotProduct x ((L.pairingMatrix_padic p).mulVec d)) = _
      rw [dotProduct, map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_mul, Matrix.mulVec, dotProduct, map_sum]
      apply congrArg
      apply Finset.sum_congr rfl
      intro j _
      rw [map_mul]
      rfl
    have hright :
        ((dotProduct x z : ℤ_[p]) : ℚ_[p]) =
          ∑ i, (x i : ℚ_[p]) *
            ∑ j, ((L.pairingMatrix_padic p) i j : ℚ_[p]) * y.1 j := by
      change PadicInt.Coe.ringHom (dotProduct x z) = _
      rw [dotProduct, map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_mul]
      apply congrArg
      dsimp [z, pairingMatrix_padicField]
      rw [Matrix.mulVec, dotProduct]
      rfl
    have hprod :
        ((((p : ℤ_[p]) ^ k * dotProduct x z : ℤ_[p])) : ℚ_[p]) =
          (p : ℚ_[p]) ^ k * ((dotProduct x z : ℤ_[p]) : ℚ_[p]) := by
      push_cast
      rfl
    apply PadicInt.ext
    rw [hleft, hprod, hright]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    calc
      (x i : ℚ_[p]) *
          ∑ j, ((L.pairingMatrix_padic p) i j : ℚ_[p]) *
            ((p : ℚ_[p]) ^ k * y.1 j) =
          (x i : ℚ_[p]) * ((p : ℚ_[p]) ^ k *
            ∑ j, ((L.pairingMatrix_padic p) i j : ℚ_[p]) * y.1 j) := by
              apply congrArg
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j _
              ring
      _ = (p : ℚ_[p]) ^ k * ((x i : ℚ_[p]) *
            ∑ j, ((L.pairingMatrix_padic p) i j : ℚ_[p]) * y.1 j) := by ring
  refine ⟨⟨d, hd⟩, ?_⟩
  apply Subtype.ext
  ext i
  change ((p : ℚ_[p]) ^ k * y.1 i) / (p : ℚ_[p]) ^ k = y.1 i
  have hp : (p : ℚ_[p]) ^ k ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero)
  field_simp

/-- At an exact Hensel lattice depth, scaling by `p^k` identifies `L_p#`
with the depth-`k` denominator module. -/
noncomputable def localDualPadicDenominatorEquivLocalDual
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : L.IsHenselLatticeDepth p k) :
    localDualPadicDenominator L p k ≃ₗ[ℤ_[p]]
      localDualPadicSubmodule L p :=
  LinearEquiv.ofBijective
    (localDualPadicDenominatorToLocalDual L p k)
    ⟨localDualPadicDenominatorToLocalDual_injective L p k,
      localDualPadicDenominatorToLocalDual_surjective L p k hk⟩

/-- Exact depth and the form matrix give canonical standard coordinates on
the depth-`k` denominator module. -/
noncomputable def localDualPadicDenominatorEquivCoordinates
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : L.IsHenselLatticeDepth p k) :
    localDualPadicDenominator L p k ≃ₗ[ℤ_[p]] (Fin n → ℤ_[p]) :=
  (localDualPadicDenominatorEquivLocalDual L p k hk).trans
    (localDualPadicEquivCoordinates L p)

/-- Reduce the standard coordinates on `D_k / p D_k` modulo `p`. -/
noncomputable def localDualPadicDenominatorPrimeSubquotientToResidue
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : L.IsHenselLatticeDepth p k) :
    (localDualPadicDenominator L p k ⧸
        localDualPadicDenominatorPrimeSubmodule L p k) →ₗ[ℤ]
      (Fin n → ZMod p) := by
  letI : Module ℤ_[p] (Fin n → ZMod p) :=
    Module.compHom (Fin n → ZMod p) PadicInt.toZMod
  let e := localDualPadicDenominatorEquivCoordinates L p k hk
  let residue : (Fin n → ℤ_[p]) →ₗ[ℤ_[p]] (Fin n → ZMod p) :=
    { toFun := fun x i => PadicInt.toZMod (x i)
      map_add' := by
        intro x y
        ext i
        simp
      map_smul' := by
        intro a x
        ext i
        change PadicInt.toZMod (a * x i) =
          PadicInt.toZMod a * PadicInt.toZMod (x i)
        exact map_mul PadicInt.toZMod a (x i) }
  let f : localDualPadicDenominator L p k →ₗ[ℤ_[p]] (Fin n → ZMod p) :=
    residue.comp (e : localDualPadicDenominator L p k →ₗ[ℤ_[p]]
      (Fin n → ℤ_[p]))
  let P := localDualPadicDenominatorPrimeSubmodule L p k
  have hP : P ≤ LinearMap.ker f := by
    intro x hx
    rcases hx with ⟨y, hy, hxy⟩
    rw [LinearMap.mem_ker]
    ext i
    change PadicInt.toZMod (e x i) = 0
    have hxe : e x = (p : ℤ_[p]) • e ⟨y, hy⟩ := by
      rw [← e.map_smul]
      congr 1
      apply Subtype.ext
      change x.1 = (p : ℤ_[p]) • y
      simpa using hxy.symm
    rw [hxe]
    simp
  exact (P.liftQ f hP).restrictScalars ℤ

@[simp] lemma localDualPadicDenominatorPrimeSubquotientToResidue_mkQ
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : L.IsHenselLatticeDepth p k)
    (x : localDualPadicDenominator L p k) :
    localDualPadicDenominatorPrimeSubquotientToResidue L p k hk
        ((localDualPadicDenominatorPrimeSubmodule L p k).mkQ x) =
      fun i => PadicInt.toZMod
        (localDualPadicDenominatorEquivCoordinates L p k hk x i) := by
  rfl

lemma localDualPadicDenominatorPrimeSubquotientToResidue_injective
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : L.IsHenselLatticeDepth p k) :
    Function.Injective
      (localDualPadicDenominatorPrimeSubquotientToResidue L p k hk) := by
  let e := localDualPadicDenominatorEquivCoordinates L p k hk
  let P := localDualPadicDenominatorPrimeSubmodule L p k
  have hzero_imp : ∀ q,
      localDualPadicDenominatorPrimeSubquotientToResidue L p k hk q = 0 →
        q = 0 := by
    intro q hzero
    induction q using Quotient.inductionOn with
    | h x =>
      change P.mkQ x = 0
      apply (Submodule.Quotient.mk_eq_zero P).mpr
      have hxmod : ∀ i, PadicInt.toZMod (e x i) = 0 := by
        intro i
        have hi := congr_fun hzero i
        simpa [e, P] using hi
      have hxdiv : ∀ i, (p : ℤ_[p]) ∣ e x i := by
        intro i
        have hi : e x i ∈ RingHom.ker (PadicInt.toZMod (p := p)) :=
          RingHom.mem_ker.mpr (hxmod i)
        rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
          Ideal.mem_span_singleton] at hi
        exact hi
      choose y hy using hxdiv
      let yd : localDualPadicDenominator L p k := e.symm y
      have hyd : (p : ℤ_[p]) • yd = x := by
        apply e.injective
        rw [e.map_smul, e.apply_symm_apply]
        ext i
        simpa [smul_eq_mul] using (hy i).symm
      refine ⟨yd.1, yd.2, ?_⟩
      change (p : ℤ_[p]) • yd.1 = x.1
      exact congrArg Subtype.val hyd
  intro q r hqr
  rw [← sub_eq_zero]
  apply hzero_imp
  calc
    localDualPadicDenominatorPrimeSubquotientToResidue L p k hk (q - r) =
        localDualPadicDenominatorPrimeSubquotientToResidue L p k hk q -
          localDualPadicDenominatorPrimeSubquotientToResidue L p k hk r :=
      map_sub _ _ _
    _ = 0 := sub_eq_zero.mpr hqr

lemma localDualPadicDenominatorPrimeSubquotientToResidue_surjective
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : L.IsHenselLatticeDepth p k) :
    Function.Surjective
      (localDualPadicDenominatorPrimeSubquotientToResidue L p k hk) := by
  intro z
  choose x hx using fun i => ZMod.ringHom_surjective PadicInt.toZMod (z i)
  let e := localDualPadicDenominatorEquivCoordinates L p k hk
  let xd : localDualPadicDenominator L p k := e.symm x
  refine ⟨(localDualPadicDenominatorPrimeSubmodule L p k).mkQ xd, ?_⟩
  ext i
  change PadicInt.toZMod (e xd i) = z i
  rw [show e xd = x by simp [xd]]
  exact hx i

/-- The exact-depth denominator residue quotient has the standard coordinate
model `(ZMod p)^n`. -/
noncomputable def localDualPadicDenominatorPrimeSubquotientEquivResidue
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : L.IsHenselLatticeDepth p k) :
    (localDualPadicDenominator L p k ⧸
        localDualPadicDenominatorPrimeSubmodule L p k) ≃ₗ[ℤ]
      (Fin n → ZMod p) :=
  LinearEquiv.ofBijective
    (localDualPadicDenominatorPrimeSubquotientToResidue L p k hk)
    ⟨localDualPadicDenominatorPrimeSubquotientToResidue_injective L p k hk,
      localDualPadicDenominatorPrimeSubquotientToResidue_surjective L p k hk⟩

/-- Reduce standard source-denominator coordinates modulo `p`. -/
noncomputable def
    associatedBilinearDualPadicDenominatorPrimeSubquotientToResidue
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : L.IsAssociatedBilinearHenselLatticeDepth p k) :
    (associatedBilinearDualPadicDenominator L p k ⧸
        associatedBilinearDualPadicDenominatorPrimeSubmodule L p k) →ₗ[ℤ]
      (Fin n → ZMod p) := by
  letI : Module ℤ_[p] (Fin n → ZMod p) :=
    Module.compHom (Fin n → ZMod p) PadicInt.toZMod
  let e := associatedBilinearDualPadicDenominatorEquivCoordinates L p k hk
  let residue : (Fin n → ℤ_[p]) →ₗ[ℤ_[p]] (Fin n → ZMod p) :=
    { toFun := fun x i => PadicInt.toZMod (x i)
      map_add' := by
        intro x y
        ext i
        simp
      map_smul' := by
        intro a x
        ext i
        change PadicInt.toZMod (a * x i) =
          PadicInt.toZMod a * PadicInt.toZMod (x i)
        exact map_mul PadicInt.toZMod a (x i) }
  let f : associatedBilinearDualPadicDenominator L p k →ₗ[ℤ_[p]]
      (Fin n → ZMod p) :=
    residue.comp (e : associatedBilinearDualPadicDenominator L p k →ₗ[ℤ_[p]]
      (Fin n → ℤ_[p]))
  let P := associatedBilinearDualPadicDenominatorPrimeSubmodule L p k
  have hP : P ≤ LinearMap.ker f := by
    intro x hx
    rcases hx with ⟨y, hy, hxy⟩
    rw [LinearMap.mem_ker]
    ext i
    change PadicInt.toZMod (e x i) = 0
    have hxe : e x = (p : ℤ_[p]) • e ⟨y, hy⟩ := by
      rw [← e.map_smul]
      congr 1
      apply Subtype.ext
      change x.1 = (p : ℤ_[p]) • y
      simpa using hxy.symm
    rw [hxe]
    simp
  exact (P.liftQ f hP).restrictScalars ℤ

@[simp] lemma
    associatedBilinearDualPadicDenominatorPrimeSubquotientToResidue_mkQ
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : L.IsAssociatedBilinearHenselLatticeDepth p k)
    (x : associatedBilinearDualPadicDenominator L p k) :
    associatedBilinearDualPadicDenominatorPrimeSubquotientToResidue
        L p k hk
        ((associatedBilinearDualPadicDenominatorPrimeSubmodule L p k).mkQ x) =
      fun i => PadicInt.toZMod
        (associatedBilinearDualPadicDenominatorEquivCoordinates
          L p k hk x i) := by
  rfl

/-- Reduce the actual adjacent source subquotient `S_k / S_(k+1)` directly
to standard residue coordinates. This avoids a dependent transport through
the propositionally equal presentation `S_k / p S_k`. -/
noncomputable def
    associatedBilinearDualPadicDenominatorAdjacentSubquotientToResidue
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : L.IsAssociatedBilinearHenselLatticeDepth p k) :
    (associatedBilinearDualPadicDenominator L p k ⧸
        (associatedBilinearDualPadicDenominator L p (k + 1)).comap
          (associatedBilinearDualPadicDenominator L p k).subtype) →ₗ[ℤ]
      (Fin n → ZMod p) := by
  letI : Module ℤ_[p] (Fin n → ZMod p) :=
    Module.compHom (Fin n → ZMod p) PadicInt.toZMod
  let D := associatedBilinearDualPadicDenominator L p k
  let Dsucc := associatedBilinearDualPadicDenominator L p (k + 1)
  let e := associatedBilinearDualPadicDenominatorEquivCoordinates L p k hk
  let residue : (Fin n → ℤ_[p]) →ₗ[ℤ_[p]] (Fin n → ZMod p) :=
    { toFun := fun x i => PadicInt.toZMod (x i)
      map_add' := by
        intro x y
        ext i
        simp
      map_smul' := by
        intro a x
        ext i
        change PadicInt.toZMod (a * x i) =
          PadicInt.toZMod a * PadicInt.toZMod (x i)
        exact map_mul PadicInt.toZMod a (x i) }
  let f : D →ₗ[ℤ_[p]] (Fin n → ZMod p) :=
    residue.comp (e : D →ₗ[ℤ_[p]] (Fin n → ℤ_[p]))
  have hDsucc : Dsucc.comap D.subtype ≤ LinearMap.ker f := by
    intro x hx
    have hxmap : x.1 ∈ Submodule.map
        ((LinearMap.lsmul ℤ_[p] (Fin n → ℤ_[p])) (p : ℤ_[p])) D := by
      rw [←
        associatedBilinearDualPadicDenominator_succ_eq_map_prime_smul
          L p k hk]
      exact hx
    rcases hxmap with ⟨y, hy, hxy⟩
    rw [LinearMap.mem_ker]
    ext i
    change PadicInt.toZMod (e x i) = 0
    have hxe : e x = (p : ℤ_[p]) • e ⟨y, hy⟩ := by
      rw [← e.map_smul]
      apply congrArg e
      apply Subtype.ext
      exact hxy.symm
    rw [hxe]
    simp
  exact ((Dsucc.comap D.subtype).liftQ f hDsucc).restrictScalars ℤ

@[simp] lemma
    associatedBilinearDualPadicDenominatorAdjacentSubquotientToResidue_mkQ
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : L.IsAssociatedBilinearHenselLatticeDepth p k)
    (x : associatedBilinearDualPadicDenominator L p k) :
    associatedBilinearDualPadicDenominatorAdjacentSubquotientToResidue
        L p k hk
        (((associatedBilinearDualPadicDenominator L p (k + 1)).comap
          (associatedBilinearDualPadicDenominator L p k).subtype).mkQ x) =
      fun i => PadicInt.toZMod
        (associatedBilinearDualPadicDenominatorEquivCoordinates
          L p k hk x i) := by
  rfl

lemma
    associatedBilinearDualPadicDenominatorAdjacentSubquotientToResidue_injective
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : L.IsAssociatedBilinearHenselLatticeDepth p k) :
    Function.Injective
      (associatedBilinearDualPadicDenominatorAdjacentSubquotientToResidue
        L p k hk) := by
  let D := associatedBilinearDualPadicDenominator L p k
  let Dsucc := associatedBilinearDualPadicDenominator L p (k + 1)
  let e := associatedBilinearDualPadicDenominatorEquivCoordinates L p k hk
  have hzero_imp : ∀ q,
      associatedBilinearDualPadicDenominatorAdjacentSubquotientToResidue
          L p k hk q = 0 → q = 0 := by
    intro q hzero
    induction q using Quotient.inductionOn with
    | h x =>
      change (Dsucc.comap D.subtype).mkQ x = 0
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      have hxmod : ∀ i, PadicInt.toZMod (e x i) = 0 := by
        intro i
        have hi := congr_fun hzero i
        simpa [D, Dsucc, e] using hi
      have hxdiv : ∀ i, (p : ℤ_[p]) ∣ e x i := by
        intro i
        have hi : e x i ∈ RingHom.ker (PadicInt.toZMod (p := p)) :=
          RingHom.mem_ker.mpr (hxmod i)
        rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
          Ideal.mem_span_singleton] at hi
        exact hi
      choose y hy using hxdiv
      let yd : D := e.symm y
      have hyd : (p : ℤ_[p]) • yd = x := by
        apply e.injective
        rw [e.map_smul, e.apply_symm_apply]
        ext i
        simpa [smul_eq_mul] using (hy i).symm
      have hxsucc : x.1 ∈ Dsucc := by
        change x.1 ∈
          associatedBilinearDualPadicDenominator L p (k + 1)
        rw [associatedBilinearDualPadicDenominator_succ_eq_map_prime_smul
          L p k hk]
        exact ⟨yd.1, yd.2, congrArg Subtype.val hyd⟩
      exact hxsucc
  intro q r hqr
  rw [← sub_eq_zero]
  apply hzero_imp
  calc
    associatedBilinearDualPadicDenominatorAdjacentSubquotientToResidue
        L p k hk (q - r) =
      associatedBilinearDualPadicDenominatorAdjacentSubquotientToResidue
          L p k hk q -
        associatedBilinearDualPadicDenominatorAdjacentSubquotientToResidue
          L p k hk r := map_sub _ _ _
    _ = 0 := sub_eq_zero.mpr hqr

lemma
    associatedBilinearDualPadicDenominatorAdjacentSubquotientToResidue_surjective
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : L.IsAssociatedBilinearHenselLatticeDepth p k) :
    Function.Surjective
      (associatedBilinearDualPadicDenominatorAdjacentSubquotientToResidue
        L p k hk) := by
  intro z
  choose x hx using fun i => ZMod.ringHom_surjective PadicInt.toZMod (z i)
  let e := associatedBilinearDualPadicDenominatorEquivCoordinates L p k hk
  let xd : associatedBilinearDualPadicDenominator L p k := e.symm x
  refine ⟨((associatedBilinearDualPadicDenominator L p (k + 1)).comap
    (associatedBilinearDualPadicDenominator L p k).subtype).mkQ xd, ?_⟩
  ext i
  change PadicInt.toZMod (e xd i) = z i
  rw [show e xd = x by simp [xd]]
  exact hx i

/-- The actual adjacent source subquotient has the standard residue model,
with a computation rule on its depth-`k` representatives. -/
noncomputable def
    associatedBilinearDualPadicDenominatorAdjacentSubquotientEquivResidue
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : L.IsAssociatedBilinearHenselLatticeDepth p k) :
    (associatedBilinearDualPadicDenominator L p k ⧸
        (associatedBilinearDualPadicDenominator L p (k + 1)).comap
          (associatedBilinearDualPadicDenominator L p k).subtype) ≃ₗ[ℤ]
      (Fin n → ZMod p) :=
  LinearEquiv.ofBijective
    (associatedBilinearDualPadicDenominatorAdjacentSubquotientToResidue
      L p k hk)
    ⟨associatedBilinearDualPadicDenominatorAdjacentSubquotientToResidue_injective
        L p k hk,
      associatedBilinearDualPadicDenominatorAdjacentSubquotientToResidue_surjective
        L p k hk⟩

/-- The actual one-column adjacent correction kernel has residue coordinates
in `(ZMod p)^n`. -/
noncomputable def
    localDualPadicDenominatorIntegralPreimageSuccKernelEquivResidue
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : L.IsHenselLatticeDepth p k) :
    LinearMap.ker (localDualQuotientMapOfLE (n := n)
        (localDualPadicDenominatorIntegralPreimage_succ_le L p k)) ≃ₗ[ℤ]
      (Fin n → ZMod p) :=
  (localDualPadicDenominatorIntegralPreimageSuccKernelEquivPrimeSubquotient
    L p k hk).trans
      (localDualPadicDenominatorPrimeSubquotientEquivResidue L p k hk)

/-- The actual one-column source correction kernel has residue coordinates. -/
noncomputable def
    associatedBilinearDualPadicDenominatorIntegralPreimageSuccKernelEquivResidue
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : L.IsAssociatedBilinearHenselLatticeDepth p k) :
    LinearMap.ker (localDualQuotientMapOfLE (n := n)
        (associatedBilinearDualPadicDenominatorIntegralPreimage_succ_le
          L p k)) ≃ₗ[ℤ]
      (Fin n → ZMod p) :=
  (associatedBilinearDualPadicDenominatorIntegralPreimageSuccKernelEquivPadicSubquotient
    L p k).trans
      (associatedBilinearDualPadicDenominatorAdjacentSubquotientEquivResidue
        L p k hk)

lemma natCard_localDualPadicDenominatorIntegralPreimage_succKernel
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : L.IsHenselLatticeDepth p k) :
    Nat.card (LinearMap.ker (localDualQuotientMapOfLE (n := n)
      (localDualPadicDenominatorIntegralPreimage_succ_le L p k))) = p ^ n := by
  rw [Nat.card_congr
    (localDualPadicDenominatorIntegralPreimageSuccKernelEquivResidue
      L p k hk).toEquiv]
  simp

/-- If `k` is strictly deeper than the determinant valuation, then every
vector in the local dual becomes `p` times an integral vector after scaling
by `p^k`.  This is the coordinate adjugate argument behind both exact local
depth conditions used by the quantitative Hensel source. -/
lemma exists_padicIntVector_prime_mul_eq_primePow_mul_of_isLocalDual
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hval : padicValInt p L.pairingDeterminant < k)
    (y : Fin n → ℚ_[p]) (hy : L.IsLocalDualPadicVector p y) :
    ∃ u : Fin n → ℤ_[p], ∀ i : Fin n,
      (p : ℚ_[p]) ^ k * y i =
        (((p : ℤ_[p]) * u i : ℤ_[p]) : ℚ_[p]) := by
  let z : Fin n → ℤ_[p] := fun i => ⟨_, hy i⟩
  let w : Fin n → ℤ_[p] := (L.pairingMatrix_padic p).adjugate.mulVec z
  have hz : padicIntVectorToPadic p z =
      (L.pairingMatrix_padicField p).mulVec y := rfl
  have hw : padicIntVectorToPadic p w =
      (L.pairingMatrix_padicField p).adjugate.mulVec
        ((L.pairingMatrix_padicField p).mulVec y) := by
    ext i
    change PadicInt.Coe.ringHom
        (((L.pairingMatrix_padic p).adjugate.mulVec z) i) = _
    rw [RingHom.map_mulVec]
    change (((L.pairingMatrix_padic p).adjugate.map PadicInt.Coe.ringHom).mulVec
      (padicIntVectorToPadic p z)) i = _
    have hadj : (L.pairingMatrix_padic p).adjugate.map PadicInt.Coe.ringHom =
        (L.pairingMatrix_padicField p).adjugate := by
      exact PadicInt.Coe.ringHom.map_adjugate _
    rw [hadj, hz]
  have hw_det : ∀ i : Fin n,
      (w i : ℚ_[p]) = (L.pairingDeterminant : ℚ_[p]) * y i := by
    intro i
    have hvec :
        (L.pairingMatrix_padicField p).adjugate.mulVec
            ((L.pairingMatrix_padicField p).mulVec y) =
          fun j => (L.pairingDeterminant : ℚ_[p]) * y j := by
      rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul,
        L.pairingMatrix_padicField_det p, Matrix.smul_mulVec, Matrix.one_mulVec]
      rfl
    exact congr_fun (hw.trans hvec) i
  obtain ⟨a, ha⟩ :=
    exists_padicInt_prime_mul_eq_primePow_mul_inv_intCast_of_padicValInt_lt
      p k L.pairingDeterminant (ne_of_gt L.pairingDeterminant_pos) hval
  refine ⟨fun i => a * w i, ?_⟩
  intro i
  change (p : ℚ_[p]) ^ k * y i =
    (p : ℚ_[p]) * ((a : ℚ_[p]) * (w i : ℚ_[p]))
  have ha' : (p : ℚ_[p]) ^ k * (L.pairingDeterminant : ℚ_[p])⁻¹ =
      (p : ℚ_[p]) * (a : ℚ_[p]) := by simpa using ha
  rw [← mul_assoc, ← ha', hw_det]
  field_simp [ne_of_gt L.pairingDeterminant_pos]

lemma isHenselLatticeDepth_of_pairingDeterminant_val_lt
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hval : padicValInt p L.pairingDeterminant < k) :
    L.IsHenselLatticeDepth p k := by
  intro y hy i
  obtain ⟨u, hu⟩ :=
    L.exists_padicIntVector_prime_mul_eq_primePow_mul_of_isLocalDual
      p k hval y hy
  rw [hu i]
  exact (p * u i).property

lemma isHenselQuadraticDepth_of_pairingDeterminant_val_lt
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hval : padicValInt p L.pairingDeterminant < k) :
    L.IsHenselQuadraticDepth p k := by
  intro y hy
  obtain ⟨u, hu⟩ :=
    L.exists_padicIntVector_prime_mul_eq_primePow_mul_of_isLocalDual
      p k hval y hy
  let z : Fin n → ℤ_[p] := fun i => ⟨_, hy i⟩
  refine ⟨∑ i, u i * z i, ?_⟩
  change (p : ℚ_[p]) ^ k *
      (∑ i, y i * (L.pairingMatrix_padicField p).mulVec y i) = _
  rw [Finset.mul_sum]
  calc
    ∑ i, (p : ℚ_[p]) ^ k *
          (y i * (L.pairingMatrix_padicField p).mulVec y i) =
        ∑ i, ((p : ℚ_[p]) ^ k * y i) *
          (L.pairingMatrix_padicField p).mulVec y i := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = ∑ i, ((((p : ℤ_[p]) * u i : ℤ_[p]) : ℚ_[p])) *
          (z i : ℚ_[p]) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hu i]
    _ = ((((p : ℤ_[p]) * ∑ i, u i * z i : ℤ_[p]) : ℚ_[p])) := by
      push_cast
      simp [Finset.mul_sum, mul_assoc]

/-- Unimodular row and column operations do not change the `p`-adic
valuation of the determinant, so a diagonalization computes it as the sum of
the diagonal valuations. -/
lemma padicValInt_det_eq_sum_diagonal_of_left_right_mul_eq_diagonal
    (A P Q : Matrix (Fin n) (Fin n) ℤ)
    (p : ℕ) [Fact (Nat.Prime p)] (d : Fin n → ℤ)
    (hP : IsUnit P) (hQ : IsUnit Q)
    (hdiag : P * A * Q = Matrix.diagonal d)
    (hd : ∀ i : Fin n, d i ≠ 0) :
    padicValInt p A.det = ∑ i : Fin n, padicValInt p (d i) := by
  have hPdet : IsUnit P.det := by
    rwa [Matrix.isUnit_iff_isUnit_det] at hP
  have hQdet : IsUnit Q.det := by
    rwa [Matrix.isUnit_iff_isUnit_det] at hQ
  have hdetdiag : P.det * A.det * Q.det = ∏ i, d i := by
    simpa [Matrix.det_mul, Matrix.det_diagonal, mul_assoc] using congrArg Matrix.det hdiag
  have hdiag_ne : (∏ i, d i) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr (fun i _hi => hd i)
  have hA_ne : A.det ≠ 0 := by
    intro hA
    apply hdiag_ne
    rw [← hdetdiag, hA]
    simp
  calc
    padicValInt p A.det
        = padicValInt p (P.det * A.det) := by
            symm
            exact padicValInt_mul_isUnit_left p hPdet hA_ne
    _ = padicValInt p (P.det * A.det * Q.det) := by
            symm
            exact padicValInt_mul_isUnit_right p
              (mul_ne_zero hPdet.ne_zero hA_ne) hQdet
    _ = padicValInt p (∏ i, d i) := by rw [hdetdiag]
    _ = ∑ i : Fin n, padicValInt p (d i) := by
            exact padicValInt_prod p d hd

lemma sum_truncatedPadicValInt_eq_padicValInt_det_of_left_right_mul_eq_diagonal
    (A P Q : Matrix (Fin n) (Fin n) ℤ)
    (p k : ℕ) [Fact (Nat.Prime p)] (d : Fin n → ℤ)
    (hP : IsUnit P) (hQ : IsUnit Q)
    (hdiag : P * A * Q = Matrix.diagonal d)
    (hdval : ∀ i : Fin n, padicValInt p (d i) ≤ k)
    (hd : ∀ i : Fin n, d i ≠ 0) :
    ∑ i : Fin n, truncatedPadicValInt p k (d i) =
      padicValInt p A.det := by
  calc
    ∑ i : Fin n, truncatedPadicValInt p k (d i)
        = ∑ i : Fin n, padicValInt p (d i) := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            exact truncatedPadicValInt_eq_padicValInt_of_ne_zero_of_le
              (hd i) (hdval i)
    _ = padicValInt p A.det := by
            exact (padicValInt_det_eq_sum_diagonal_of_left_right_mul_eq_diagonal
              (n := n) A P Q p d hP hQ hdiag hd).symm

/-- A nonsingular square integer matrix admits the row/column diagonalization
shape needed by the local-density Smith input.

Mathlib's Smith normal form is stated for a full-rank submodule.  Applying it
to the image of `A : ℤ^n → ℤ^n`, and pulling the image basis back through the
injective map `A`, gives domain and codomain bases in which `A` is diagonal.
Changing both bases back to the standard coordinate basis gives integral
unimodular row and column matrices. -/
lemma exists_integral_diagonalization_of_det_ne_zero
    (A : Matrix (Fin n) (Fin n) ℤ) (hdet : A.det ≠ 0) :
    ∃ (P Q : Matrix (Fin n) (Fin n) ℤ) (d : Fin n → ℤ),
      IsUnit P ∧ IsUnit Q ∧ P * A * Q = Matrix.diagonal d := by
  classical
  let bStd : Module.Basis (Fin n) ℤ (Fin n → ℤ) := Pi.basisFun ℤ (Fin n)
  let f : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℤ) := Matrix.toLin' A
  let R : Submodule ℤ (Fin n → ℤ) := LinearMap.range f
  have hmul_inj : Function.Injective A.mulVec := by
    rw [Matrix.mulVec_injective_iff]
    exact Matrix.linearIndependent_cols_of_det_ne_zero hdet
  have hf_inj : Function.Injective f := by
    intro x y hxy
    exact hmul_inj (by simpa [f, Matrix.toLin'_apply] using hxy)
  have hR_rank : Module.finrank ℤ R = Module.finrank ℤ (Fin n → ℤ) :=
    LinearMap.finrank_range_of_inj hf_inj
  obtain ⟨bM, d, bR, hsnf⟩ :=
    Submodule.exists_smith_normal_form_of_rank_eq
      (N := R) bStd hR_rank
  let fR : (Fin n → ℤ) →ₗ[ℤ] R :=
    LinearMap.codRestrict R f (fun x => ⟨x, rfl⟩)
  have hfR_inj : Function.Injective fR := by
    intro x y hxy
    exact hf_inj (by simpa [fR] using congrArg Subtype.val hxy)
  have hfR_surj : Function.Surjective fR := by
    intro y
    rcases y.property with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    ext i
    simpa [fR] using congr_fun hx i
  let eR : (Fin n → ℤ) ≃ₗ[ℤ] R :=
    LinearEquiv.ofBijective fR ⟨hfR_inj, hfR_surj⟩
  let bD : Module.Basis (Fin n) ℤ (Fin n → ℤ) := bR.map eR.symm
  have hf_bD : ∀ j : Fin n, f (bD j) = d j • bM j := by
    intro j
    have hcast : fR (bD j) = bR j := by
      change eR (eR.symm (bR j)) = bR j
      exact eR.apply_symm_apply (bR j)
    have hval := congrArg Subtype.val hcast
    simpa [fR, bD, hsnf j] using hval
  have hmatrix :
      LinearMap.toMatrix bD bM f = Matrix.diagonal d := by
    ext i j
    rw [LinearMap.toMatrix_apply, hf_bD j]
    rw [map_smul, Module.Basis.repr_self, Finsupp.smul_single]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij]
  let P : Matrix (Fin n) (Fin n) ℤ := bM.toMatrix bStd
  let Q : Matrix (Fin n) (Fin n) ℤ := bStd.toMatrix bD
  haveI : Invertible P := by
    dsimp [P]
    exact Module.Basis.invertibleToMatrix bM bStd
  haveI : Invertible Q := by
    dsimp [Q]
    exact Module.Basis.invertibleToMatrix bStd bD
  refine ⟨P, Q, d, isUnit_of_invertible P, isUnit_of_invertible Q, ?_⟩
  have hchange0 :
      bM.toMatrix bStd * LinearMap.toMatrix bStd bStd f * bStd.toMatrix bD =
        LinearMap.toMatrix bD bM f :=
    basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
      (b' := bStd) (c' := bStd) (b := bD) (c := bM) (f := f)
  have hA : LinearMap.toMatrix bStd bStd f = A := by
    simp [f, bStd]
  have hchange :
      bM.toMatrix bStd * A * bStd.toMatrix bD =
        LinearMap.toMatrix bD bM f := by
    rw [← hA]
    exact hchange0
  change bM.toMatrix bStd * A * bStd.toMatrix bD = Matrix.diagonal d
  rw [hchange, hmatrix]

/-- If integral unimodular row and column operations put `L.pairingMatrix` into
truncated unit-times-`p`-power diagonal form, then the one-column denominator
subquotient has the expected `p`-primary cardinal.  This is the finite-count
input extracted from the Smith normal form. -/
lemma pairingMatrixLocalDualCoordinateSubmodule_subquotient_card_of_left_right_mul_eq_diagonal_units_prime_pows_of_lt
    (L : PositiveDefiniteIntegralLattice n) (P Q : Matrix (Fin n) (Fin n) ℤ)
    (p k : ℕ) [Fact (Nat.Prime p)]
    (u : Fin n → ℤ) (v : Fin n → ℕ) (hv : ∀ i, v i ≤ k)
    (hunit : ∀ i : Fin n, v i < k →
      IsUnit (((u i : ℤ) : ZMod (primePowModulus p k : ℕ))))
    (hP : IsUnit P) (hQ : IsUnit Q)
    (hdiag : P * L.pairingMatrix * Q =
      Matrix.diagonal (fun i : Fin n => u i * (p ^ v i : ℤ))) :
    Nat.card
        (pairingMatrixLocalDualCoordinateSubmodule L p k ⧸
          (primePowCoordinateSubmodule (n := n) p k).comap
            (pairingMatrixLocalDualCoordinateSubmodule L p k).subtype) =
      p ^ (∑ i : Fin n, v i) := by
  let w : ℕ := ∑ i : Fin n, (k - v i)
  have hsum : w + (∑ i : Fin n, v i) = n * k := by
    calc
      w + (∑ i : Fin n, v i)
          = ∑ i : Fin n, ((k - v i) + v i) := by
              simpa [w] using
                (Finset.sum_add_distrib (s := Finset.univ)
                  (f := fun i : Fin n => k - v i) (g := fun i : Fin n => v i)).symm
      _ = ∑ _i : Fin n, k := by
              refine Finset.sum_congr rfl ?_
              intro i _hi
              exact Nat.sub_add_cancel (hv i)
      _ = n * k := by
              simp [Fintype.card_fin]
  have hw : w ≤ n * k := by omega
  have hcard :
      Nat.card ((Fin n → ℤ) ⧸ pairingMatrixLocalDualCoordinateSubmodule L p k) =
        p ^ w := by
    simpa [pairingMatrixLocalDualCoordinateSubmodule, w] using
      matrixModLinearMap_ker_quotient_card_of_left_right_mul_eq_diagonal_units_prime_pows_of_lt
        (n := n) L.pairingMatrix P Q p k u v hv hunit hP hQ hdiag
  have hsub :=
    pairingMatrixLocalDualCoordinateSubmodule_subquotient_card_eq_prime_pow_of_quotient_card
      (n := n) L p k w hw hcard
  have hdiff : n * k - w = ∑ i : Fin n, v i := by omega
  simpa [hdiff] using hsub

/-- Push basis images forward through the quotient map induced by a larger
coordinate denominator. -/
def localDualQuotientFamilyOfLE
    {D E : Submodule ℤ (Fin n → ℤ)} (hDE : D ≤ E)
    (Y : Fin n → localDualQuotientTarget D) :
    Fin n → localDualQuotientTarget E :=
  fun i => localDualQuotientMapOfLE (n := n) hDE (Y i)

/-- If every one-column fiber of the denominator-enlargement quotient map has
cardinality `c`, then the basis-family fiber has cardinality `c^n`. -/
lemma localDualQuotientFamilyOfLE_fiber_card_eq_pow
    {D E : Submodule ℤ (Fin n → ℤ)}
    (hD_rank : Module.finrank ℤ D = n)
    (hE_rank : Module.finrank ℤ E = n) (hDE : D ≤ E)
    (Y : Fin n → localDualQuotientTarget E) (c : ℕ)
    (hfiber : ∀ q : localDualQuotientTarget E,
      Nat.card
          {x : localDualQuotientTarget D //
            localDualQuotientMapOfLE (n := n) hDE x = q} = c) :
    Nat.card
        {X : Fin n → localDualQuotientTarget D //
          localDualQuotientFamilyOfLE (n := n) hDE X = Y} =
      c ^ n := by
  classical
  have hD_rank' : Module.finrank ℤ D = Module.finrank ℤ (Fin n → ℤ) := by
    simpa [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using hD_rank
  have hE_rank' : Module.finrank ℤ E = Module.finrank ℤ (Fin n → ℤ) := by
    simpa [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using hE_rank
  letI : Finite (localDualQuotientTarget D) :=
    Submodule.finiteQuotientOfFreeOfRankEq (M := Fin n → ℤ) D hD_rank'
  letI : Fintype (localDualQuotientTarget D) :=
    Fintype.ofFinite (localDualQuotientTarget D)
  letI : Finite (localDualQuotientTarget E) :=
    Submodule.finiteQuotientOfFreeOfRankEq (M := Fin n → ℤ) E hE_rank'
  letI : Fintype (localDualQuotientTarget E) :=
    Fintype.ofFinite (localDualQuotientTarget E)
  calc
    Nat.card
        {X : Fin n → localDualQuotientTarget D //
          localDualQuotientFamilyOfLE (n := n) hDE X = Y} =
        Nat.card
          {X : Fin n → localDualQuotientTarget D //
            (fun i : Fin n =>
              localDualQuotientMapOfLE (n := n) hDE (X i)) = Y} := by
          rfl
    _ = c ^ Fintype.card (Fin n) := by
          exact nat_card_pi_map_fiber_eq_pow
            (f := localDualQuotientMapOfLE (n := n) hDE) Y c hfiber
    _ = c ^ n := by
          simp

/-- A subquotient cardinal computation for one column gives the corresponding
`c^n` cardinality for the whole basis-family fiber. -/
lemma localDualQuotientFamilyOfLE_fiber_card_eq_pow_of_subquotient_card
    {D E : Submodule ℤ (Fin n → ℤ)}
    (hD_rank : Module.finrank ℤ D = n)
    (hE_rank : Module.finrank ℤ E = n) (hDE : D ≤ E)
    (Y : Fin n → localDualQuotientTarget E) (c : ℕ)
    (hsubquot : Nat.card (E ⧸ D.comap E.subtype) = c) :
    Nat.card
        {X : Fin n → localDualQuotientTarget D //
          localDualQuotientFamilyOfLE (n := n) hDE X = Y} =
      c ^ n := by
  refine localDualQuotientFamilyOfLE_fiber_card_eq_pow
    (n := n) hD_rank hE_rank hDE Y c ?_
  intro q
  rw [localDualQuotientMapOfLE_fiber_card_eq_ker (n := n) hDE q,
    localDualQuotientMapOfLE_ker_card_eq_subquotient (n := n) hDE,
    hsubquot]

/-- For the form-matrix local-dual denominator, a one-column subquotient
cardinality `p^v` yields the expected `p^(n*v)` cardinality for the full
basis-family fiber. -/
lemma pairingMatrixLocalDualQuotientFamilyOfLE_fiber_card_eq_prime_pow
    (L : PositiveDefiniteIntegralLattice n) (p k v : ℕ) [Fact (Nat.Prime p)]
    (Y : Fin n → localDualQuotientTarget
      (pairingMatrixLocalDualCoordinateSubmodule L p k))
    (hsubquot :
      Nat.card
          (pairingMatrixLocalDualCoordinateSubmodule L p k ⧸
            (primePowCoordinateSubmodule (n := n) p k).comap
              (pairingMatrixLocalDualCoordinateSubmodule L p k).subtype) =
        p ^ v) :
    Nat.card
        {X : Fin n → localDualQuotientTarget
            (primePowCoordinateSubmodule (n := n) p k) //
          localDualQuotientFamilyOfLE (n := n)
            (primePowCoordinateSubmodule_le_pairingMatrixLocalDualCoordinateSubmodule
              (n := n) L p k) X = Y} =
      p ^ (n * v) := by
  have hfamily :=
    localDualQuotientFamilyOfLE_fiber_card_eq_pow_of_subquotient_card
      (n := n)
      (primePowCoordinateSubmodule_rank (n := n) p k)
      (pairingMatrixLocalDualCoordinateSubmodule_rank (n := n) L p k)
      (primePowCoordinateSubmodule_le_pairingMatrixLocalDualCoordinateSubmodule
        (n := n) L p k)
      Y (p ^ v) hsubquot
  calc
    Nat.card
        {X : Fin n → localDualQuotientTarget
            (primePowCoordinateSubmodule (n := n) p k) //
          localDualQuotientFamilyOfLE (n := n)
            (primePowCoordinateSubmodule_le_pairingMatrixLocalDualCoordinateSubmodule
              (n := n) L p k) X = Y} =
        (p ^ v) ^ n := hfamily
    _ = p ^ (n * v) := by
          rw [← Nat.pow_mul]
          rw [Nat.mul_comm]

lemma quotientBasisFamilyMap_ofLE
    {D E : Submodule ℤ (Fin n → ℤ)} (hDE : D ≤ E)
    (Y : Fin n → localDualQuotientTarget D) (x : Fin n → ℤ) :
    quotientBasisFamilyMap E (localDualQuotientFamilyOfLE (n := n) hDE Y) x =
      localDualQuotientMapOfLE (n := n) hDE
        (quotientBasisFamilyMap D Y x) := by
  classical
  simp [quotientBasisFamilyMap, localDualQuotientFamilyOfLE,
    map_sum]

/-- The `p`-adic quotient value represented by the same integral coordinates
and a family in the integral-integral model quotient.  This is the `p`-adic quotient
side of `quotientBasisFamilyMap` after casting each basis image through
`padicSubmoduleIntegralPreimageQuotientMap`. -/
def padicQuotientBasisFamilyMap
    (p : ℕ) [Fact (Nat.Prime p)]
    (D : Submodule ℤ_[p] (Fin n → ℤ_[p]))
    (Y : Fin n → localDualQuotientTarget (padicSubmoduleIntegralPreimage (n := n) p D))
    (x : Fin n → ℤ) :
    ((Fin n → ℤ_[p]) ⧸ D) :=
  ∑ i : Fin n, (x i : ℤ_[p]) •
    padicSubmoduleIntegralPreimageQuotientMap (n := n) p D (Y i)

/-- The same p-adic quotient linear combination, with the basis images already
living in the p-adic quotient.  This is the algebraic target for transporting
quotient-family values across a p-adic local isometry before proving that the
transported values lift back to an integral integral model quotient. -/
def padicQuotientBasisFamilyMapFromPadicValues
    (p : ℕ) [Fact (Nat.Prime p)]
    (D : Submodule ℤ_[p] (Fin n → ℤ_[p]))
    (Y : Fin n → ((Fin n → ℤ_[p]) ⧸ D))
    (x : Fin n → ℤ_[p]) :
    ((Fin n → ℤ_[p]) ⧸ D) :=
  ∑ i : Fin n, x i • Y i

lemma padicQuotientBasisFamilyMapFromPadicValues_basisFun
    (p : ℕ) [Fact (Nat.Prime p)]
    (D : Submodule ℤ_[p] (Fin n → ℤ_[p]))
    (Y : Fin n → ((Fin n → ℤ_[p]) ⧸ D)) (i : Fin n) :
    padicQuotientBasisFamilyMapFromPadicValues (n := n) p D Y
        ((Pi.basisFun ℤ_[p] (Fin n)) i) = Y i := by
  classical
  simp [padicQuotientBasisFamilyMapFromPadicValues]

/-- The p-adic linear map represented by p-adic quotient images of the
coordinate basis. -/
def padicQuotientBasisFamilyLinearMapFromPadicValues
    (p : ℕ) [Fact (Nat.Prime p)]
    (D : Submodule ℤ_[p] (Fin n → ℤ_[p]))
    (Y : Fin n → ((Fin n → ℤ_[p]) ⧸ D)) :
    (Fin n → ℤ_[p]) →ₗ[ℤ_[p]] ((Fin n → ℤ_[p]) ⧸ D) where
  toFun := padicQuotientBasisFamilyMapFromPadicValues (n := n) p D Y
  map_add' x y := by
    classical
    simp [padicQuotientBasisFamilyMapFromPadicValues, Pi.add_apply, add_smul,
      Finset.sum_add_distrib]
  map_smul' a x := by
    classical
    simp [padicQuotientBasisFamilyMapFromPadicValues, Pi.smul_apply,
      Finset.smul_sum, smul_smul]

lemma localDualPadicDenominator_primePow_smul_quotient_eq_zero
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (q : ((Fin n → ℤ_[p]) ⧸ localDualPadicDenominator L p k)) :
    ((p : ℤ_[p]) ^ k) • q = 0 := by
  induction q using Quotient.inductionOn with
  | h v =>
      change (Submodule.Quotient.mk (((p : ℤ_[p]) ^ k) • v) :
          (Fin n → ℤ_[p]) ⧸ localDualPadicDenominator L p k) =
        Submodule.Quotient.mk 0
      rw [Submodule.Quotient.eq]
      simpa using primePow_smul_mem_localDualPadicDenominator (n := n) L p k v

lemma smul_localDualPadicDenominator_quotient_eq_zero_of_primePow_dvd
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    {a : ℤ_[p]} (ha : ((p : ℤ_[p]) ^ k ∣ a))
    (q : ((Fin n → ℤ_[p]) ⧸ localDualPadicDenominator L p k)) :
    a • q = 0 := by
  rcases ha with ⟨b, rfl⟩
  calc
    (((p : ℤ_[p]) ^ k) * b) • q =
        ((p : ℤ_[p]) ^ k) • (b • q) := by
          exact (smul_smul ((p : ℤ_[p]) ^ k) b q).symm
    _ = 0 := by
          rw [localDualPadicDenominator_primePow_smul_quotient_eq_zero]

lemma exists_integralVectorToPadic_forall_primePow_dvd_sub
    (p k : ℕ) [Fact (Nat.Prime p)] (v : Fin n → ℤ_[p]) :
    ∃ x : Fin n → ℤ,
      ∀ i : Fin n,
        ((p : ℤ_[p]) ^ k ∣ v i - integralVectorToPadic (n := n) p x i) := by
  classical
  choose x hx using fun i : Fin n => padicInt_exists_int_sub_mem_span_primePow p k (v i)
  exact ⟨x, by intro i; simpa [integralVectorToPadic] using hx i⟩

lemma padicInt_toZModPow_eq_intCast_of_primePow_dvd_sub
    (p k : ℕ) [Fact (Nat.Prime p)] (a : ℤ_[p]) (z : ℤ)
    (h : ((p : ℤ_[p]) ^ k ∣ a - (z : ℤ_[p]))) :
    PadicInt.toZModPow k a = (z : ZMod (p ^ k)) := by
  have hker :
      a - (z : ℤ_[p]) ∈ RingHom.ker (PadicInt.toZModPow (p := p) k) := by
    rw [PadicInt.ker_toZModPow]
    exact Ideal.mem_span_singleton.mpr h
  have hzero := RingHom.mem_ker.mp hker
  exact sub_eq_zero.mp (by simpa [map_sub] using hzero)

set_option backward.isDefEq.respectTransparency false in
lemma padic_quadForm_toZModPow_eq_of_forall_primePow_dvd_sub
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (v : Fin n → ℤ_[p]) (x : Fin n → ℤ)
    (hv : ∀ i : Fin n,
      ((p : ℤ_[p]) ^ k ∣ v i - integralVectorToPadic (n := n) p x i)) :
    PadicInt.toZModPow k
        (dotProduct v ((L.pairingMatrix_padic p).mulVec v)) =
      (L.quadForm x : ZMod (primePowModulus p k : ℕ)) := by
  have hvi :
      ∀ i : Fin n, PadicInt.toZModPow k (v i) = (x i : ZMod (p ^ k)) := by
    intro i
    exact padicInt_toZModPow_eq_intCast_of_primePow_dvd_sub p k
      (v i) (x i) (hv i)
  simp [pairingMatrix_padic, quadForm_eq_dotProduct, dotProduct,
    Matrix.mulVec, hvi]

lemma quadForm_zmod_eq_of_local_isometry_matrix_approx
    {L₀ L₁ : PositiveDefiniteIntegralLattice n} (p k : ℕ) [Fact (Nat.Prime p)]
    {U : Matrix (Fin n) (Fin n) ℤ_[p]}
    (hU : Uᵀ * L₁.pairingMatrix_padic p * U = L₀.pairingMatrix_padic p)
    (v : Fin n → ℤ_[p]) (x y : Fin n → ℤ)
    (hv : ∀ i : Fin n,
      ((p : ℤ_[p]) ^ k ∣ v i - integralVectorToPadic (n := n) p x i))
    (hUy : U.mulVec v = integralVectorToPadic (n := n) p y) :
    (L₀.quadForm x : ZMod (primePowModulus p k : ℕ)) =
      (L₁.quadForm y : ZMod (primePowModulus p k : ℕ)) := by
  have hsource :=
    padic_quadForm_toZModPow_eq_of_forall_primePow_dvd_sub
      (n := n) L₀ p k v x hv
  have htarget_approx :
      ∀ i : Fin n,
        ((p : ℤ_[p]) ^ k ∣
          (U.mulVec v) i - integralVectorToPadic (n := n) p y i) := by
    intro i
    rw [hUy]
    simp
  have htarget :=
    padic_quadForm_toZModPow_eq_of_forall_primePow_dvd_sub
      (n := n) L₁ p k (U.mulVec v) y htarget_approx
  have hquad :=
    congrArg (PadicInt.toZModPow k)
      (padic_dotProduct_mulVec_eq_of_local_isometry_matrix
        (L₀ := L₀) (L₁ := L₁) p hU v v)
  rwa [hsource, htarget] at hquad

lemma padicQuotientBasisFamilyMapFromPadicValues_eq_of_forall_primePow_dvd_sub
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (Y : Fin n → ((Fin n → ℤ_[p]) ⧸ localDualPadicDenominator L p k))
    (v : Fin n → ℤ_[p]) (x : Fin n → ℤ)
    (hv : ∀ i : Fin n,
      ((p : ℤ_[p]) ^ k ∣ v i - integralVectorToPadic (n := n) p x i)) :
    padicQuotientBasisFamilyMapFromPadicValues (n := n) p
        (localDualPadicDenominator L p k) Y v =
      padicQuotientBasisFamilyMapFromPadicValues (n := n) p
        (localDualPadicDenominator L p k) Y
        (integralVectorToPadic (n := n) p x) := by
  classical
  refine Finset.sum_congr rfl ?_
  intro i _
  have hzero :
      (v i - integralVectorToPadic (n := n) p x i) • Y i = 0 :=
    smul_localDualPadicDenominator_quotient_eq_zero_of_primePow_dvd
      (n := n) L p k (hv i) (Y i)
  have hvadd :
      integralVectorToPadic (n := n) p x i +
          (v i - integralVectorToPadic (n := n) p x i) =
        v i := by
    ring
  calc
    v i • Y i =
        (integralVectorToPadic (n := n) p x i +
          (v i - integralVectorToPadic (n := n) p x i)) • Y i := by
          exact congrArg (fun a => a • Y i) hvadd.symm
    _ = integralVectorToPadic (n := n) p x i • Y i := by
          rw [add_smul, hzero, add_zero]

lemma padicQuotientBasisFamilyMap_eq_of_forall_primePow_dvd_sub
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (Y : Fin n → localDualQuotientTarget
      (padicSubmoduleIntegralPreimage (n := n) p
        (localDualPadicDenominator L p k)))
    (v : Fin n → ℤ_[p]) (x : Fin n → ℤ)
    (hv : ∀ i : Fin n,
      ((p : ℤ_[p]) ^ k ∣ v i - integralVectorToPadic (n := n) p x i)) :
    padicQuotientBasisFamilyMapFromPadicValues (n := n) p
        (localDualPadicDenominator L p k)
        (fun i => padicSubmoduleIntegralPreimageQuotientMap (n := n) p
          (localDualPadicDenominator L p k) (Y i)) v =
      padicQuotientBasisFamilyMap (n := n) p
        (localDualPadicDenominator L p k) Y x := by
  rw [padicQuotientBasisFamilyMapFromPadicValues_eq_of_forall_primePow_dvd_sub
    (n := n) L p k _ v x hv]
  rfl

noncomputable def padicQuotientTransportedBasisFamily
    (p : ℕ) [Fact (Nat.Prime p)]
    (D E : Submodule ℤ_[p] (Fin n → ℤ_[p]))
    (e : (Fin n → ℤ_[p]) ≃ₗ[ℤ_[p]] (Fin n → ℤ_[p]))
    (hDE : Submodule.map e.toLinearMap D = E)
    (Y : Fin n → ((Fin n → ℤ_[p]) ⧸ D)) :
    Fin n → ((Fin n → ℤ_[p]) ⧸ E) :=
  fun i => Submodule.Quotient.equiv D E e hDE
    (padicQuotientBasisFamilyMapFromPadicValues (n := n) p D Y
      (e.symm ((Pi.basisFun ℤ_[p] (Fin n)) i)))

lemma padicQuotientBasisFamilyMapFromPadicValues_transport
    (p : ℕ) [Fact (Nat.Prime p)]
    (D E : Submodule ℤ_[p] (Fin n → ℤ_[p]))
    (e : (Fin n → ℤ_[p]) ≃ₗ[ℤ_[p]] (Fin n → ℤ_[p]))
    (hDE : Submodule.map e.toLinearMap D = E)
    (Y : Fin n → ((Fin n → ℤ_[p]) ⧸ D)) (x : Fin n → ℤ_[p]) :
    padicQuotientBasisFamilyMapFromPadicValues (n := n) p E
        (padicQuotientTransportedBasisFamily (n := n) p D E e hDE Y) x =
      Submodule.Quotient.equiv D E e hDE
        (padicQuotientBasisFamilyMapFromPadicValues (n := n) p D Y (e.symm x)) := by
  classical
  let φ := Submodule.Quotient.equiv D E e hDE
  let f := padicQuotientBasisFamilyLinearMapFromPadicValues (n := n) p D Y
  have hx :
      (∑ i : Fin n, x i • e.symm ((Pi.basisFun ℤ_[p] (Fin n)) i)) =
        e.symm x := by
    calc
      (∑ i : Fin n, x i • e.symm ((Pi.basisFun ℤ_[p] (Fin n)) i)) =
          e.symm (∑ i : Fin n, x i • (Pi.basisFun ℤ_[p] (Fin n)) i) := by
            rw [map_sum]
            refine Finset.sum_congr rfl ?_
            intro i _
            exact (map_smul e.symm (x i) ((Pi.basisFun ℤ_[p] (Fin n)) i)).symm
      _ = e.symm x := by
            simpa using congrArg e.symm ((Pi.basisFun ℤ_[p] (Fin n)).sum_repr x)
  calc
    padicQuotientBasisFamilyMapFromPadicValues (n := n) p E
        (padicQuotientTransportedBasisFamily (n := n) p D E e hDE Y) x =
        ∑ i : Fin n, x i • φ
          (padicQuotientBasisFamilyMapFromPadicValues (n := n) p D Y
            (e.symm ((Pi.basisFun ℤ_[p] (Fin n)) i))) := by
          rfl
    _ = φ (∑ i : Fin n,
          x i • padicQuotientBasisFamilyMapFromPadicValues (n := n) p D Y
            (e.symm ((Pi.basisFun ℤ_[p] (Fin n)) i))) := by
          rw [map_sum]
          refine Finset.sum_congr rfl ?_
          intro i _
          exact (map_smul φ (x i)
            (padicQuotientBasisFamilyMapFromPadicValues (n := n) p D Y
              (e.symm ((Pi.basisFun ℤ_[p] (Fin n)) i)))).symm
    _ = φ (f (∑ i : Fin n, x i • e.symm ((Pi.basisFun ℤ_[p] (Fin n)) i))) := by
          refine congrArg φ ?_
          rw [map_sum]
          refine Finset.sum_congr rfl ?_
          intro i _
          exact (map_smul f (x i) (e.symm ((Pi.basisFun ℤ_[p] (Fin n)) i))).symm
    _ = φ (padicQuotientBasisFamilyMapFromPadicValues (n := n) p D Y (e.symm x)) := by
          rw [hx]
          rfl

lemma padicSubmodule_map_symm_eq_of_map_eq
    (p : ℕ) [Fact (Nat.Prime p)]
    (D E : Submodule ℤ_[p] (Fin n → ℤ_[p]))
    (e : (Fin n → ℤ_[p]) ≃ₗ[ℤ_[p]] (Fin n → ℤ_[p]))
    (hDE : Submodule.map e.toLinearMap D = E) :
    Submodule.map e.symm.toLinearMap E = D := by
  rw [← hDE, ← Submodule.map_comp]
  change Submodule.map (e.symm.toLinearMap.comp e.toLinearMap) D = D
  simp [Submodule.map_id]

lemma padicQuotientTransportedBasisFamily_symm
    (p : ℕ) [Fact (Nat.Prime p)]
    (D E : Submodule ℤ_[p] (Fin n → ℤ_[p]))
    (e : (Fin n → ℤ_[p]) ≃ₗ[ℤ_[p]] (Fin n → ℤ_[p]))
    (hDE : Submodule.map e.toLinearMap D = E)
    (Y : Fin n → ((Fin n → ℤ_[p]) ⧸ D)) :
    padicQuotientTransportedBasisFamily (n := n) p E D e.symm
        (padicSubmodule_map_symm_eq_of_map_eq (n := n) p D E e hDE)
        (padicQuotientTransportedBasisFamily (n := n) p D E e hDE Y) = Y := by
  classical
  let hED := padicSubmodule_map_symm_eq_of_map_eq (n := n) p D E e hDE
  let φ := Submodule.Quotient.equiv D E e hDE
  let ψ := Submodule.Quotient.equiv E D e.symm hED
  ext i
  have hψφ : ∀ q : ((Fin n → ℤ_[p]) ⧸ D), ψ (φ q) = q := by
    intro q
    induction q using Quotient.inductionOn with
    | h a =>
        change D.mkQ (e.symm (e a)) = D.mkQ a
        rw [e.symm_apply_apply]
  have hmap :=
    padicQuotientBasisFamilyMapFromPadicValues_transport (n := n) p D E e hDE Y
      (e ((Pi.basisFun ℤ_[p] (Fin n)) i))
  change ψ (padicQuotientBasisFamilyMapFromPadicValues (n := n) p E
      (padicQuotientTransportedBasisFamily (n := n) p D E e hDE Y)
      (e ((Pi.basisFun ℤ_[p] (Fin n)) i))) = Y i
  rw [hmap]
  rw [e.symm_apply_apply, padicQuotientBasisFamilyMapFromPadicValues_basisFun, hψφ]

lemma padicQuotientBasisFamilyMapFromPadicValues_transport_eq_mkQ_iff
    (p : ℕ) [Fact (Nat.Prime p)]
    (D E : Submodule ℤ_[p] (Fin n → ℤ_[p]))
    (e : (Fin n → ℤ_[p]) ≃ₗ[ℤ_[p]] (Fin n → ℤ_[p]))
    (hDE : Submodule.map e.toLinearMap D = E)
    (Y : Fin n → ((Fin n → ℤ_[p]) ⧸ D))
    (x y : Fin n → ℤ_[p]) :
    padicQuotientBasisFamilyMapFromPadicValues (n := n) p E
        (padicQuotientTransportedBasisFamily (n := n) p D E e hDE Y) x =
        E.mkQ y ↔
      padicQuotientBasisFamilyMapFromPadicValues (n := n) p D Y (e.symm x) =
        D.mkQ (e.symm y) := by
  classical
  let φ := Submodule.Quotient.equiv D E e hDE
  let ψ := Submodule.Quotient.equiv E D e.symm
    (padicSubmodule_map_symm_eq_of_map_eq (n := n) p D E e hDE)
  have htransport :=
    padicQuotientBasisFamilyMapFromPadicValues_transport (n := n) p D E e hDE Y x
  have hψφ : ∀ q : ((Fin n → ℤ_[p]) ⧸ D), ψ (φ q) = q := by
    intro q
    induction q using Quotient.inductionOn with
    | h a =>
        change D.mkQ (e.symm (e a)) = D.mkQ a
        rw [e.symm_apply_apply]
  have hψ_mk : ψ (E.mkQ y) = D.mkQ (e.symm y) := by
    simp [ψ, Submodule.Quotient.equiv]
  have hφ_mk : φ (D.mkQ (e.symm y)) = E.mkQ y := by
    simp [φ, Submodule.Quotient.equiv]
  constructor
  · intro h
    have happly := congrArg ψ h
    rw [htransport, hψφ, hψ_mk] at happly
    exact happly
  · intro h
    rw [htransport, h, hφ_mk]

lemma padicSubmoduleIntegralPreimageQuotientMap_quotientBasisFamilyMap
    (p : ℕ) [Fact (Nat.Prime p)]
    (D : Submodule ℤ_[p] (Fin n → ℤ_[p]))
    (Y : Fin n → localDualQuotientTarget (padicSubmoduleIntegralPreimage (n := n) p D))
    (x : Fin n → ℤ) :
    padicSubmoduleIntegralPreimageQuotientMap (n := n) p D
        (quotientBasisFamilyMap (padicSubmoduleIntegralPreimage (n := n) p D) Y x) =
      padicQuotientBasisFamilyMap (n := n) p D Y x := by
  classical
  simp [quotientBasisFamilyMap, padicQuotientBasisFamilyMap,
    Int.cast_smul_eq_zsmul]

/-- Choose integral-preimage quotient basis images lifting the p-adically
transported basis images for the actual local-dual denominator. -/
noncomputable def localDualPadicTransportedIntegralPreimageBasisFamily
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (D : Submodule ℤ_[p] (Fin n → ℤ_[p]))
    (e : (Fin n → ℤ_[p]) ≃ₗ[ℤ_[p]] (Fin n → ℤ_[p]))
    (hDE : Submodule.map e.toLinearMap D = localDualPadicDenominator L p k)
    (Y : Fin n → ((Fin n → ℤ_[p]) ⧸ D)) :
    Fin n → localDualQuotientTarget
      (padicSubmoduleIntegralPreimage (n := n) p
        (localDualPadicDenominator L p k)) :=
  fun i =>
    Classical.choose
      (padicSubmoduleIntegralPreimageQuotientMap_surjective_localDualPadicDenominator
        (n := n) L p k
        (padicQuotientTransportedBasisFamily (n := n) p D
          (localDualPadicDenominator L p k) e hDE Y i))

lemma padicSubmoduleIntegralPreimageQuotientMap_localDualPadicTransportedIntegralPreimageBasisFamily
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (D : Submodule ℤ_[p] (Fin n → ℤ_[p]))
    (e : (Fin n → ℤ_[p]) ≃ₗ[ℤ_[p]] (Fin n → ℤ_[p]))
    (hDE : Submodule.map e.toLinearMap D = localDualPadicDenominator L p k)
    (Y : Fin n → ((Fin n → ℤ_[p]) ⧸ D)) (i : Fin n) :
    padicSubmoduleIntegralPreimageQuotientMap (n := n) p
        (localDualPadicDenominator L p k)
        (localDualPadicTransportedIntegralPreimageBasisFamily
          (n := n) L p k D e hDE Y i) =
      padicQuotientTransportedBasisFamily (n := n) p D
        (localDualPadicDenominator L p k) e hDE Y i := by
  exact Classical.choose_spec
    (padicSubmoduleIntegralPreimageQuotientMap_surjective_localDualPadicDenominator
      (n := n) L p k
      (padicQuotientTransportedBasisFamily (n := n) p D
        (localDualPadicDenominator L p k) e hDE Y i))

lemma padicSubmoduleIntegralPreimageQuotientMap_quotientBasisFamilyMap_localDualPadicTransported
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (D : Submodule ℤ_[p] (Fin n → ℤ_[p]))
    (e : (Fin n → ℤ_[p]) ≃ₗ[ℤ_[p]] (Fin n → ℤ_[p]))
    (hDE : Submodule.map e.toLinearMap D = localDualPadicDenominator L p k)
    (Y : Fin n → ((Fin n → ℤ_[p]) ⧸ D)) (x : Fin n → ℤ) :
    padicSubmoduleIntegralPreimageQuotientMap (n := n) p
        (localDualPadicDenominator L p k)
        (quotientBasisFamilyMap
          (padicSubmoduleIntegralPreimage (n := n) p
            (localDualPadicDenominator L p k))
          (localDualPadicTransportedIntegralPreimageBasisFamily
            (n := n) L p k D e hDE Y) x) =
      padicQuotientBasisFamilyMapFromPadicValues (n := n) p
        (localDualPadicDenominator L p k)
        (padicQuotientTransportedBasisFamily (n := n) p D
          (localDualPadicDenominator L p k) e hDE Y)
        (integralVectorToPadic (n := n) p x) := by
  classical
  calc
    padicSubmoduleIntegralPreimageQuotientMap (n := n) p
        (localDualPadicDenominator L p k)
        (quotientBasisFamilyMap
          (padicSubmoduleIntegralPreimage (n := n) p
            (localDualPadicDenominator L p k))
          (localDualPadicTransportedIntegralPreimageBasisFamily
            (n := n) L p k D e hDE Y) x) =
        padicQuotientBasisFamilyMap (n := n) p
          (localDualPadicDenominator L p k)
          (localDualPadicTransportedIntegralPreimageBasisFamily
            (n := n) L p k D e hDE Y) x := by
          exact padicSubmoduleIntegralPreimageQuotientMap_quotientBasisFamilyMap
            (n := n) p (localDualPadicDenominator L p k)
            (localDualPadicTransportedIntegralPreimageBasisFamily
              (n := n) L p k D e hDE Y) x
    _ = padicQuotientBasisFamilyMapFromPadicValues (n := n) p
        (localDualPadicDenominator L p k)
        (padicQuotientTransportedBasisFamily (n := n) p D
          (localDualPadicDenominator L p k) e hDE Y)
        (integralVectorToPadic (n := n) p x) := by
          simp [padicQuotientBasisFamilyMap,
            padicQuotientBasisFamilyMapFromPadicValues,
            padicSubmoduleIntegralPreimageQuotientMap_localDualPadicTransportedIntegralPreimageBasisFamily,
            integralVectorToPadic]

lemma quotientBasisFamilyMap_localDualPadicTransportedIntegralPreimageBasisFamily_eq_mkQ_iff
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (D : Submodule ℤ_[p] (Fin n → ℤ_[p]))
    (e : (Fin n → ℤ_[p]) ≃ₗ[ℤ_[p]] (Fin n → ℤ_[p]))
    (hDE : Submodule.map e.toLinearMap D = localDualPadicDenominator L p k)
    (Y : Fin n → ((Fin n → ℤ_[p]) ⧸ D)) (x y : Fin n → ℤ) :
    quotientBasisFamilyMap
        (padicSubmoduleIntegralPreimage (n := n) p
          (localDualPadicDenominator L p k))
        (localDualPadicTransportedIntegralPreimageBasisFamily
          (n := n) L p k D e hDE Y) x =
        (padicSubmoduleIntegralPreimage (n := n) p
          (localDualPadicDenominator L p k)).mkQ y ↔
      padicQuotientBasisFamilyMapFromPadicValues (n := n) p
          (localDualPadicDenominator L p k)
          (padicQuotientTransportedBasisFamily (n := n) p D
            (localDualPadicDenominator L p k) e hDE Y)
          (integralVectorToPadic (n := n) p x) =
        (localDualPadicDenominator L p k).mkQ
          (integralVectorToPadic (n := n) p y) := by
  let E := localDualPadicDenominator L p k
  let f := padicSubmoduleIntegralPreimageQuotientMap (n := n) p E
  constructor
  · intro h
    have happly := congrArg f h
    rw [padicSubmoduleIntegralPreimageQuotientMap_quotientBasisFamilyMap_localDualPadicTransported
      (n := n) L p k D e hDE Y x] at happly
    simpa [E, f] using happly
  · intro h
    refine padicSubmoduleIntegralPreimageQuotientMap_injective (n := n) p E ?_
    rw [padicSubmoduleIntegralPreimageQuotientMap_quotientBasisFamilyMap_localDualPadicTransported
      (n := n) L p k D e hDE Y x]
    simpa [E, f] using h

/-- The linear map represented by a family of quotient images of the coordinate
basis. -/
def quotientBasisFamilyLinearMap (D : Submodule ℤ (Fin n → ℤ))
    (Y : Fin n → localDualQuotientTarget D) :
    (Fin n → ℤ) →ₗ[ℤ] localDualQuotientTarget D where
  toFun := quotientBasisFamilyMap D Y
  map_add' := quotientBasisFamilyMap_add D Y
  map_smul' := quotientBasisFamilyMap_zsmul D Y

/-- The matrix over `ZMod (p^k)` attached to a family of quotient basis images
for the good-prime coordinate quotient `ℤ^n / p^kℤ^n`.  The `j`th column is the
coordinate vector of the image of the `j`th basis vector. -/
def localDualQuotientFamilyMatrix
    (p k : ℕ) [Fact (Nat.Prime p)]
    (Y : Fin n →
      localDualQuotientTarget (primePowCoordinateSubmodule (n := n) p k)) :
    Matrix (Fin n) (Fin n) (ZMod (primePowModulus p k : ℕ)) :=
  fun i j => primePowQuotientCoordinate (n := n) p k i (Y j)

lemma localDualQuotientFamilyMatrix_mulVec_eq
    (p k : ℕ) [Fact (Nat.Prime p)]
    (Y : Fin n →
      localDualQuotientTarget (primePowCoordinateSubmodule (n := n) p k))
    (x : Fin n → ℤ) :
    (localDualQuotientFamilyMatrix (n := n) p k Y).mulVec
        (fun j : Fin n => (x j : ZMod (primePowModulus p k : ℕ))) =
      primePowQuotientVector (n := n) p k
        (quotientBasisFamilyMap (primePowCoordinateSubmodule (n := n) p k) Y x) := by
  classical
  ext i
  simp [localDualQuotientFamilyMatrix, primePowQuotientVector,
    quotientBasisFamilyMap, Matrix.mulVec, dotProduct, mul_comm]

@[simp] lemma localDualQuotientFamilyMatrix_identity
    (p k : ℕ) [Fact (Nat.Prime p)] :
    localDualQuotientFamilyMatrix (n := n) p k
        (quotientIdentityBasisFamily
          (primePowCoordinateSubmodule (n := n) p k)) =
      (1 : Matrix (Fin n) (Fin n) (ZMod (primePowModulus p k : ℕ))) := by
  ext i j
  rw [localDualQuotientFamilyMatrix, quotientIdentityBasisFamily,
    primePowQuotientCoordinate_mkQ]
  by_cases hij : i = j
  · subst i
    simp
  · simp [hij]

/-- Admissibility for a coordinate local-dual quotient: the submodule is
full-rank, hence the quotient is finite, and the quadratic form is well-defined
modulo `p^k` on its quotient classes. -/
def IsDualQuotientAdmissible (L : PositiveDefiniteIntegralLattice n) (p k : ℕ)
    [Fact (Nat.Prime p)] (D : Submodule ℤ (Fin n → ℤ)) : Prop :=
  Module.finrank ℤ D = n ∧
    ∀ ⦃x y : Fin n → ℤ⦄, y - x ∈ D →
      (L.quadForm y : ZMod (primePowModulus p k : ℕ)) =
        (L.quadForm x : ZMod (primePowModulus p k : ℕ))

lemma quadForm_add_eq_bilinearFormValue
    (L : PositiveDefiniteIntegralLattice n) (x d : Fin n → ℤ) :
    L.quadForm (x + d) =
      L.quadForm x + 2 * L.bilinearFormValue x d + L.quadForm d := by
  calc
    L.quadForm (x + d) =
        dotProduct (x + d) (L.pairingMatrix.mulVec (x + d)) := by
          rw [L.quadForm_eq_dotProduct]
    _ = dotProduct (x + d) (L.pairingMatrix.mulVec x + L.pairingMatrix.mulVec d) := by
          rw [Matrix.mulVec_add]
    _ = L.quadForm x + L.bilinearFormValue x d +
          L.bilinearFormValue d x + L.quadForm d := by
          simp [quadForm_eq_dotProduct, bilinearFormValue, dotProduct,
            Finset.sum_add_distrib, add_mul, mul_add]
          abel_nf
    _ = L.quadForm x + 2 * L.bilinearFormValue x d + L.quadForm d := by
          rw [L.bilinearFormValue_comm d x]
          ring

/-- The associated-bilinear Gram pairing is twice the stored symmetric
bilinear value. -/
lemma dotProduct_polarGramMatrix_mulVec
    (L : PositiveDefiniteIntegralLattice n) (x y : Fin n → ℤ) :
    dotProduct x (L.polarGramMatrix.mulVec y) =
      2 * L.bilinearFormValue x y := by
  rw [L.polarGramMatrix_eq_two_smul_pairingMatrix, Matrix.smul_mulVec,
    dotProduct_smul]
  rfl

/-- Coordinate assumptions for the actual Schulze--Pillot denominator
`p^k L_p# ∩ L`.

The first field says the quotient is finite in the coordinate model.  The
second and third fields are the coordinate integral models of the source-side
conditions that elements of the denominator pair integrally with `L` modulo
`p^k`, and have quadratic value divisible by `p^k`. -/
def IsDualCoordinateDenominator (L : PositiveDefiniteIntegralLattice n) (p k : ℕ)
    [Fact (Nat.Prime p)] (D : Submodule ℤ (Fin n → ℤ)) : Prop :=
  Module.finrank ℤ D = n ∧
    (∀ x d : Fin n → ℤ, d ∈ D →
      ((L.bilinearFormValue x d : ℤ) :
        ZMod (primePowModulus p k : ℕ)) = 0) ∧
    (∀ d : Fin n → ℤ, d ∈ D →
      ((L.quadForm d : ℤ) : ZMod (primePowModulus p k : ℕ)) = 0)

lemma pairingMatrixLocalDualCoordinateSubmodule_isDualCoordinateDenominator
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] :
    IsDualCoordinateDenominator L p k
      (pairingMatrixLocalDualCoordinateSubmodule L p k) := by
  refine ⟨pairingMatrixLocalDualCoordinateSubmodule_rank (n := n) L p k, ?_, ?_⟩
  · intro x d hd
    let m : ℕ+ := primePowModulus p k
    have hFd :
        (matrixMod L.pairingMatrix m).mulVec
          (fun j : Fin n => (d j : ZMod (m : ℕ))) = 0 := by
      simpa [pairingMatrixLocalDualCoordinateSubmodule, matrixModLinearMap, m]
        using hd
    change ((dotProduct x (L.pairingMatrix.mulVec d) : ℤ) :
        ZMod (primePowModulus p k : ℕ)) = 0
    calc
      ((dotProduct x (L.pairingMatrix.mulVec d) : ℤ) :
          ZMod (primePowModulus p k : ℕ)) =
          dotProduct (fun i : Fin n => (x i : ZMod (m : ℕ)))
            ((matrixMod L.pairingMatrix m).mulVec
              (fun j : Fin n => (d j : ZMod (m : ℕ)))) := by
            simp [m, matrixMod, dotProduct, Matrix.mulVec]
      _ = 0 := by rw [hFd]; simp [dotProduct]
  · intro d hd
    let m : ℕ+ := primePowModulus p k
    have hFd :
        (matrixMod L.pairingMatrix m).mulVec
          (fun j : Fin n => (d j : ZMod (m : ℕ))) = 0 := by
      simpa [pairingMatrixLocalDualCoordinateSubmodule, matrixModLinearMap, m]
        using hd
    calc
      ((L.quadForm d : ℤ) : ZMod (primePowModulus p k : ℕ)) =
          ((dotProduct d (L.pairingMatrix.mulVec d) : ℤ) :
            ZMod (primePowModulus p k : ℕ)) := by
            rw [L.quadForm_eq_dotProduct]
      _ =
          dotProduct (fun i : Fin n => (d i : ZMod (m : ℕ)))
            ((matrixMod L.pairingMatrix m).mulVec
              (fun j : Fin n => (d j : ZMod (m : ℕ)))) := by
            simp [m, matrixMod, dotProduct, Matrix.mulVec]
      _ = 0 := by rw [hFd]; simp [dotProduct]

lemma localDualPadicCoordinateSubmodule_isDualCoordinateDenominator
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] :
    IsDualCoordinateDenominator L p k
      (localDualPadicCoordinateSubmodule L p k) := by
  rw [localDualPadicCoordinateSubmodule_eq_pairingMatrixLocalDualCoordinateSubmodule]
  exact pairingMatrixLocalDualCoordinateSubmodule_isDualCoordinateDenominator (n := n) L p k

lemma IsDualCoordinateDenominator.admissible
    {L : PositiveDefiniteIntegralLattice n} {p k : ℕ} [Fact (Nat.Prime p)]
    {D : Submodule ℤ (Fin n → ℤ)}
    (hD : IsDualCoordinateDenominator L p k D) :
    IsDualQuotientAdmissible L p k D := by
  refine ⟨hD.1, ?_⟩
  intro x y hyx
  let d : Fin n → ℤ := y - x
  have hd : d ∈ D := hyx
  have hy : y = x + d := by
    ext i
    simp [d, sub_eq_add_neg]
  have hbilin : ((L.bilinearFormValue x d : ℤ) :
      ZMod (primePowModulus p k : ℕ)) = 0 := hD.2.1 x d hd
  have hquad : ((L.quadForm d : ℤ) :
      ZMod (primePowModulus p k : ℕ)) = 0 := hD.2.2 d hd
  calc
    (L.quadForm y : ZMod (primePowModulus p k : ℕ)) =
        (L.quadForm (x + d) : ZMod (primePowModulus p k : ℕ)) := by
          rw [hy]
    _ = (L.quadForm x + 2 * L.bilinearFormValue x d + L.quadForm d :
          ZMod (primePowModulus p k : ℕ)) := by
          have hcast := congrArg
            (fun z : ℤ => (z : ZMod (primePowModulus p k : ℕ)))
            (quadForm_add_eq_bilinearFormValue L x d)
          simpa only [Int.cast_add, Int.cast_mul, Int.cast_ofNat] using hcast
    _ = (L.quadForm x : ZMod (primePowModulus p k : ℕ)) := by
          simp [hbilin, hquad]

lemma pairingMatrixLocalDualCoordinateSubmodule_admissible
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] :
    IsDualQuotientAdmissible L p k
      (pairingMatrixLocalDualCoordinateSubmodule L p k) :=
  (pairingMatrixLocalDualCoordinateSubmodule_isDualCoordinateDenominator
    (n := n) L p k).admissible

lemma localDualPadicCoordinateSubmodule_admissible
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] :
    IsDualQuotientAdmissible L p k
      (localDualPadicCoordinateSubmodule L p k) :=
  (localDualPadicCoordinateSubmodule_isDualCoordinateDenominator
    (n := n) L p k).admissible

lemma localDualPadicDenominatorIntegralPreimage_admissible
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] :
    IsDualQuotientAdmissible L p k
      (localDualPadicDenominatorIntegralPreimage L p k) := by
  rw [localDualPadicDenominatorIntegralPreimage_eq_localDualPadicCoordinateSubmodule]
  exact localDualPadicCoordinateSubmodule_admissible (n := n) L p k

/-- The source associated-bilinear quadratic-depth condition makes its
integral-integral model quotient quadratic congruence well-defined. -/
lemma associatedBilinearDualPadicDenominatorIntegralPreimage_admissible
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : L.IsAssociatedBilinearHenselQuadraticDepth p k) :
    IsDualQuotientAdmissible L p k
      (associatedBilinearDualPadicDenominatorIntegralPreimage L p k) := by
  refine ⟨associatedBilinearDualPadicDenominatorIntegralPreimage_rank
    (n := n) L p k, ?_⟩
  intro x y hyx
  let d : Fin n → ℤ := y - x
  have hd : d ∈
      associatedBilinearDualPadicDenominatorIntegralPreimage L p k := hyx
  have hdPadic : integralVectorToPadic (n := n) p d ∈
      associatedBilinearDualPadicDenominator L p k := hd
  have hcrossDvd :
      ((p : ℤ_[p]) ^ k ∣ ((2 * L.bilinearFormValue x d : ℤ) : ℤ_[p])) := by
    have hx := (mem_associatedBilinearDualPadicDenominator_iff L p k
      (integralVectorToPadic (n := n) p d)).mp hdPadic x
    rw [L.polarGramMatrix_padic_eq_two_smul_pairingMatrix_padic p,
      Matrix.smul_mulVec, dotProduct_smul] at hx
    change ((p : ℤ_[p]) ^ k ∣
      (2 : ℤ_[p]) * dotProduct (integralVectorToPadic (n := n) p x)
        ((L.pairingMatrix_padic p).mulVec
          (integralVectorToPadic (n := n) p d))) at hx
    rw [padicBilinearFormValue_integral_right L p x d] at hx
    simpa only [Int.cast_mul, Int.cast_ofNat] using hx
  have hcross :
      ((2 * L.bilinearFormValue x d : ℤ) :
        ZMod (primePowModulus p k : ℕ)) = 0 :=
    (padicInt_primePow_dvd_intCast_iff_zmod_eq_zero p k _).mp hcrossDvd
  let dDual : Fin n → ℚ_[p] :=
    fun i => ((integralVectorToPadic (n := n) p d i : ℤ_[p]) : ℚ_[p]) /
      (p : ℚ_[p]) ^ k
  have hdDual : L.IsAssociatedBilinearDualPadicVector p dDual := by
    exact
      isAssociatedBilinearDualPadicVector_div_primePow_of_mem_associatedBilinearDualPadicDenominator
        L p k (integralVectorToPadic (n := n) p d) hdPadic
  obtain ⟨a, ha⟩ := hk dDual hdDual
  have hquadDvd :
      ((p : ℤ_[p]) ^ k ∣ ((L.quadForm d : ℤ) : ℤ_[p])) := by
    refine ⟨(p : ℤ_[p]) * a, ?_⟩
    apply PadicInt.ext
    have hquadCast :
        L.quadForm_padicField p
            (fun i => ((integralVectorToPadic (n := n) p d i : ℤ_[p]) : ℚ_[p])) =
          (L.quadForm d : ℚ_[p]) := by
      simp [quadForm_padicField, pairingMatrix_padicField, pairingMatrix_padic,
        integralVectorToPadic, quadForm_eq_dotProduct, dotProduct, Matrix.mulVec]
    change (L.quadForm d : ℚ_[p]) =
      (p : ℚ_[p]) ^ k * ((p : ℚ_[p]) * (a : ℚ_[p]))
    rw [← hquadCast]
    have hp : (p : ℚ_[p]) ^ k ≠ 0 :=
      pow_ne_zero _ (by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero)
    have hvec :
        (fun i => ((integralVectorToPadic (n := n) p d i : ℤ_[p]) : ℚ_[p])) =
          (p : ℚ_[p]) ^ k • dDual := by
      ext i
      dsimp [dDual]
      field_simp
    have hscale :
        L.quadForm_padicField p
            (fun i => ((integralVectorToPadic (n := n) p d i : ℤ_[p]) : ℚ_[p])) =
          (p : ℚ_[p]) ^ (2 * k) * L.quadForm_padicField p dDual := by
      rw [hvec, L.quadForm_padicField_smul]
      congr 1
      rw [show 2 * k = k * 2 by omega, pow_mul]
    rw [hscale]
    rw [show 2 * k = k + k by omega, pow_add]
    calc
      (p : ℚ_[p]) ^ k * (p : ℚ_[p]) ^ k *
          L.quadForm_padicField p dDual =
          (p : ℚ_[p]) ^ k *
            ((p : ℚ_[p]) ^ k * L.quadForm_padicField p dDual) := by ring
      _ = (p : ℚ_[p]) ^ k * ((p : ℚ_[p]) * (a : ℚ_[p])) := by
        rw [ha]
        rfl
  have hquad :
      ((L.quadForm d : ℤ) : ZMod (primePowModulus p k : ℕ)) = 0 :=
    (padicInt_primePow_dvd_intCast_iff_zmod_eq_zero p k _).mp hquadDvd
  have hy_eq : y = x + d := by
    dsimp [d]
    abel
  rw [hy_eq]
  have hadd := congrArg
    (fun z : ℤ => (z : ZMod (primePowModulus p k : ℕ)))
    (quadForm_add_eq_bilinearFormValue L x d)
  simpa [hcross, hquad] using hadd

/-- Source quadratic depth gives the extra prime needed in the adjacent
Hensel step: a vector in `p^k L_p#` has quadratic value divisible by
`p^(k+1)`. -/
lemma primePow_succ_dvd_quadForm_of_mem_associatedBilinearDualPadicDenominatorIntegralPreimage
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : L.IsAssociatedBilinearHenselQuadraticDepth p k)
    (d : Fin n → ℤ)
    (hd : d ∈
      associatedBilinearDualPadicDenominatorIntegralPreimage L p k) :
    ((p : ℤ) ^ (k + 1)) ∣ L.quadForm d := by
  have hdPadic : integralVectorToPadic (n := n) p d ∈
      associatedBilinearDualPadicDenominator L p k := hd
  let dDual : Fin n → ℚ_[p] :=
    fun i => ((integralVectorToPadic (n := n) p d i : ℤ_[p]) : ℚ_[p]) /
      (p : ℚ_[p]) ^ k
  have hdDual : L.IsAssociatedBilinearDualPadicVector p dDual :=
    isAssociatedBilinearDualPadicVector_div_primePow_of_mem_associatedBilinearDualPadicDenominator
      L p k (integralVectorToPadic (n := n) p d) hdPadic
  obtain ⟨a, ha⟩ := hk dDual hdDual
  have hquadDvd :
      ((p : ℤ_[p]) ^ (k + 1) ∣ ((L.quadForm d : ℤ) : ℤ_[p])) := by
    refine ⟨a, ?_⟩
    apply PadicInt.ext
    have hquadCast :
        L.quadForm_padicField p
            (fun i => ((integralVectorToPadic (n := n) p d i : ℤ_[p]) : ℚ_[p])) =
          (L.quadForm d : ℚ_[p]) := by
      simp [quadForm_padicField, pairingMatrix_padicField, pairingMatrix_padic,
        integralVectorToPadic, quadForm_eq_dotProduct, dotProduct, Matrix.mulVec]
    change (L.quadForm d : ℚ_[p]) =
      (p : ℚ_[p]) ^ (k + 1) * (a : ℚ_[p])
    rw [← hquadCast]
    have hp : (p : ℚ_[p]) ^ k ≠ 0 :=
      pow_ne_zero _ (by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero)
    have hvec :
        (fun i => ((integralVectorToPadic (n := n) p d i : ℤ_[p]) : ℚ_[p])) =
          (p : ℚ_[p]) ^ k • dDual := by
      ext i
      dsimp [dDual]
      field_simp
    rw [hvec, L.quadForm_padicField_smul]
    rw [pow_two]
    calc
      (p : ℚ_[p]) ^ k * (p : ℚ_[p]) ^ k *
          L.quadForm_padicField p dDual =
          (p : ℚ_[p]) ^ k *
            ((p : ℚ_[p]) ^ k * L.quadForm_padicField p dDual) := by ring
      _ = (p : ℚ_[p]) ^ k * ((p : ℚ_[p]) * (a : ℚ_[p])) := by
        rw [ha]
        rfl
      _ = (p : ℚ_[p]) ^ (k + 1) * (a : ℚ_[p]) := by
        rw [pow_succ]
        ring
  have hzero :
      ((L.quadForm d : ℤ) : ZMod (primePowModulus p (k + 1) : ℕ)) = 0 :=
    (padicInt_primePow_dvd_intCast_iff_zmod_eq_zero p (k + 1) _).mp hquadDvd
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hzero
  simpa [primePowModulus] using hzero

/-- Every associated-bilinear Gram coordinate of a source denominator vector
is divisible by the working prime power. -/
lemma primePow_dvd_polarGramMatrix_mulVec_of_mem_associatedBilinearDualPadicDenominatorIntegralPreimage
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (d : Fin n → ℤ)
    (hd : d ∈
      associatedBilinearDualPadicDenominatorIntegralPreimage L p k)
    (i : Fin n) :
    ((p : ℤ) ^ k) ∣ L.polarGramMatrix.mulVec d i := by
  have hdPadic : integralVectorToPadic (n := n) p d ∈
      associatedBilinearDualPadicDenominator L p k := hd
  have hdivPadic :=
    (mem_associatedBilinearDualPadicDenominator_iff L p k
      (integralVectorToPadic (n := n) p d)).mp hdPadic
      ((Pi.basisFun ℤ (Fin n)) i)
  have hdot :
      dotProduct
          (integralVectorToPadic (n := n) p
            ((Pi.basisFun ℤ (Fin n)) i))
          ((L.polarGramMatrix_padic p).mulVec
            (integralVectorToPadic (n := n) p d)) =
        (L.polarGramMatrix_padic p).mulVec
          (integralVectorToPadic (n := n) p d) i := by
    rw [dotProduct, Finset.sum_eq_single i]
    · simp [integralVectorToPadic, Pi.basisFun]
    · intro j _ hji
      simp [integralVectorToPadic, Pi.basisFun, hji]
    · simp
  rw [hdot] at hdivPadic
  have hdivPadic' :
      ((p : ℤ_[p]) ^ k ∣
        ((L.polarGramMatrix.mulVec d i : ℤ) : ℤ_[p])) := by
    convert hdivPadic using 1
    change ((∑ j, L.polarGramMatrix i j * d j : ℤ) : ℤ_[p]) =
      ∑ j, (L.polarGramMatrix i j : ℤ_[p]) * (d j : ℤ_[p])
    push_cast
    rfl
  have hzero :
      ((L.polarGramMatrix.mulVec d i : ℤ) :
        ZMod (primePowModulus p k : ℕ)) = 0 :=
    (padicInt_primePow_dvd_intCast_iff_zmod_eq_zero p k _).mp hdivPadic'
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hzero
  simpa [primePowModulus] using hzero

/-- The associated-bilinear source denominator is exactly the integral kernel
of multiplication by the Gram matrix modulo `p^k`. -/
lemma
    associatedBilinearDualPadicDenominatorIntegralPreimage_eq_polarGramMatrixModLinearMap_ker
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] :
    associatedBilinearDualPadicDenominatorIntegralPreimage L p k =
      LinearMap.ker (matrixModLinearMap (n := n) L.polarGramMatrix p k) := by
  ext d
  constructor
  · intro hd
    rw [LinearMap.mem_ker]
    ext i
    have hi :
        ((L.polarGramMatrix.mulVec d i : ℤ) :
          ZMod (primePowModulus p k : ℕ)) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      simpa [primePowModulus] using
        L.primePow_dvd_polarGramMatrix_mulVec_of_mem_associatedBilinearDualPadicDenominatorIntegralPreimage
          p k d hd i
    simpa [matrixModLinearMap, matrixMod, Matrix.mulVec, dotProduct] using hi
  · intro hd
    rw [LinearMap.mem_ker] at hd
    unfold associatedBilinearDualPadicDenominatorIntegralPreimage
    rw [mem_padicSubmoduleIntegralPreimage_iff,
      mem_associatedBilinearDualPadicDenominator_iff]
    intro x
    have hcoord : ∀ i : Fin n,
        ((p : ℤ_[p]) ^ k ∣
          (L.polarGramMatrix_padic p).mulVec
            (integralVectorToPadic (n := n) p d) i) := by
      intro i
      have hi := congrFun hd i
      have hzero :
          ((L.polarGramMatrix.mulVec d i : ℤ) :
            ZMod (primePowModulus p k : ℕ)) = 0 := by
        simpa [matrixModLinearMap, matrixMod, Matrix.mulVec, dotProduct] using hi
      have hdiv :
          ((p : ℤ_[p]) ^ k ∣
            ((L.polarGramMatrix.mulVec d i : ℤ) : ℤ_[p])) :=
        (padicInt_primePow_dvd_intCast_iff_zmod_eq_zero p k _).mpr hzero
      convert hdiv using 1
      change
        (∑ j, (L.polarGramMatrix i j : ℤ_[p]) * (d j : ℤ_[p])) =
          ((∑ j, L.polarGramMatrix i j * d j : ℤ) : ℤ_[p])
      push_cast
      rfl
    rw [dotProduct]
    exact Finset.dvd_sum fun i _ =>
      dvd_mul_of_dvd_right (hcoord i)
        (integralVectorToPadic (n := n) p x i)

/-- Gram multiplication modulo `p^k`, descended to coordinate classes modulo
`p^k ℤ^n`. -/
def associatedBilinearGramModQuotientLinearMap
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] :
    localDualQuotientTarget
        (primePowCoordinateSubmodule (n := n) p k) →ₗ[ℤ]
      (Fin n → ZMod (primePowModulus p k : ℕ)) :=
  (primePowCoordinateSubmodule (n := n) p k).liftQ
    (matrixModLinearMap (n := n) L.polarGramMatrix p k) (by
      intro d hd
      rw [←
        L.associatedBilinearDualPadicDenominatorIntegralPreimage_eq_polarGramMatrixModLinearMap_ker
          p k]
      exact
        L.primePowCoordinateSubmodule_le_associatedBilinearDualPadicDenominatorIntegralPreimage
          p k hd)

@[simp] lemma associatedBilinearGramModQuotientLinearMap_mkQ
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (d : Fin n → ℤ) :
    associatedBilinearGramModQuotientLinearMap L p k
        ((primePowCoordinateSubmodule (n := n) p k).mkQ d) =
      matrixModLinearMap (n := n) L.polarGramMatrix p k d := rfl

/-- The extra associated-bilinear source-denominator classes are exactly the
kernel of reduced Gram multiplication on coordinate classes modulo `p^k`. -/
noncomputable def
    associatedBilinearDualPadicDenominatorFiberEquivGramModQuotientLinearMapKer
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] :
    (associatedBilinearDualPadicDenominatorIntegralPreimage L p k ⧸
      (primePowCoordinateSubmodule (n := n) p k).comap
        (associatedBilinearDualPadicDenominatorIntegralPreimage L p k).subtype) ≃ₗ[ℤ]
      LinearMap.ker (associatedBilinearGramModQuotientLinearMap L p k) := by
  let P := primePowCoordinateSubmodule (n := n) p k
  let E := associatedBilinearDualPadicDenominatorIntegralPreimage L p k
  let f : E →ₗ[ℤ]
      LinearMap.ker (associatedBilinearGramModQuotientLinearMap L p k) :=
    { toFun := fun d => ⟨P.mkQ d.1, by
          rw [LinearMap.mem_ker]
          change matrixModLinearMap (n := n) L.polarGramMatrix p k d.1 = 0
          apply LinearMap.mem_ker.mp
          rw [←
            L.associatedBilinearDualPadicDenominatorIntegralPreimage_eq_polarGramMatrixModLinearMap_ker
              p k]
          exact d.2⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        simp
      map_smul' := by
        intro a x
        apply Subtype.ext
        change P.mkQ (a • x.1) = a • P.mkQ x.1
        exact map_smul (P.mkQ) a x.1 }
  let fQ : (E ⧸ P.comap E.subtype) →ₗ[ℤ]
      LinearMap.ker (associatedBilinearGramModQuotientLinearMap L p k) :=
    (P.comap E.subtype).liftQ f (by
      intro d hd
      apply Subtype.ext
      exact (Submodule.Quotient.mk_eq_zero P).mpr hd)
  apply LinearEquiv.ofBijective fQ
  constructor
  · intro q r hqr
    induction q using Quotient.inductionOn with
    | h x =>
      induction r using Quotient.inductionOn with
      | h y =>
        change (Submodule.Quotient.mk x :
            E ⧸ P.comap E.subtype) = Submodule.Quotient.mk y
        rw [Submodule.Quotient.eq]
        have hval := congrArg Subtype.val hqr
        change (P.mkQ x.1 : (Fin n → ℤ) ⧸ P) = P.mkQ y.1 at hval
        change (Submodule.Quotient.mk x.1 :
            (Fin n → ℤ) ⧸ P) = Submodule.Quotient.mk y.1 at hval
        rw [Submodule.Quotient.eq] at hval
        exact hval
  · intro q
    let d : Fin n → ℤ := Quotient.out q.1
    have hdE : d ∈ E := by
      change d ∈
        associatedBilinearDualPadicDenominatorIntegralPreimage L p k
      rw [
        L.associatedBilinearDualPadicDenominatorIntegralPreimage_eq_polarGramMatrixModLinearMap_ker
          p k,
        LinearMap.mem_ker]
      calc
        matrixModLinearMap (n := n) L.polarGramMatrix p k d =
            associatedBilinearGramModQuotientLinearMap L p k (P.mkQ d) := rfl
        _ = associatedBilinearGramModQuotientLinearMap L p k q.1 := by
          exact congrArg (associatedBilinearGramModQuotientLinearMap L p k)
            (Submodule.Quotient.mk_out q.1)
        _ = 0 := LinearMap.mem_ker.mp q.2
    refine ⟨(P.comap E.subtype).mkQ ⟨d, hdE⟩, ?_⟩
    apply Subtype.ext
    exact Submodule.Quotient.mk_out q.1

/-- If the working depth bounds the Gram discriminant valuation, the reduced
Gram kernel has cardinality `p` to that valuation. This is the one-column
nonunit denominator-fiber calculation. -/
lemma
    associatedBilinearGramModQuotientLinearMap_ker_natCard_eq_prime_pow_polarDeterminant_val_of_le
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hdisc : padicValInt p L.polarDeterminant ≤ k) :
    Nat.card
        (LinearMap.ker (associatedBilinearGramModQuotientLinearMap L p k)) =
      p ^ padicValInt p L.polarDeterminant := by
  classical
  let E :=
    associatedBilinearDualPadicDenominatorIntegralPreimage L p k
  have hdet : L.polarGramMatrix.det ≠ 0 := by
    simpa [polarDeterminant] using (ne_of_gt L.polarDeterminant_pos)
  rcases exists_integral_diagonalization_of_det_ne_zero
      (n := n) L.polarGramMatrix hdet with
    ⟨P, Q, d, hP, hQ, hdiag⟩
  have hPdet : IsUnit P.det := by
    rwa [Matrix.isUnit_iff_isUnit_det] at hP
  have hQdet : IsUnit Q.det := by
    rwa [Matrix.isUnit_iff_isUnit_det] at hQ
  have hdiagdet_ne : (Matrix.diagonal d).det ≠ 0 := by
    rw [← hdiag]
    simpa [Matrix.det_mul, mul_assoc] using
      mul_ne_zero (mul_ne_zero hPdet.ne_zero hdet) hQdet.ne_zero
  have hprod_ne : (∏ i : Fin n, d i) ≠ 0 := by
    simpa [Matrix.det_diagonal] using hdiagdet_ne
  have hd : ∀ i : Fin n, d i ≠ 0 := by
    intro i hi
    exact hprod_ne
      (Finset.prod_eq_zero_iff.mpr ⟨i, Finset.mem_univ i, hi⟩)
  have hsum :
      ∑ i : Fin n, padicValInt p (d i) = padicValInt p L.polarDeterminant := by
    rw [← padicValInt_det_eq_sum_diagonal_of_left_right_mul_eq_diagonal
      (n := n) L.polarGramMatrix P Q p d hP hQ hdiag hd]
    rfl
  have hdval : ∀ i : Fin n, padicValInt p (d i) ≤ k := by
    intro i
    have hi :
        padicValInt p (d i) ≤ ∑ j : Fin n, padicValInt p (d j) :=
      Finset.single_le_sum
        (fun j _ => Nat.zero_le (padicValInt p (d j)))
        (Finset.mem_univ i)
    rw [hsum] at hi
    exact hi.trans hdisc
  let v : Fin n → ℕ := fun i => truncatedPadicValInt p k (d i)
  have hv : ∀ i : Fin n, v i ≤ k := fun i =>
    truncatedPadicValInt_le p k (d i)
  have hfac : ∀ i : Fin n,
      ∃ u : ℤ,
        (∀ _hv : v i < k,
          IsUnit (((u : ℤ) : ZMod (primePowModulus p k : ℕ)))) ∧
        d i = u * (p ^ v i : ℤ) := fun i =>
    exists_unit_factor_truncatedPadicValInt p k (d i)
  choose u hu using hfac
  have hunit : ∀ i : Fin n, v i < k →
      IsUnit ((((u i) : ℤ) : ZMod (primePowModulus p k : ℕ))) := by
    intro i
    exact (hu i).1
  have hdiag' :
      P * L.polarGramMatrix * Q =
        Matrix.diagonal (fun i : Fin n => u i * (p ^ v i : ℤ)) := by
    rw [hdiag]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [fun i => (hu i).2]
    · simp [Matrix.diagonal_apply_ne _ hij]
  have hvsum :
      ∑ i : Fin n, v i = padicValInt p L.polarDeterminant := by
    calc
      ∑ i : Fin n, v i = padicValInt p L.polarGramMatrix.det :=
        sum_truncatedPadicValInt_eq_padicValInt_det_of_left_right_mul_eq_diagonal
          (n := n) L.polarGramMatrix P Q p k d hP hQ hdiag hdval hd
      _ = padicValInt p L.polarDeterminant := rfl
  let w := ∑ i : Fin n, (k - v i)
  have hsum_compl : w + padicValInt p L.polarDeterminant = n * k := by
    rw [← hvsum]
    calc
      w + ∑ i : Fin n, v i =
          ∑ i : Fin n, ((k - v i) + v i) := by
            simpa [w] using
              (Finset.sum_add_distrib (s := Finset.univ)
                (f := fun i : Fin n => k - v i)
                (g := fun i : Fin n => v i)).symm
      _ = ∑ _i : Fin n, k := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            exact Nat.sub_add_cancel (hv i)
      _ = n * k := by simp [Fintype.card_fin]
  have hw : w ≤ n * k := by omega
  have hcard :
      Nat.card ((Fin n → ℤ) ⧸ E) = p ^ w := by
    rw [show E =
        LinearMap.ker
          (matrixModLinearMap (n := n) L.polarGramMatrix p k) by
      exact
        L.associatedBilinearDualPadicDenominatorIntegralPreimage_eq_polarGramMatrixModLinearMap_ker
          p k]
    simpa [w] using
      matrixModLinearMap_ker_quotient_card_of_left_right_mul_eq_diagonal_units_prime_pows_of_lt
        (n := n) L.polarGramMatrix P Q p k u v hv hunit hP hQ hdiag'
  have hsub :=
    primePowCoordinateSubmodule_subquotient_card_eq_prime_pow_of_quotient_card
      (n := n) p k E
      (L.primePowCoordinateSubmodule_le_associatedBilinearDualPadicDenominatorIntegralPreimage
        p k)
      w hw hcard
  have hdiff : n * k - w = padicValInt p L.polarDeterminant := by omega
  have hsub' :
      Nat.card
          (associatedBilinearDualPadicDenominatorIntegralPreimage L p k ⧸
            (primePowCoordinateSubmodule (n := n) p k).comap
              (associatedBilinearDualPadicDenominatorIntegralPreimage L p k).subtype) =
        p ^ padicValInt p L.polarDeterminant := by
    simpa [E, hdiff] using hsub
  calc
    Nat.card
        (LinearMap.ker (associatedBilinearGramModQuotientLinearMap L p k)) =
        Nat.card
          (associatedBilinearDualPadicDenominatorIntegralPreimage L p k ⧸
            (primePowCoordinateSubmodule (n := n) p k).comap
              (associatedBilinearDualPadicDenominatorIntegralPreimage L p k).subtype) :=
      Nat.card_congr
        (associatedBilinearDualPadicDenominatorFiberEquivGramModQuotientLinearMapKer
          L p k).symm.toEquiv
    _ = p ^ padicValInt p L.polarDeterminant := hsub'

/-- If the Gram matrix is invertible modulo `p^k`, the associated-bilinear
source denominator has no integral-coordinate classes beyond `p^k ℤ^n`. -/
lemma
    associatedBilinearDualPadicDenominatorIntegralPreimage_le_primePowCoordinateSubmodule_of_polarGramMatrix_zmod_isUnit
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hG : IsUnit (matrixMod L.polarGramMatrix (primePowModulus p k))) :
    associatedBilinearDualPadicDenominatorIntegralPreimage L p k ≤
      primePowCoordinateSubmodule (n := n) p k := by
  intro d hd
  rw [mem_primePowCoordinateSubmodule_iff_coordinate_zmod_eq_zero]
  let m : ℕ+ := primePowModulus p k
  let G : Matrix (Fin n) (Fin n) (ZMod (m : ℕ)) :=
    matrixMod L.polarGramMatrix m
  let v : Fin n → ZMod (m : ℕ) := fun i => (d i : ZMod (m : ℕ))
  have hGd : G.mulVec v = 0 := by
    ext i
    have hi :
        ((L.polarGramMatrix.mulVec d i : ℤ) : ZMod (m : ℕ)) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      simpa [m, primePowModulus] using
        L.primePow_dvd_polarGramMatrix_mulVec_of_mem_associatedBilinearDualPadicDenominatorIntegralPreimage
          p k d hd i
    simpa [G, v, m, matrixMod, Matrix.mulVec, dotProduct] using hi
  have hG_unit : IsUnit G := by
    simpa [G, m] using hG
  have hG_det : IsUnit G.det := by
    rwa [Matrix.isUnit_iff_isUnit_det] at hG_unit
  have hleft : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul G hG_det
  have hv_zero : v = 0 := by
    calc
      v = (1 : Matrix (Fin n) (Fin n) (ZMod (m : ℕ))).mulVec v := by simp
      _ = (G⁻¹ * G).mulVec v := by rw [hleft]
      _ = G⁻¹.mulVec (G.mulVec v) := by rw [Matrix.mulVec_mulVec]
      _ = 0 := by rw [hGd]; simp
  intro i
  exact congr_fun hv_zero i

/-- Basis-image families whose induced map to the coordinate local-dual
quotient satisfies Schulze--Pillot's quadratic congruence condition. -/
noncomputable def localDualQuotientSolutionFamilies
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (D : Submodule ℤ (Fin n → ℤ)) (hD_rank : Module.finrank ℤ D = n) :
    Finset (Fin n → localDualQuotientTarget D) := by
  classical
  have hD_rank' : Module.finrank ℤ D = Module.finrank ℤ (Fin n → ℤ) := by
    simpa [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using hD_rank
  letI : Finite (localDualQuotientTarget D) :=
    Submodule.finiteQuotientOfFreeOfRankEq (M := Fin n → ℤ) D hD_rank'
  letI : Fintype (localDualQuotientTarget D) :=
    Fintype.ofFinite (localDualQuotientTarget D)
  exact Finset.univ.filter fun Y =>
    ∀ x y : Fin n → ℤ,
      quotientBasisFamilyMap D Y x = D.mkQ y →
        (L.quadForm y : ZMod (primePowModulus p k : ℕ)) =
          (L.quadForm x : ZMod (primePowModulus p k : ℕ))

/-- The finite Schulze--Pillot coordinate local-dual quotient count attached to
a full-rank coordinate quotient model. -/
noncomputable def coordinateLocalDualQuotientCount
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (D : Submodule ℤ (Fin n → ℤ)) (hD_rank : Module.finrank ℤ D = n) : ℕ :=
  (localDualQuotientSolutionFamilies L p k D hD_rank).card

/-- Schulze--Pillot's finite local-dual quotient count in the current
coordinate model, using the `p`-adic denominator
`p^k L_p# ∩ L` through its integral coordinate integral model. -/
noncomputable def localDualQuotientCount
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] : ℕ :=
  coordinateLocalDualQuotientCount L p k
    (localDualPadicDenominatorIntegralPreimage L p k)
    (localDualPadicDenominatorIntegralPreimage_rank (n := n) L p k)

/-- Schulze--Pillot's source-normalized count, using the dual for the
associated bilinear form `2F`. -/
noncomputable def associatedBilinearDualQuotientCount
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] : ℕ :=
  coordinateLocalDualQuotientCount L p k
    (associatedBilinearDualPadicDenominatorIntegralPreimage L p k)
    (associatedBilinearDualPadicDenominatorIntegralPreimage_rank (n := n) L p k)

/-- The exponent `k n(n-1)/2` in Schulze--Pillot's fixed-`k` finite local
density normalization. -/
def localDensityDenominatorExponent (n k : ℕ) : ℕ :=
  k * (n * (n - 1) / 2)

/-- The determinant-normalized local-dual quotient count whose independence
of a sufficiently deep exponent is supplied by quantitative Hensel lifting. -/
noncomputable def localDualQuotientNormalizedCount
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] : ℚ :=
  ((p : ℚ) ^ localDensityDenominatorExponent n k)⁻¹ *
    (localDualQuotientCount L p k : ℚ)

/-- The classical raw Gram-matrix solution-count density
`N_A(p^k) / p^(k n(n-1)/2)` used for odd-prime computational comparisons. -/
noncomputable def classicalGramLocalDensity
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] : ℚ :=
  ((p : ℚ) ^ localDensityDenominatorExponent n k)⁻¹ *
    (gramCongruenceSolutionCount L p k : ℚ)

/-- The finite rational value of `|2|_p^{-n}`.  This is `2^n` at the dyadic
prime and `1` at odd primes. -/
def twoPadicNormInvPow (p n : ℕ) : ℚ :=
  if p = 2 then (2 : ℚ) ^ n else 1

/-- Conversion from the current half-polar `F`-dual quotient count to
Schulze--Pillot's associated-bilinear `2F`-dual count.  The two counts agree
away from `2`; at a valid dyadic Hensel depth the current count is larger by
`2^(n*n)`.  The separate factor `twoPadicNormInvPow` comes from
the even diagonal entries in the quadratic congruence and is not part of this
dual-lattice conversion. -/
def dualCountNormalizationFactor (p n : ℕ) : ℚ :=
  if p = 2 then ((2 : ℚ) ^ (n * n))⁻¹ else 1

/-- The Gram-determinant p-adic norm factor
`|det_b(L_p)|_p^((1 - n) / 2)` in Schulze--Pillot's fixed-`k` local density.

Here `det_b` is the determinant of the bilinear Gram matrix, formalized as
`PositiveDefiniteIntegralLattice.polarDeterminant`.  The half-integer exponent is represented with
`Real.rpow`; this keeps the square-root convention explicit at the interface
without imposing a rational-valued parity split yet. -/
noncomputable def gramDetPadicNormFactor
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] : ℝ :=
  ‖(L.polarDeterminant : ℤ_[p])‖ ^ (((1 : ℝ) - (n : ℝ)) / 2)

/-- The same Gram-determinant factor, written using a visible
`p`-adic valuation parameter `v` with `|polarDeterminant(L)|_p = p^{-v}`. -/
noncomputable def gramDetPadicValuationFactor
    (p n v : ℕ) : ℝ :=
  (p : ℝ) ^ ((v : ℝ) * (((n : ℝ) - 1) / 2))

/-- The complementary non-unit quotient-count correction expected in the
odd-prime comparison:
`A(L_p, L_p mod p^k L_p#) / p^(k n(n-1)/2)` should be the raw classical
matrix density times `p^{-n v}` when `|polarDeterminant(L)|_p = p^{-v}`. -/
noncomputable def localDualQuotientValuationCorrectionFactor
    (p n v : ℕ) : ℝ :=
  (p : ℝ) ^ (-((n : ℝ) * (v : ℝ)))

/-- The fixed-`k` Schulze--Pillot finite local-density factor attached to an
explicit admissible coordinate quotient denominator, before the Gram-determinant
factor is added. -/
noncomputable def localDualQuotientFixedKDensityFactor
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (D : Submodule ℤ (Fin n → ℤ))
    (hD : IsDualQuotientAdmissible L p k D) : ℚ :=
  (1 / 2 : ℚ) * twoPadicNormInvPow p n *
    ((p : ℚ) ^ localDensityDenominatorExponent n k)⁻¹ *
    (coordinateLocalDualQuotientCount L p k D hD.1 : ℚ)

/-- The fixed-`k` Schulze--Pillot finite local-density factor in the current
coordinate model, before the Gram-determinant factor is added.  The visible
normalization factor converts the current `F`-dual count to the source
associated-bilinear `2F`-dual normalization at `2`. -/
noncomputable def fixedKDensityFactor
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] : ℚ :=
  dualCountNormalizationFactor p n *
    localDualQuotientFixedKDensityFactor L p k
      (localDualPadicDenominatorIntegralPreimage L p k)
      (localDualPadicDenominatorIntegralPreimage_admissible (n := n) L p k)

/-- The fixed-`k` Schulze--Pillot local-density factor in the current
coordinate model, including the Gram-determinant p-adic norm factor. -/
noncomputable def fixedKDensityWithGramDetFactor
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] : ℝ :=
  (fixedKDensityFactor L p k : ℝ) *
    gramDetPadicNormFactor L p

/-- The coordinate admissibility hypotheses on the exponent `k` in the first
fixed-`k` Schulze--Pillot local-density interface.

The positivity field records the source convention `k ≥ 1`.  The denominator
field records, in the current coordinate model, that the integral integral model of
`p^k L_p# ∩ L` has full rank and makes the quadratic form well-defined modulo
`p^k` on the quotient.  The stronger exact local lattice and quadratic depth
conditions needed for quantitative Hensel lifting are recorded separately by
`IsLocalDensityHenselExponent`. -/
structure IsLocalDensityAdmissibleExponent
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] : Prop where
  one_le : 1 ≤ k
  denominator :
    IsDualCoordinateDenominator L p k
      (localDualPadicDenominatorIntegralPreimage L p k)

lemma isLocalDensityAdmissibleExponent_of_one_le
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] (hk : 1 ≤ k) :
    IsLocalDensityAdmissibleExponent L p k where
  one_le := hk
  denominator := by
    rw [localDualPadicDenominatorIntegralPreimage_eq_localDualPadicCoordinateSubmodule]
    exact localDualPadicCoordinateSubmodule_isDualCoordinateDenominator (n := n) L p k

/-- The local depth conditions used by the current quotient coordinates and
the source-normalized quantitative Hensel theorem.  The first two depth fields
refer to the half-polar `F`-dual used by the concrete count.  The final field
is Schulze--Pillot's actual quadratic-depth condition on the associated-
bilinear `2F`-dual. -/
structure IsLocalDensityHenselExponent
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] : Prop where
  admissible : IsLocalDensityAdmissibleExponent L p k
  lattice_depth : L.IsHenselLatticeDepth p k
  quadratic_depth : L.IsHenselQuadraticDepth p k
  associated_bilinear_quadratic_depth :
    L.IsAssociatedBilinearHenselQuadraticDepth p k

lemma IsHenselLatticeDepth.succ
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (h : L.IsHenselLatticeDepth p k) :
    L.IsHenselLatticeDepth p (k + 1) := by
  intro y hy i
  rw [pow_succ]
  simpa [mul_assoc, mul_comm, mul_left_comm] using
    (PadicInt.subring p).mul_mem (p : ℤ_[p]).property (h y hy i)

lemma IsHenselQuadraticDepth.succ
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (h : L.IsHenselQuadraticDepth p k) :
    L.IsHenselQuadraticDepth p (k + 1) := by
  intro y hy
  obtain ⟨a, ha⟩ := h y hy
  refine ⟨(p : ℤ_[p]) * a, ?_⟩
  change (p : ℚ_[p]) ^ (k + 1) * L.quadForm_padicField p y =
    (p : ℚ_[p]) * ((p : ℚ_[p]) * (a : ℚ_[p]))
  rw [pow_succ]
  calc
    (p : ℚ_[p]) ^ k * (p : ℚ_[p]) * L.quadForm_padicField p y =
        (p : ℚ_[p]) *
          ((p : ℚ_[p]) ^ k * L.quadForm_padicField p y) := by ring
    _ = (p : ℚ_[p]) * ((p : ℚ_[p]) * (a : ℚ_[p])) := by
      rw [ha]
      rfl

lemma IsAssociatedBilinearHenselQuadraticDepth.succ
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (h : L.IsAssociatedBilinearHenselQuadraticDepth p k) :
    L.IsAssociatedBilinearHenselQuadraticDepth p (k + 1) := by
  intro y hy
  obtain ⟨a, ha⟩ := h y hy
  refine ⟨(p : ℤ_[p]) * a, ?_⟩
  change (p : ℚ_[p]) ^ (k + 1) * L.quadForm_padicField p y =
    (p : ℚ_[p]) * ((p : ℚ_[p]) * (a : ℚ_[p]))
  rw [pow_succ]
  calc
    (p : ℚ_[p]) ^ k * (p : ℚ_[p]) * L.quadForm_padicField p y =
        (p : ℚ_[p]) *
          ((p : ℚ_[p]) ^ k * L.quadForm_padicField p y) := by ring
    _ = (p : ℚ_[p]) * ((p : ℚ_[p]) * (a : ℚ_[p])) := by
      rw [ha]
      rfl

lemma IsAssociatedBilinearHenselQuadraticDepth.add
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (h : L.IsAssociatedBilinearHenselQuadraticDepth p k) :
    ∀ r : ℕ, L.IsAssociatedBilinearHenselQuadraticDepth p (k + r)
  | 0 => by simpa using h
  | r + 1 => by
      rw [Nat.add_succ]
      exact (h.add L p k r).succ L p (k + r)

/-- At depth `k+r`, the source denominator is contained in
`p^(r+1) Z_p^n` once source quadratic depth holds at `k`. -/
lemma
    associatedBilinearDualPadicDenominator_add_coordinate_primePow_dvd
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : L.IsAssociatedBilinearHenselQuadraticDepth p k) :
    ∀ (r : ℕ) (d : Fin n → ℤ_[p]),
      d ∈ associatedBilinearDualPadicDenominator L p (k + r) →
      ∀ i : Fin n, (p : ℤ_[p]) ^ (r + 1) ∣ d i
  | 0, d, hd => by
      intro i
      obtain ⟨a, ha⟩ :=
        hk.coordinate_prime_mul L p k
          (fun j => (d j : ℚ_[p]) / (p : ℚ_[p]) ^ k)
          (isAssociatedBilinearDualPadicVector_div_primePow_of_mem_associatedBilinearDualPadicDenominator
            L p k d hd)
          i
      refine ⟨a, ?_⟩
      apply PadicInt.ext
      change (d i : ℚ_[p]) = (p : ℚ_[p]) ^ (0 + 1) * (a : ℚ_[p])
      have hp : (p : ℚ_[p]) ^ k ≠ 0 :=
        pow_ne_zero _ (by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero)
      calc
        (d i : ℚ_[p]) =
            (p : ℚ_[p]) ^ k * ((d i : ℚ_[p]) / (p : ℚ_[p]) ^ k) := by
              field_simp
        _ = (((p : ℤ_[p]) * a : ℤ_[p]) : ℚ_[p]) := ha
        _ = (p : ℚ_[p]) ^ (0 + 1) * (a : ℚ_[p]) := by
              push_cast
              ring
  | r + 1, d, hd => by
      intro i
      have hdepth := (hk.add L p k r).latticeDepth L p (k + r)
      obtain ⟨e, he, hpe⟩ :=
        exists_prime_smul_eq_of_mem_associatedBilinearDualPadicDenominator_succ
          L p (k + r) hdepth d (by simpa [Nat.add_assoc] using hd)
      obtain ⟨a, ha⟩ :=
        associatedBilinearDualPadicDenominator_add_coordinate_primePow_dvd
          L p k hk r e he i
      refine ⟨a, ?_⟩
      have hi := congr_fun hpe i
      simp only [Pi.smul_apply, smul_eq_mul] at hi
      rw [← hi, ha]
      ring

/-- Integral-integral model version of the cofinal source-denominator bound. -/
lemma
    associatedBilinearDualPadicDenominatorIntegralPreimage_add_le_primePowCoordinateSubmodule
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : L.IsAssociatedBilinearHenselQuadraticDepth p k)
    (r : ℕ) :
    associatedBilinearDualPadicDenominatorIntegralPreimage L p (k + r) ≤
      primePowCoordinateSubmodule (n := n) p (r + 1) := by
  intro d hd
  rw [mem_primePowCoordinateSubmodule_iff_coordinate_zmod_eq_zero]
  intro i
  exact
    (padicInt_primePow_dvd_intCast_iff_zmod_eq_zero p (r + 1) (d i)).mp
      (associatedBilinearDualPadicDenominator_add_coordinate_primePow_dvd
        L p k hk r (integralVectorToPadic (n := n) p d) hd i)

lemma IsLocalDensityHenselExponent.succ
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : IsLocalDensityHenselExponent L p k) :
    IsLocalDensityHenselExponent L p (k + 1) where
  admissible :=
    isLocalDensityAdmissibleExponent_of_one_le L p (k + 1) (by omega)
  lattice_depth := hk.lattice_depth.succ L p k
  quadratic_depth := hk.quadratic_depth.succ L p k
  associated_bilinear_quadratic_depth :=
    hk.associated_bilinear_quadratic_depth.succ L p k

lemma IsLocalDensityHenselExponent.add
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : IsLocalDensityHenselExponent L p k) :
    ∀ r : ℕ, IsLocalDensityHenselExponent L p (k + r)
  | 0 => by simpa using hk
  | r + 1 => by
      rw [Nat.add_succ]
      exact (hk.add L p k r).succ L p (k + r)

lemma isLocalDensityHenselExponent_of_polarDeterminant_val_lt_of_ne_two
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hdisc_lt : padicValInt p L.polarDeterminant < k) (hp_two : p ≠ 2) :
    IsLocalDensityHenselExponent L p k where
  admissible :=
    isLocalDensityAdmissibleExponent_of_one_le L p k (by omega)
  lattice_depth := L.isHenselLatticeDepth_of_pairingDeterminant_val_lt p k
    (lt_of_le_of_lt (L.padicValInt_pairingDeterminant_le_polarDeterminant p) hdisc_lt)
  quadratic_depth := L.isHenselQuadraticDepth_of_pairingDeterminant_val_lt p k
    (lt_of_le_of_lt (L.padicValInt_pairingDeterminant_le_polarDeterminant p) hdisc_lt)
  associated_bilinear_quadratic_depth :=
    (L.isAssociatedBilinearHenselQuadraticDepth_iff_of_ne_two
      p k hp_two).2
      (L.isHenselQuadraticDepth_of_pairingDeterminant_val_lt p k
        (lt_of_le_of_lt (L.padicValInt_pairingDeterminant_le_polarDeterminant p) hdisc_lt))

lemma isLocalDensityHenselExponent_of_polarDeterminant_val_add_two_lt
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hdisc_lt : padicValInt p L.polarDeterminant + 2 < k) :
    IsLocalDensityHenselExponent L p k := by
  by_cases hp_two : p = 2
  · subst p
    let r := k - 2
    have hr : r + 2 = k := by
      dsimp [r]
      omega
    have hdisc_r : padicValInt 2 L.polarDeterminant < r := by
      dsimp [r]
      omega
    have hlattice := L.isHenselLatticeDepth_of_pairingDeterminant_val_lt 2 r
      (lt_of_le_of_lt (L.padicValInt_pairingDeterminant_le_polarDeterminant 2) hdisc_r)
    have hquadratic := L.isHenselQuadraticDepth_of_pairingDeterminant_val_lt 2 r
      (lt_of_le_of_lt (L.padicValInt_pairingDeterminant_le_polarDeterminant 2) hdisc_r)
    rw [← hr]
    exact
      { admissible := isLocalDensityAdmissibleExponent_of_one_le L 2 (r + 2) (by omega)
        lattice_depth := (hlattice.succ L 2 r).succ L 2 (r + 1)
        quadratic_depth := (hquadratic.succ L 2 r).succ L 2 (r + 1)
        associated_bilinear_quadratic_depth :=
          hquadratic.associatedBilinear_add_two_dyadic L r }
  · exact isLocalDensityHenselExponent_of_polarDeterminant_val_lt_of_ne_two
      (n := n) L p k (by omega) hp_two

/-- A conservative canonical determinant-depth exponent for quantitative
Hensel lifting.  The two extra powers beyond the half-polar determinant bound
ensure the associated-bilinear quadratic-depth condition also at `p = 2`. -/
def localDensityHenselExponent
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] : ℕ :=
  padicValInt p L.polarDeterminant + 3

lemma isLocalDensityHenselExponent_preferred
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    IsLocalDensityHenselExponent L p (localDensityHenselExponent L p) :=
  isLocalDensityHenselExponent_of_polarDeterminant_val_add_two_lt
    (n := n) L p (localDensityHenselExponent L p) (by
      simp [localDensityHenselExponent])

/-- The strengthened fixed-`k` exponent interface used for the odd-prime
classical matrix-count comparison.  It keeps Schulze--Pillot's admissibility
hypotheses and records the extra large-`k` range needed by the Smith-normal
form numerator comparison. -/
structure IsLocalDensityClassicalComparisonExponent
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] : Prop where
  hensel : IsLocalDensityHenselExponent L p k
  disc_val_lt : padicValInt p L.polarDeterminant < k

lemma isLocalDensityClassicalComparisonExponent_of_polarDeterminant_val_lt
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hdisc_lt : padicValInt p L.polarDeterminant < k) (hp_two : p ≠ 2) :
    IsLocalDensityClassicalComparisonExponent L p k where
  hensel := isLocalDensityHenselExponent_of_polarDeterminant_val_lt_of_ne_two
    (n := n) L p k hdisc_lt hp_two
  disc_val_lt := hdisc_lt

/-- First fixed-`k` version of Schulze--Pillot's local density
`α_p^{SP}(L,k)`, with coordinate admissibility of `k` explicit.

The next major theorem should show that this value is independent of the choice
of admissible exponent. -/
noncomputable def normalizedLocalDensityAtExponent
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (_hk : IsLocalDensityAdmissibleExponent L p k) : ℝ :=
  fixedKDensityWithGramDetFactor L p k

/-- Schulze--Pillot's `k`-independent local density in the current
normalization.  It is defined at the canonical determinant-depth exponent;
`normalizedLocalDensity_eq_fixedK` identifies it with every fixed-`k` value in the
quantitative Hensel range. -/
noncomputable def normalizedLocalDensity
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] : ℝ :=
  normalizedLocalDensityAtExponent L p (localDensityHenselExponent L p)
    (isLocalDensityHenselExponent_preferred (n := n) L p).admissible

end PositiveDefiniteIntegralLattice

end
