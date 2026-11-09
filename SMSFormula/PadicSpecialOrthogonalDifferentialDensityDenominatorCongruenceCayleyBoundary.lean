import SMSFormula.PadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceFiberTorsor
import SMSFormula.PadicSpecialOrthogonalDifferentialDensityCongruenceSelectedDepthTranslation

/-!
# Inverse-Cayley domain for the denominator-congruence subgroup

At the selected density depth, the form-determinant valuation is strictly
smaller than the depth.  Consequently every column in the selected local-dual
denominator is divisible by `p`, and every element of the denominator-
congruence subgroup `H_k` is congruent to the identity modulo `p`.

At an odd prime this proves that the integral matrix `g + 1` is a unit, so the
integral inverse-Cayley matrix of every `g : H_k` is defined.  This is the
chart-domain statement needed to compare `H_k / K_k` with the
determinant-loss coordinate quotient.
-/

noncomputable section

open Matrix
open scoped Matrix Matrix.Norms.Operator

namespace Matrix

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

/-- The inverse Cayley matrix of a form-preserving matrix in its integral
inverse domain is skew-adjoint.  This ring-level version does not require a
determinant-one hypothesis. -/
theorem skewAdjointOperator_cayleyRingInverseMatrix_eq_zero_of_formPreserving
    (F G : Matrix ι ι R) (hG : IsUnit (G + 1))
    (hform : Gᵀ * F * G = F) :
    skewAdjointOperator F (cayleyRingInverseMatrix G) = 0 := by
  let C : Matrix ι ι R := G + 1
  let D : Matrix ι ι R := G - 1
  let X : Matrix ι ι R := cayleyRingInverseMatrix G
  have hCdet : IsUnit C.det := (Matrix.isUnit_iff_isUnit_det C).mp hG
  have hCtdet : IsUnit Cᵀ.det := by
    rw [Matrix.det_transpose]
    exact hCdet
  have hcross : C * X = D := cayleyRingInverseMatrix_cross G hG
  have hcrossR : X * C = D := by
    change (C⁻¹ * D) * C = D
    calc
      (C⁻¹ * D) * C = C⁻¹ * (D * C) := by rw [Matrix.mul_assoc]
      _ = C⁻¹ * (C * D) := by
        congr 1
        dsimp [C, D]
        noncomm_ring
      _ = (C⁻¹ * C) * D := by rw [Matrix.mul_assoc]
      _ = D := by rw [Matrix.nonsing_inv_mul C hCdet, one_mul]
  have hcrossT : Cᵀ * Xᵀ = Dᵀ := by
    simpa only [Matrix.transpose_mul] using congrArg Matrix.transpose hcrossR
  have hcleared : Cᵀ * (Xᵀ * F + F * X) * C = 0 := by
    calc
      Cᵀ * (Xᵀ * F + F * X) * C =
          (Cᵀ * Xᵀ) * F * C + Cᵀ * F * (X * C) := by
        noncomm_ring
      _ = Dᵀ * F * C + Cᵀ * F * D := by rw [hcrossT, hcrossR]
      _ = 0 := by
        dsimp [C, D]
        rw [Matrix.transpose_add, Matrix.transpose_sub]
        simp only [Matrix.transpose_one]
        calc
          (Gᵀ - 1) * F * (G + 1) + (Gᵀ + 1) * F * (G - 1) =
              (Gᵀ * F * G - F) + (Gᵀ * F * G - F) := by
            noncomm_ring
          _ = 0 := by rw [hform]; simp
  change Xᵀ * F + F * X = 0
  calc
    Xᵀ * F + F * X =
        ((Cᵀ)⁻¹ * Cᵀ) * (Xᵀ * F + F * X) * (C * C⁻¹) := by
      rw [Matrix.nonsing_inv_mul Cᵀ hCtdet,
        Matrix.mul_nonsing_inv C hCdet, one_mul, Matrix.mul_one]
    _ = (Cᵀ)⁻¹ * (Cᵀ * (Xᵀ * F + F * X) * C) * C⁻¹ := by
      noncomm_ring
    _ = 0 := by rw [hcleared, Matrix.mul_zero, Matrix.zero_mul]

/-- The inverse Cayley formula commutes with its denominator. -/
theorem cayleyRingInverseMatrix_eq_sub_mul_nonsing_inv
    (G : Matrix ι ι R) (hG : IsUnit (G + 1)) :
    cayleyRingInverseMatrix G = (G - 1) * (G + 1)⁻¹ := by
  let C : Matrix ι ι R := G + 1
  let D : Matrix ι ι R := G - 1
  have hCdet : IsUnit C.det := (Matrix.isUnit_iff_isUnit_det C).mp hG
  change C⁻¹ * D = D * C⁻¹
  calc
    C⁻¹ * D = (C⁻¹ * D) * (C * C⁻¹) := by
      rw [Matrix.mul_nonsing_inv C hCdet, Matrix.mul_one]
    _ = C⁻¹ * (D * C) * C⁻¹ := by noncomm_ring
    _ = C⁻¹ * (C * D) * C⁻¹ := by
      congr 2
      dsimp [C, D]
      noncomm_ring
    _ = D * C⁻¹ := by
      rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul C hCdet, one_mul]

end Matrix

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The selected density depth is strictly larger than the form-determinant
valuation. -/
theorem padicValInt_pairingDeterminant_lt_localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    padicValInt p L.pairingDeterminant <
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p := by
  have hformdisc := L.padicValInt_pairingDeterminant_le_polarDeterminant p
  have hdepth :=
    L.localDensityHenselExponent_le_localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
      p
  unfold localDensityHenselExponent at hdepth
  omega

/-- Beyond the form-determinant valuation, every vector in the local-dual
denominator is coordinatewise divisible by `p`. -/
theorem localDualPadicDenominator_coord_mem_span_prime_of_pairingDeterminantVal_lt
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hval : padicValInt p L.pairingDeterminant < k)
    (d : Fin n → ℤ_[p]) (hd : d ∈ localDualPadicDenominator L p k) :
    ∀ i : Fin n, d i ∈ (Ideal.span {(p : ℤ_[p])} : Ideal ℤ_[p]) := by
  let y : Fin n → ℚ_[p] :=
    fun i ↦ (d i : ℚ_[p]) / (p : ℚ_[p]) ^ k
  have hy : L.IsLocalDualPadicVector p y :=
    L.isLocalDualPadicVector_div_primePow_of_mem_localDualPadicDenominator
      p k d hd
  obtain ⟨u, hu⟩ :=
    L.exists_padicIntVector_prime_mul_eq_primePow_mul_of_isLocalDual
      p k hval y hy
  intro i
  apply (Ideal.mem_span_singleton).2
  refine ⟨u i, ?_⟩
  apply PadicInt.ext
  change (d i : ℚ_[p]) = (p : ℚ_[p]) * (u i : ℚ_[p])
  have hp : (p : ℚ_[p]) ^ k ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero)
  calc
    (d i : ℚ_[p]) =
        (p : ℚ_[p]) ^ k *
          ((d i : ℚ_[p]) / (p : ℚ_[p]) ^ k) := by field_simp
    _ = (p : ℚ_[p]) * (u i : ℚ_[p]) := hu i

/-- The selected denominator-congruence subgroup lies in the ordinary
depth-one principal congruence subgroup. -/
theorem
    localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceSubgroup_le_principalCongruenceSubgroup_one
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceSubgroup p ≤
      L.localPadicPrincipalCongruenceSubgroup p 1 := by
  intro g hg
  rw [L.mem_localPadicPrincipalCongruenceSubgroup_iff]
  have hcols : ∀ j : Fin n,
      (fun i ↦
        L.localPadicLatticeStabilizerIntegralGL p g i j -
          (1 : Matrix (Fin n) (Fin n) ℤ_[p]) i j) ∈
        localDualPadicDenominator L p
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p) := by
    exact hg
  intro i j
  have hdiv :=
    L.localDualPadicDenominator_coord_mem_span_prime_of_pairingDeterminantVal_lt
      p
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)
      (L.padicValInt_pairingDeterminant_lt_localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)
      _ (hcols j) i
  have hdiv' :
      L.localPadicLatticeStabilizerIntegralGL p g i j -
          (1 : Matrix (Fin n) (Fin n) ℤ_[p]) i j ∈
        (Ideal.span {(p : ℤ_[p]) ^ 1} : Ideal ℤ_[p]) := by
    simpa using hdiv
  rw [← PadicInt.ker_toZModPow 1, RingHom.mem_ker] at hdiv'
  change PadicInt.toZModPow 1
      (L.localPadicLatticeStabilizerIntegralGL p g i j -
        (1 : Matrix (Fin n) (Fin n) ℤ_[p]) i j) = 0 at hdiv'
  rw [map_sub] at hdiv'
  have hone' :
      PadicInt.toZModPow 1
          ((1 : Matrix (Fin n) (Fin n) ℤ_[p]) i j) =
        (1 : Matrix (Fin n) (Fin n) (ZMod (p ^ 1))) i j := by
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  rw [hone'] at hdiv'
  exact sub_eq_zero.mp hdiv'

/-- At an odd prime, `g + 1` is an integral matrix unit for every
denominator-congruence element `g : H_k`. -/
theorem
    isUnit_localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceIntegralGL_add_one
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2)
    (g : L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceSubgroup p) :
    IsUnit
      ((L.localPadicLatticeStabilizerIntegralGL p g.1).1 +
        (1 : Matrix (Fin n) (Fin n) ℤ_[p])) := by
  apply padicIntMatrix_add_one_isUnit_of_toZMod_eq_one hp2
  intro i j
  have hdiv :=
    L.localDualPadicDenominator_coord_mem_span_prime_of_pairingDeterminantVal_lt
      p
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)
      (L.padicValInt_pairingDeterminant_lt_localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)
      _ (g.2 j) i
  have hmax :
      L.localPadicLatticeStabilizerIntegralGL p g.1 i j -
          (1 : Matrix (Fin n) (Fin n) ℤ_[p]) i j ∈
        IsLocalRing.maximalIdeal ℤ_[p] := by
    rw [PadicInt.maximalIdeal_eq_span_p]
    exact hdiv
  rw [← PadicInt.ker_toZMod, RingHom.mem_ker] at hmax
  change PadicInt.toZMod
      (L.localPadicLatticeStabilizerIntegralGL p g.1 i j -
        (1 : Matrix (Fin n) (Fin n) ℤ_[p]) i j) = 0 at hmax
  rw [map_sub] at hmax
  have hone :
      PadicInt.toZMod ((1 : Matrix (Fin n) (Fin n) ℤ_[p]) i j) =
        (1 : Matrix (Fin n) (Fin n) (ZMod p)) i j := by
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  rw [hone] at hmax
  exact sub_eq_zero.mp hmax

/-- The literal integral inverse-Cayley matrix of an odd-prime
denominator-congruence element. -/
def
    localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceInverseCayleyIntegral
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2)
    (g : L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceSubgroup p) :
    (skewAdjointMatricesLieSubalgebra (L.pairingMatrix_padic p)).toSubmodule := by
  let G := (L.localPadicLatticeStabilizerIntegralGL p g.1).1
  let X := cayleyRingInverseMatrix G
  refine ⟨X, ?_⟩
  apply (mem_ker_skewAdjointOperator_iff _ _).mp
  exact
    skewAdjointOperator_cayleyRingInverseMatrix_eq_zero_of_formPreserving
      (L.pairingMatrix_padic p) G
      (L.isUnit_localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceIntegralGL_add_one
        p hp2 g)
      (L.localPadicLatticeStabilizerIntegralGL_preserves_form p g.1)

/-- The integral inverse-Cayley matrix is the literal ring formula. -/
@[simp] theorem
    coe_localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceInverseCayleyIntegral
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2)
    (g : L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceSubgroup p) :
    (L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceInverseCayleyIntegral
        p hp2 g : Matrix (Fin n) (Fin n) ℤ_[p]) =
      cayleyRingInverseMatrix
        (L.localPadicLatticeStabilizerIntegralGL p g.1).1 :=
  rfl

/-- Every column of the integral inverse-Cayley matrix remains in the
selected local-dual denominator. -/
theorem
    localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceInverseCayleyIntegral_column_mem_denominator
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2)
    (g : L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceSubgroup p) :
    ∀ j : Fin n,
      (fun i ↦
        (L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceInverseCayleyIntegral
          p hp2 g : Matrix (Fin n) (Fin n) ℤ_[p]) i j) ∈
        localDualPadicDenominator L p
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p) := by
  let G := (L.localPadicLatticeStabilizerIntegralGL p g.1).1
  let D : Matrix (Fin n) (Fin n) ℤ_[p] := G - 1
  let B : Matrix (Fin n) (Fin n) ℤ_[p] := (G + 1)⁻¹
  have hG : IsUnit (G + 1) :=
    L.isUnit_localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceIntegralGL_add_one
      p hp2 g
  have hformula :
      (L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceInverseCayleyIntegral
          p hp2 g : Matrix (Fin n) (Fin n) ℤ_[p]) = D * B := by
    rw [L.coe_localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceInverseCayleyIntegral]
    exact cayleyRingInverseMatrix_eq_sub_mul_nonsing_inv G hG
  have hD : ∀ j : Fin n, (fun i ↦ D i j) ∈
      localDualPadicDenominator L p
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p) := by
    intro j
    simpa only [D, Matrix.sub_apply] using g.2 j
  intro j
  rw [hformula]
  have hsum :
      (∑ l : Fin n, B l j • (fun i ↦ D i l)) ∈
        localDualPadicDenominator L p
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p) := by
    exact (localDualPadicDenominator L p
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)).sum_mem
        fun l _ ↦
          (localDualPadicDenominator L p
            (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)).smul_mem
              (B l j) (hD l)
  convert hsum using 1
  funext i
  simp [Matrix.mul_apply, Pi.smul_apply, mul_comm]

/-- The integral inverse-Cayley matrix, transported to the rational p-adic
skew-adjoint coordinate space. -/
def
    localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceInverseCayley
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2)
    (g : L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceSubgroup p) :
    (skewAdjointMatricesLieSubalgebra
      (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule := by
  let Xz :=
    L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceInverseCayleyIntegral
      p hp2 g
  let Xq : Matrix (Fin n) (Fin n) ℚ_[p] :=
    (Xz : Matrix (Fin n) (Fin n) ℤ_[p]).map PadicInt.Coe.ringHom
  refine ⟨Xq, ?_⟩
  apply (mem_ker_skewAdjointOperator_iff _ _).mp
  apply LinearMap.mem_ker.mpr
  have hXz : skewAdjointOperator (L.pairingMatrix_padic p)
      (Xz : Matrix (Fin n) (Fin n) ℤ_[p]) = 0 :=
    LinearMap.mem_ker.mp
      ((mem_ker_skewAdjointOperator_iff _ _).mpr Xz.property)
  have hmap :
      (skewAdjointOperator (L.pairingMatrix_padic p)
          (Xz : Matrix (Fin n) (Fin n) ℤ_[p])).map PadicInt.Coe.ringHom =
        skewAdjointOperator
          (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p])) Xq := by
    simp only [skewAdjointOperator_apply]
    rw [Matrix.map_add _ (fun a b ↦ map_add PadicInt.Coe.ringHom a b),
      Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map,
      L.rationalFormMatrix_map_padic_eq_pairingMatrix_padicField]
    rfl
  rw [← hmap, hXz]
  simp

/-- The transported inverse-Cayley coordinate is literally the scalar
extension of the integral inverse-Cayley matrix. -/
@[simp] theorem
    coe_localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceInverseCayley
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2)
    (g : L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceSubgroup p) :
    (L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceInverseCayley
        p hp2 g : Matrix (Fin n) (Fin n) ℚ_[p]) =
      (L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceInverseCayleyIntegral
        p hp2 g : Matrix (Fin n) (Fin n) ℤ_[p]).map
          PadicInt.Coe.ringHom :=
  by
    simp [localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceInverseCayley]

/-- Scalar extension of the integral coordinate is the p-adic-field
inverse-Cayley formula of the stabilizer matrix. -/
theorem
    coe_localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceInverseCayley_eq_ringFormula
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2)
    (g : L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceSubgroup p) :
    (L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceInverseCayley
        p hp2 g : Matrix (Fin n) (Fin n) ℚ_[p]) =
      cayleyRingInverseMatrix
        ((L.localPadicLatticeStabilizerIntegralGL p g.1).1.map
          PadicInt.Coe.ringHom) := by
  let G := (L.localPadicLatticeStabilizerIntegralGL p g.1).1
  let A : Matrix (Fin n) (Fin n) ℤ_[p] := G + 1
  have hA : IsUnit A :=
    L.isUnit_localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceIntegralGL_add_one
      p hp2 g
  have hAmap : A.map PadicInt.Coe.ringHom =
      G.map PadicInt.Coe.ringHom + 1 := by
    dsimp [A]
    rw [Matrix.map_add _ (fun a b ↦ map_add PadicInt.Coe.ringHom a b),
      Matrix.map_one PadicInt.Coe.ringHom
        (map_zero PadicInt.Coe.ringHom) (map_one PadicInt.Coe.ringHom)]
  have hAinvmap :
      A⁻¹.map PadicInt.Coe.ringHom =
        (G.map PadicInt.Coe.ringHom + 1)⁻¹ := by
    rw [show A⁻¹ = (hA.unit⁻¹).1 by
      rw [Matrix.coe_units_inv, hA.unit_spec]]
    change
      (Matrix.GeneralLinearGroup.map PadicInt.Coe.ringHom hA.unit⁻¹).1 =
        (G.map PadicInt.Coe.ringHom + 1)⁻¹
    rw [map_inv, Matrix.coe_units_inv]
    congr 1
  rw [L.coe_localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceInverseCayley,
    L.coe_localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceInverseCayleyIntegral]
  change
    (A⁻¹ * (G - 1)).map PadicInt.Coe.ringHom =
      (G.map PadicInt.Coe.ringHom + 1)⁻¹ *
        (G.map PadicInt.Coe.ringHom - 1)
  rw [Matrix.map_mul, hAinvmap,
    Matrix.map_sub _ (fun a b ↦ map_sub PadicInt.Coe.ringHom a b),
    Matrix.map_one PadicInt.Coe.ringHom
      (map_zero PadicInt.Coe.ringHom) (map_one PadicInt.Coe.ringHom)]

/-- Every element of `H_k` has inverse-Cayley coordinate in the exact
level-`k` form-adapted ball. -/
theorem
    localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceInverseCayley_mem_formElementaryUniformCoordinateBall
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2)
    (g : L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceSubgroup p) :
    L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceInverseCayley
        p hp2 g ∈
      skewAdjointFormElementaryPadicUniformCoordinateBall
        p
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)
        L.rationalFormMatrix (L.form_symm.map _)
          L.rationalFormMatrix_det_ne_zero := by
  apply
    (mem_skewAdjointFormElementaryPadicUniformCoordinateBall_iff_upper
      p
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)
      L.rationalFormMatrix (L.form_symm.map _)
      L.rationalFormMatrix_det_ne_zero _).2
  intro q
  let Xz :=
    L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceInverseCayleyIntegral
      p hp2 g
  have hcol :=
    L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceInverseCayleyIntegral_column_mem_denominator
      p hp2 g q.1.2
  have hdiv :=
    (L.mem_localDualPadicDenominator_iff_forall_padic
      p
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)
      (fun i ↦ (Xz : Matrix (Fin n) (Fin n) ℤ_[p]) i q.1.2)).1
      hcol ((Pi.basisFun ℤ_[p] (Fin n)) q.1.1)
  have hdot :
      dotProduct ((Pi.basisFun ℤ_[p] (Fin n)) q.1.1)
          ((L.pairingMatrix_padic p).mulVec
            (fun i ↦ (Xz : Matrix (Fin n) (Fin n) ℤ_[p]) i q.1.2)) =
        (L.pairingMatrix_padic p *
          (Xz : Matrix (Fin n) (Fin n) ℤ_[p])) q.1.1 q.1.2 := by
    rw [dotProduct]
    calc
      (∑ i,
          ((Pi.basisFun ℤ_[p] (Fin n)) q.1.1) i *
            (L.pairingMatrix_padic p).mulVec
              (fun a ↦ (Xz : Matrix (Fin n) (Fin n) ℤ_[p]) a q.1.2) i) =
          ((Pi.basisFun ℤ_[p] (Fin n)) q.1.1) q.1.1 *
            (L.pairingMatrix_padic p).mulVec
              (fun a ↦ (Xz : Matrix (Fin n) (Fin n) ℤ_[p]) a q.1.2) q.1.1 := by
        exact Finset.sum_eq_single q.1.1
          (by
            intro i _ hi
            simp [Pi.basisFun, hi])
          (by simp)
      _ = (L.pairingMatrix_padic p *
          (Xz : Matrix (Fin n) (Fin n) ℤ_[p])) q.1.1 q.1.2 := by
        simp [Pi.basisFun, Matrix.mulVec, Matrix.mul_apply, dotProduct]
  rw [hdot] at hdiv
  have hmem :
      (L.pairingMatrix_padic p *
          (Xz : Matrix (Fin n) (Fin n) ℤ_[p])) q.1.1 q.1.2 ∈
        (Ideal.span
          {(p : ℤ_[p]) ^
            L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p} :
          Ideal ℤ_[p]) :=
    (Ideal.mem_span_singleton).2 hdiv
  have hnorm :=
    (PadicInt.norm_le_pow_iff_mem_span_pow
      ((L.pairingMatrix_padic p *
        (Xz : Matrix (Fin n) (Fin n) ℤ_[p])) q.1.1 q.1.2)
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)).2
      hmem
  have hmap :
      ((L.pairingMatrix_padic p *
          (Xz : Matrix (Fin n) (Fin n) ℤ_[p])).map PadicInt.Coe.ringHom) =
        L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]) *
          (L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceInverseCayley
            p hp2 g : Matrix (Fin n) (Fin n) ℚ_[p]) := by
    rw [Matrix.map_mul,
      L.coe_localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceInverseCayley,
      L.rationalFormMatrix_map_padic_eq_pairingMatrix_padicField]
    rfl
  rw [← hmap]
  change
    ‖(((L.pairingMatrix_padic p *
        (Xz : Matrix (Fin n) (Fin n) ℤ_[p])) q.1.1 q.1.2 : ℤ_[p]) : ℚ_[p])‖ ≤
      ‖(p : ℚ_[p]) ^
        L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p‖
  rw [show
    ‖(((L.pairingMatrix_padic p *
        (Xz : Matrix (Fin n) (Fin n) ℤ_[p])) q.1.1 q.1.2 : ℤ_[p]) : ℚ_[p])‖ =
      ‖(L.pairingMatrix_padic p *
        (Xz : Matrix (Fin n) (Fin n) ℤ_[p])) q.1.1 q.1.2‖ from rfl]
  calc
    ‖(L.pairingMatrix_padic p *
        (Xz : Matrix (Fin n) (Fin n) ℤ_[p])) q.1.1 q.1.2‖ ≤
        (p : ℝ) ^
          (-(L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p : ℤ)) :=
      hnorm
    _ = ‖(p : ℚ_[p]) ^
          L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p‖ := by
      rw [norm_pow, Padic.norm_p]
      simp [inv_pow]


end PositiveDefiniteIntegralLattice
