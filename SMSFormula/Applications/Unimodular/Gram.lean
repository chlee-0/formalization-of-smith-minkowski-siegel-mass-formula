import SMSFormula.Lattice
import SMSFormula.IntegralQuadraticFormBridge

/-!
# Gram-matrix predicates for unimodular mass applications

The application uses the existing `PositiveDefiniteIntegralLattice` convention: the stored
matrix is the integral quadratic matrix `G` for `q(x) = xᵀGx`.  Thus classical
unimodularity is `pairingDeterminant = 1`; the repository's polar discriminant is then
`2^n`.
-/

noncomputable section

open BigOperators

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ} (L : PositiveDefiniteIntegralLattice n)

/-- Classical unimodularity in the uniform integral quadratic-matrix model. -/
def IsUnimodular : Prop :=
  L.pairingDeterminant = 1

/-- Every vector has even norm `q(x)`.  For a unimodular lattice this is the
Type II (even) condition.  This is a parity predicate only: unimodularity is the
separate hypothesis `IsUnimodular`. -/
def HasEvenNorms : Prop :=
  ∀ x : Fin n → ℤ, Even (L.quadForm x)

/-- Some vector has odd norm `q(x)`.  For a unimodular lattice this is the
Type I (odd) condition.  This is a parity predicate only: unimodularity is the
separate hypothesis `IsUnimodular`. -/
def HasOddNorm : Prop :=
  ∃ x : Fin n → ℤ, Odd (L.quadForm x)

theorem polarDeterminant_eq_two_pow_of_isUnimodular (h : L.IsUnimodular) :
    L.polarDeterminant = (2 : ℤ) ^ n := by
  rw [L.polarDeterminant_eq_two_pow_mul_pairingDeterminant, h, mul_one]

/-- A classically unimodular integral form matrix has integral real inverse:
over `ℝ`, the inverse of the stored form matrix is the cast adjugate matrix.
This is the lattice-specific determinant-one input needed to reindex the
inverse theta series in the Gaussian/Poisson Type II obstruction route. -/
theorem real_pairingMatrix_inv_eq_adjugate_of_isUnimodular (h : L.IsUnimodular) :
    (L.pairingMatrix.map (Int.cast : ℤ → ℝ))⁻¹ =
      L.pairingMatrix.adjugate.map (Int.cast : ℤ → ℝ) := by
  apply Matrix.inv_eq_right_inv
  have hdet : L.pairingMatrix.det = 1 := by
    simpa [IsUnimodular, pairingDeterminant] using h
  calc
    L.pairingMatrix.map (Int.cast : ℤ → ℝ) *
        L.pairingMatrix.adjugate.map (Int.cast : ℤ → ℝ)
        = (L.pairingMatrix * L.pairingMatrix.adjugate).map (Int.cast : ℤ → ℝ) := by
          ext i j
          simp [Matrix.mul_apply]
    _ = ((L.pairingMatrix.det • (1 : Matrix (Fin n) (Fin n) ℤ)).map
          (Int.cast : ℤ → ℝ)) := by
          rw [Matrix.mul_adjugate]
    _ = 1 := by
          ext i j
          by_cases hij : i = j
          · subst hij
            simp [hdet]
          · simp [hdet, hij]

theorem not_hasEvenNorms_iff_hasOddNorm :
    ¬ L.HasEvenNorms ↔ L.HasOddNorm := by
  constructor
  · intro h
    rw [HasEvenNorms] at h
    push_neg at h
    rcases h with ⟨x, hx⟩
    exact ⟨x, Int.not_even_iff_odd.mp hx⟩
  · rintro ⟨x, hx⟩ hII
    exact (Int.not_even_iff_odd.mpr hx) (hII x)

theorem not_hasOddNorm_of_hasEvenNorms
    (h : L.HasEvenNorms) : ¬ L.HasOddNorm := by
  rw [← L.not_hasEvenNorms_iff_hasOddNorm]
  exact not_not.mpr h

theorem not_hasEvenNorms_of_hasOddNorm
    (h : L.HasOddNorm) : ¬ L.HasEvenNorms := by
  rwa [L.not_hasEvenNorms_iff_hasOddNorm]

theorem quadForm_single_one (i : Fin n) :
    L.quadForm (Pi.single i 1) = L.pairingMatrix i i := by
  simp [L.quadForm_eq_dotProduct, Matrix.mulVec, dotProduct, Pi.single_apply]

theorem hasEvenNorms_iff_forall_diag_even :
    L.HasEvenNorms ↔ ∀ i, Even (L.pairingMatrix i i) := by
  constructor
  · intro h i
    simpa [L.quadForm_single_one i] using h (Pi.single i 1)
  · intro hdiag x
    have hq := L.toIntegralQuadraticForm.quadForm_eq_diagonal_sum_add_strictUpperSum x
    rw [L.toIntegralQuadraticForm_quadForm] at hq
    rw [hq]
    refine Even.add ?_ ?_
    · exact Finset.even_sum _ (by
        intro i hi
        have hhalf : L.toIntegralQuadraticForm.polarGramMatrix i i / 2 = L.pairingMatrix i i := by
          change ((2 : ℤ) * L.pairingMatrix i i) / 2 = L.pairingMatrix i i
          omega
        rw [hhalf]
        exact Even.mul_right (hdiag i) (x i ^ 2))
    · exact Finset.even_sum _ (by
        intro i hi
        exact Finset.even_sum _ (by
          intro j hj
          change Even (((2 : ℤ) * L.pairingMatrix i j) * x i * x j)
          exact Even.mul_right (Even.mul_right ⟨L.pairingMatrix i j, by ring⟩ (x i)) (x j)))

theorem hasOddNorm_iff_exists_diag_odd :
    L.HasOddNorm ↔ ∃ i, Odd (L.pairingMatrix i i) := by
  rw [← L.not_hasEvenNorms_iff_hasOddNorm,
    L.hasEvenNorms_iff_forall_diag_even]
  push_neg
  simp [Int.not_even_iff_odd]

namespace MatrixParity

/-- The integer skew-symmetric matrix with the same strict upper-triangular
entries as `A`.  It is used to compare even-diagonal symmetric matrices modulo
`2` with odd-rank skew-symmetric matrices. -/
def skewOfUpper {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => if i < j then A i j else if j < i then - A j i else 0

theorem skewOfUpper_transpose {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) :
    (skewOfUpper A).transpose = - skewOfUpper A := by
  ext i j
  dsimp [skewOfUpper]
  by_cases hij : i < j
  · have hji : ¬ j < i := by omega
    simp [hij, hji]
  · by_cases hji : j < i
    · simp [hij, hji]
    · have hEq : i = j := by omega
      subst hEq
      simp

theorem det_eq_zero_of_transpose_eq_neg_of_odd {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
    (hB : B.transpose = -B) (hodd : Odd n) : B.det = 0 := by
  have hdetT : B.transpose.det = B.det := Matrix.det_transpose B
  have hdetNeg : (-B).det = (-1 : ℤ) ^ n * B.det := by
    simpa using Matrix.det_neg (A := B)
  have h : B.det = (-1 : ℤ) ^ n * B.det := by
    calc
      B.det = B.transpose.det := hdetT.symm
      _ = (-B).det := by rw [hB]
      _ = (-1 : ℤ) ^ n * B.det := hdetNeg
  rcases hodd with ⟨k, hk⟩
  have hpow : (-1 : ℤ) ^ n = -1 := by
    rw [hk]
    simp [pow_succ, pow_mul]
  rw [hpow] at h
  nlinarith

theorem mapMatrix_skewOfUpper_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hsymm : A.IsSymm) (hdiag : ∀ i, Even (A i i)) :
    (Int.castRingHom (ZMod 2)).mapMatrix (skewOfUpper A) =
      (Int.castRingHom (ZMod 2)).mapMatrix A := by
  ext i j
  dsimp [skewOfUpper]
  by_cases hij : i < j
  · simp [hij]
  · by_cases hji : j < i
    · have hs : A j i = A i j := hsymm.apply i j
      simp [hij, hji, hs]
    · have hEq : i = j := by omega
      rcases hdiag i with ⟨a, ha⟩
      subst hEq
      simp [ha]
      rw [← two_mul (a : ZMod 2)]
      rw [show (2 : ZMod 2) = 0 from ZMod.natCast_self 2, zero_mul]

/-- An odd-rank symmetric integer matrix with even diagonal has even determinant.
This is the elementary parity integral model of the even-unimodular rank obstruction. -/
theorem even_det_of_isSymm_of_forall_diag_even_of_odd {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℤ) (hsymm : A.IsSymm)
    (hdiag : ∀ i, Even (A i i)) (hodd : Odd n) : Even A.det := by
  let B := skewOfUpper A
  have hBskew : B.transpose = -B := skewOfUpper_transpose A
  have hBdet : B.det = 0 := det_eq_zero_of_transpose_eq_neg_of_odd B hBskew hodd
  have hmap : (Int.castRingHom (ZMod 2)).mapMatrix B =
      (Int.castRingHom (ZMod 2)).mapMatrix A :=
    mapMatrix_skewOfUpper_eq A hsymm hdiag
  have hBmapdet : ((Int.castRingHom (ZMod 2)).mapMatrix B).det = 0 := by
    rw [← RingHom.map_det]
    simp [hBdet]
  have hAmapdet : ((Int.castRingHom (ZMod 2)).mapMatrix A).det = 0 := by
    rwa [hmap] at hBmapdet
  have hcastdet : ((A.det : ℤ) : ZMod 2) = 0 := by
    calc
      ((A.det : ℤ) : ZMod 2) = ((Int.castRingHom (ZMod 2)).mapMatrix A).det := by
        exact RingHom.map_det (Int.castRingHom (ZMod 2)) A
      _ = 0 := hAmapdet
  have hdiv : (2 : ℤ) ∣ A.det := by
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd A.det 2).mp hcastdet
  rcases hdiv with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  nlinarith

end MatrixParity

/-- Odd-rank classically unimodular lattices cannot be Type II.  This proves
the odd-rank half of the elementary Type II divisibility obstruction. -/
theorem not_hasEvenNorms_of_isUnimodular_odd_rank {n : ℕ}
    (L : PositiveDefiniteIntegralLattice n) (hn : Odd n) (hU : L.IsUnimodular) :
    ¬ L.HasEvenNorms := by
  intro hII
  have hdiag := L.hasEvenNorms_iff_forall_diag_even.mp hII
  have hdetEven : Even L.pairingMatrix.det :=
    MatrixParity.even_det_of_isSymm_of_forall_diag_even_of_odd L.pairingMatrix L.form_symm hdiag hn
  have hdet : L.pairingMatrix.det = 1 := by
    simpa [IsUnimodular, pairingDeterminant] using hU
  rw [hdet] at hdetEven
  norm_num at hdetEven

theorem hasOddNorm_of_isUnimodular_odd_rank {n : ℕ}
    (L : PositiveDefiniteIntegralLattice n) (hn : Odd n) (hU : L.IsUnimodular) : L.HasOddNorm := by
  rw [← L.not_hasEvenNorms_iff_hasOddNorm]
  exact L.not_hasEvenNorms_of_isUnimodular_odd_rank hn hU

/-- In rank zero the determinant convention gives classical unimodularity
without extra hypotheses. -/
theorem isUnimodular_rank_zero (L : PositiveDefiniteIntegralLattice 0) : L.IsUnimodular := by
  simp [IsUnimodular, pairingDeterminant]

theorem quadForm_eq_zero_rank_zero (L : PositiveDefiniteIntegralLattice 0) (x : Fin 0 → ℤ) :
    L.quadForm x = 0 := by
  rw [L.quadForm_eq_dotProduct]
  simp [dotProduct]

theorem hasEvenNorms_rank_zero (L : PositiveDefiniteIntegralLattice 0) :
    L.HasEvenNorms := by
  intro x
  rw [L.quadForm_eq_zero_rank_zero x]
  exact ⟨0, by rfl⟩

theorem not_hasOddNorm_rank_zero (L : PositiveDefiniteIntegralLattice 0) :
    ¬ L.HasOddNorm := by
  rintro ⟨x, hx⟩
  rw [L.quadForm_eq_zero_rank_zero x] at hx
  norm_num at hx

/-- Rank one classically unimodular lattices are necessarily odd.  This is the
rank-one endpoint of the Type I/II dichotomy, separate from the high-rank mass
theorem. -/
theorem not_hasEvenNorms_of_isUnimodular_rank_one (L : PositiveDefiniteIntegralLattice 1)
    (hU : L.IsUnimodular) : ¬ L.HasEvenNorms := by
  intro hII
  have hdiag_even : Even (L.pairingMatrix 0 0) :=
    (L.hasEvenNorms_iff_forall_diag_even.mp hII) 0
  have hdiag_one : L.pairingMatrix 0 0 = 1 := by
    simpa [IsUnimodular, pairingDeterminant] using hU
  rw [hdiag_one] at hdiag_even
  norm_num at hdiag_even

theorem hasOddNorm_of_isUnimodular_rank_one (L : PositiveDefiniteIntegralLattice 1)
    (hU : L.IsUnimodular) : L.HasOddNorm := by
  rw [← L.not_hasEvenNorms_iff_hasOddNorm]
  exact L.not_hasEvenNorms_of_isUnimodular_rank_one hU

/-- Rank two classically unimodular lattices cannot be Type II.  The
rank-two determinant is `a*c - b^2`; if both diagonal entries are even, then
this determinant is congruent to `0` or `3` modulo `4`, contradicting the
positive-definite unimodular determinant `1`. -/
theorem not_hasEvenNorms_of_isUnimodular_rank_two (L : PositiveDefiniteIntegralLattice 2)
    (hU : L.IsUnimodular) : ¬ L.HasEvenNorms := by
  intro hII
  have hdiag := L.hasEvenNorms_iff_forall_diag_even.mp hII
  rcases hdiag 0 with ⟨a, h00⟩
  rcases hdiag 1 with ⟨c, h11⟩
  have h10 : L.pairingMatrix 1 0 = L.pairingMatrix 0 1 := by
    exact (L.form_symm.apply 1 0).symm
  have hdet : L.pairingMatrix.det = 1 := by
    simpa [IsUnimodular, pairingDeterminant] using hU
  have hdet' : L.pairingMatrix 0 0 * L.pairingMatrix 1 1 -
      L.pairingMatrix 0 1 * L.pairingMatrix 0 1 = 1 := by
    simpa [Matrix.det_fin_two, h10] using hdet
  rw [h00, h11] at hdet'
  rcases Int.even_or_odd (L.pairingMatrix 0 1) with hb | hb
  · rcases hb with ⟨b, hb⟩
    rw [hb] at hdet'
    ring_nf at hdet'
    have hfour : (4 : ℤ) ∣ (1 : ℤ) := by
      refine ⟨a * c - b * b, ?_⟩
      linarith
    norm_num at hfour
  · rcases hb with ⟨b, hb⟩
    rw [hb] at hdet'
    ring_nf at hdet'
    have hfour : (4 : ℤ) ∣ (2 : ℤ) := by
      refine ⟨a * c - (b * b + b), ?_⟩
      linarith
    norm_num at hfour

/-- Rank two classically unimodular lattices are necessarily Type I. -/
theorem hasOddNorm_of_isUnimodular_rank_two (L : PositiveDefiniteIntegralLattice 2)
    (hU : L.IsUnimodular) : L.HasOddNorm := by
  rw [← L.not_hasEvenNorms_iff_hasOddNorm]
  exact L.not_hasEvenNorms_of_isUnimodular_rank_two hU

/-- Rank three classically unimodular lattices cannot be Type II.  The
rank-three determinant expansion has every term even when all diagonal entries
are even, contradicting determinant `1`. -/
theorem not_hasEvenNorms_of_isUnimodular_rank_three (L : PositiveDefiniteIntegralLattice 3)
    (hU : L.IsUnimodular) : ¬ L.HasEvenNorms := by
  intro hII
  have hdiag := L.hasEvenNorms_iff_forall_diag_even.mp hII
  rcases hdiag 0 with ⟨a, h00⟩
  rcases hdiag 1 with ⟨b, h11⟩
  rcases hdiag 2 with ⟨c, h22⟩
  have h10 : L.pairingMatrix 1 0 = L.pairingMatrix 0 1 := by
    exact (L.form_symm.apply 1 0).symm
  have h20 : L.pairingMatrix 2 0 = L.pairingMatrix 0 2 := by
    exact (L.form_symm.apply 2 0).symm
  have h21 : L.pairingMatrix 2 1 = L.pairingMatrix 1 2 := by
    exact (L.form_symm.apply 2 1).symm
  have hdet : L.pairingMatrix.det = 1 := by
    simpa [IsUnimodular, pairingDeterminant] using hU
  rw [Matrix.det_fin_three] at hdet
  rw [h00, h11, h22, h10, h20, h21] at hdet
  ring_nf at hdet
  have htwo : (2 : ℤ) ∣ (1 : ℤ) := by
    refine ⟨4 * a * b * c - a * L.pairingMatrix 1 2 * L.pairingMatrix 1 2 -
        b * L.pairingMatrix 0 2 * L.pairingMatrix 0 2 +
        L.pairingMatrix 0 1 * L.pairingMatrix 0 2 * L.pairingMatrix 1 2 -
        c * L.pairingMatrix 0 1 * L.pairingMatrix 0 1, ?_⟩
    linarith
  norm_num at htwo

/-- Rank three classically unimodular lattices are necessarily Type I. -/
theorem hasOddNorm_of_isUnimodular_rank_three (L : PositiveDefiniteIntegralLattice 3)
    (hU : L.IsUnimodular) : L.HasOddNorm := by
  rw [← L.not_hasEvenNorms_iff_hasOddNorm]
  exact L.not_hasEvenNorms_of_isUnimodular_rank_three hU

/-- The fourth powers of `i` are `1`, in the concrete form used to reduce a
complex phase modulo four. -/
theorem complex_I_pow_four_mul (q : ℕ) : Complex.I ^ (4 * q) = 1 := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [Nat.mul_succ, pow_add, ih]
      norm_num [Complex.I_mul_I]

/-- Powers of `i` depend only on the exponent modulo four. -/
theorem complex_I_pow_eq_pow_mod_four (k : ℕ) :
    Complex.I ^ k = Complex.I ^ (k % 4) := by
  nth_rewrite 1 [← Nat.mod_add_div k 4]
  rw [add_comm, pow_add, complex_I_pow_four_mul, one_mul]

/-- If a power of `i` is `1`, the exponent is divisible by `4`.  This is the
scalar endpoint used by the Gaussian/Poisson route to the positive-definite
Type II rank obstruction. -/
theorem four_dvd_of_complex_I_pow_eq_one {k : ℕ} (h : Complex.I ^ k = 1) :
    4 ∣ k := by
  refine Nat.dvd_of_mod_eq_zero ?_
  have hred : Complex.I ^ (k % 4) = 1 := by
    rwa [complex_I_pow_eq_pow_mod_four k] at h
  have hlt : k % 4 < 4 := Nat.mod_lt k (by norm_num)
  interval_cases k % 4
  · rfl
  · norm_num [Complex.ext_iff] at hred
  · norm_num [Complex.I_mul_I, Complex.ext_iff] at hred
  · norm_num [Complex.I_mul_I, Complex.ext_iff] at hred

/-- The same scalar endpoint in the `2 * k` form expected for even ranks. -/
theorem eight_dvd_two_mul_of_complex_I_pow_eq_one {k : ℕ} (h : Complex.I ^ k = 1) :
    8 ∣ 2 * k := by
  rcases four_dvd_of_complex_I_pow_eq_one h with ⟨m, hm⟩
  refine ⟨m, ?_⟩
  omega

/-- Even-rank packaging of the scalar endpoint: if the Poisson comparison gives
`i ^ (n / 2) = 1` and `n` is even, then `8 ∣ n`. -/
theorem eight_dvd_of_even_complex_I_pow_half_eq_one {n : ℕ} (hn : Even n)
    (h : Complex.I ^ (n / 2) = 1) : 8 ∣ n := by
  rcases hn with ⟨k, hk⟩
  have hhalf : n / 2 = k := by omega
  rw [hhalf] at h
  rcases four_dvd_of_complex_I_pow_eq_one h with ⟨m, hm⟩
  refine ⟨m, ?_⟩
  omega

variable {L L' : PositiveDefiniteIntegralLattice n}

theorem quadForm_eq_mulVec_of_globalIsometryMatrix
    {U : Matrix (Fin n) (Fin n) ℤ}
    (hU : U.transpose * L'.pairingMatrix * U = L.pairingMatrix) (x : Fin n → ℤ) :
    L.quadForm x = L'.quadForm (U.mulVec x) := by
  rw [L.quadForm_eq_dotProduct, L'.quadForm_eq_dotProduct, ← hU]
  rw [show (U.transpose * L'.pairingMatrix * U).mulVec x =
      U.transpose.mulVec (L'.pairingMatrix.mulVec (U.mulVec x)) from by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]]
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

theorem isUnimodular_of_isGlobalIsometry
    (h : L.IsGlobalIsometry L') (h' : L'.IsUnimodular) : L.IsUnimodular := by
  rw [IsUnimodular, L.pairingDeterminant_eq_of_isGlobalIsometry h, h']

theorem hasEvenNorms_of_isGlobalIsometry
    (h : L.IsGlobalIsometry L') (h' : L'.HasEvenNorms) : L.HasEvenNorms := by
  rintro x
  obtain ⟨U, hU_unit, hU⟩ := h
  rw [quadForm_eq_mulVec_of_globalIsometryMatrix hU]
  exact h' _

theorem hasOddNorm_of_isGlobalIsometry
    (h : L.IsGlobalIsometry L') (h' : L'.HasOddNorm) : L.HasOddNorm := by
  obtain ⟨U, hU_unit, hU⟩ := h
  rcases h' with ⟨y, hy⟩
  let V : Matrix (Fin n) (Fin n) ℤ := hU_unit.unit.inv
  refine ⟨V.mulVec y, ?_⟩
  rw [quadForm_eq_mulVec_of_globalIsometryMatrix hU]
  have hUV : U * V = 1 := by
    dsimp [V]
    calc
      U * hU_unit.unit.inv = hU_unit.unit.val * hU_unit.unit.inv := by
        exact congrArg (fun A : Matrix (Fin n) (Fin n) ℤ => A * hU_unit.unit.inv)
          hU_unit.unit_spec.symm
      _ = 1 := hU_unit.unit.val_inv
  have hUy : U.mulVec (V.mulVec y) = y := by
    rw [Matrix.mulVec_mulVec, hUV, Matrix.one_mulVec]
  rw [hUy]
  exact hy


end PositiveDefiniteIntegralLattice
