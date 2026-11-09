import SMSFormula.Applications.Unimodular.Constants
import SMSFormula.Applications.Unimodular.Genus
import SMSFormula.Mass

/-!
# Low-rank ordinary mass endpoints for unimodular applications

This file records explicit low-rank ordinary-mass endpoints.  It uses only the
existing geometric mass definition: the rank-zero and rank-one identity genera
are singletons, and the ordinary stabilizers are computed directly from the
existing isometry-group definition.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

open Matrix BigOperators
open UnimodularMass

/-- The ordinary isometry group of the rank-zero identity seed is trivial. -/
private def identityLatticeZeroIsometryGroupEquivUnit :
    (identityLattice 0).IsometryGroup ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨1, by
    constructor
    · exact isUnit_one
    · simp [identityLattice]
  ⟩
  left_inv U := by
    apply Subtype.ext
    ext i j
    fin_cases i
  right_inv u := by
    cases u
    rfl

/-- The explicit stabilizer count for the rank-zero identity lattice. -/
theorem identityLattice_zero_isometryGroup_card :
    Fintype.card (identityLattice 0).IsometryGroup = 1 := by
  rw [Fintype.card_congr identityLatticeZeroIsometryGroupEquivUnit]
  decide

/-- The rank-zero identity seed has ordinary genus mass `1`. -/
theorem identityLattice_zero_ordinaryGenusMass :
    (identityLattice 0).ordinaryGenusMass = (1 : ℚ) := by
  classical
  unfold ordinaryGenusMass
  have hterm : ∀ C : (identityLattice 0).genus,
      ((Fintype.card (genusClassRepresentative (identityLattice 0) C).IsometryGroup : ℚ)⁻¹) =
        (1 : ℚ) := by
    intro C
    have hIso := isGlobalIsometry_identityLattice_zero
      (genusClassRepresentative (identityLattice 0) C)
    have hcard := isometryGroup_card_eq_of_isGlobalIsometry hIso
    rw [hcard, identityLattice_zero_isometryGroup_card]
    norm_num
  calc
    (∑ C : (identityLattice 0).genus,
        ((Fintype.card (genusClassRepresentative (identityLattice 0) C).IsometryGroup : ℚ)⁻¹))
        = ∑ C : (identityLattice 0).genus, (1 : ℚ) := by
          exact Finset.sum_congr rfl (fun C _ => hterm C)
    _ = (Fintype.card (identityLattice 0).genus : ℚ) * (1 : ℚ) := by
          simp
    _ = 1 := by
          rw [identityLattice_zero_genus_card]
          norm_num

/-- Real-cast form of the rank-zero identity ordinary genus mass endpoint. -/
theorem identityLattice_zero_ordinaryGenusMass_real :
    (((identityLattice 0).ordinaryGenusMass : ℚ) : ℝ) = (1 : ℝ) := by
  exact_mod_cast identityLattice_zero_ordinaryGenusMass

/-- The rank-zero identity ordinary genus mass matches the Type II constant. -/
theorem identityLattice_zero_ordinaryGenusMass_eq_typeIIConstant :
    (identityLattice 0).ordinaryGenusMass = typeIIConstant 0 := by
  rw [identityLattice_zero_ordinaryGenusMass, typeIIConstant_zero]

/-- Real-cast form of the rank-zero identity Type II ordinary mass endpoint. -/
theorem identityLattice_zero_ordinaryGenusMass_real_eq_typeIIConstant :
    (((identityLattice 0).ordinaryGenusMass : ℚ) : ℝ) = (typeIIConstant 0 : ℝ) := by
  exact_mod_cast identityLattice_zero_ordinaryGenusMass_eq_typeIIConstant

/-- Every rank-zero lattice has the Type II ordinary genus mass. -/
theorem ordinaryGenusMass_eq_typeIIConstant_of_rank_zero
    (L : PositiveDefiniteIntegralLattice 0) :
    L.ordinaryGenusMass = typeIIConstant 0 := by
  rw [ordinaryGenusMass_eq_of_isGlobalIsometry
    (isGlobalIsometry_identityLattice_zero L)]
  exact identityLattice_zero_ordinaryGenusMass_eq_typeIIConstant

/-- Real-cast form of the rank-zero Type II ordinary genus mass endpoint. -/
theorem ordinaryGenusMass_real_eq_typeIIConstant_of_rank_zero
    (L : PositiveDefiniteIntegralLattice 0) :
    ((L.ordinaryGenusMass : ℚ) : ℝ) = (typeIIConstant 0 : ℝ) := by
  exact_mod_cast ordinaryGenusMass_eq_typeIIConstant_of_rank_zero L

/-- The ordinary isometry group of the rank-one identity seed is `{±1}`. -/
private def identityLatticeOneIsometryGroupEquivBool :
    (identityLattice 1).IsometryGroup ≃ Bool where
  toFun U := decide (U.1 0 0 = (-1 : ℤ))
  invFun b := if b then
      ⟨(-1 : Matrix (Fin 1) (Fin 1) ℤ), by
        constructor
        · rw [Matrix.isUnit_iff_isUnit_det]
          simp
        · ext i j
          fin_cases i
          fin_cases j
          simp [identityLattice]
      ⟩
    else
      ⟨(1 : Matrix (Fin 1) (Fin 1) ℤ), by
        constructor
        · exact isUnit_one
        · simp [identityLattice]
      ⟩
  left_inv U := by
    apply Subtype.ext
    ext i j
    fin_cases i
    fin_cases j
    have hentry : U.1 0 0 * U.1 0 0 = 1 := by
      have h := congrFun (congrFun U.2.2 0) 0
      simpa [identityLattice, Matrix.mul_apply, dotProduct, Fin.sum_univ_one] using h
    rcases (mul_self_eq_one_iff.mp hentry) with hpos | hneg
    · simp [hpos]
    · simp [hneg]
  right_inv b := by
    cases b <;> simp

/-- The explicit stabilizer count for the rank-one identity lattice. -/
theorem identityLattice_one_isometryGroup_card :
    Fintype.card (identityLattice 1).IsometryGroup = 2 := by
  classical
  rw [← Fintype.card_bool]
  exact Fintype.card_congr identityLatticeOneIsometryGroupEquivBool

/-- The rank-one identity seed has ordinary genus mass `1 / 2`. -/
theorem identityLattice_one_ordinaryGenusMass :
    (identityLattice 1).ordinaryGenusMass = (1 / 2 : ℚ) := by
  classical
  unfold ordinaryGenusMass
  have hterm : ∀ C : (identityLattice 1).genus,
      ((Fintype.card (genusClassRepresentative (identityLattice 1) C).IsometryGroup : ℚ)⁻¹) =
        (1 / 2 : ℚ) := by
    intro C
    have hsame := genusClassRepresentative_isSameGenus (identityLattice 1) C
    have hMu : (genusClassRepresentative (identityLattice 1) C).IsUnimodular := by
      exact (genusClassRepresentative (identityLattice 1) C).isUnimodular_of_isSameGenus
        (isSameGenus_symm hsame) (identityLattice_isUnimodular 1)
    have hIso := isGlobalIsometry_identityLattice_one_of_isUnimodular
      (genusClassRepresentative (identityLattice 1) C) hMu
    have hcard := isometryGroup_card_eq_of_isGlobalIsometry hIso
    rw [hcard, identityLattice_one_isometryGroup_card]
    norm_num
  calc
    (∑ C : (identityLattice 1).genus,
        ((Fintype.card (genusClassRepresentative (identityLattice 1) C).IsometryGroup : ℚ)⁻¹))
        = ∑ C : (identityLattice 1).genus, (1 / 2 : ℚ) := by
          exact Finset.sum_congr rfl (fun C _ => hterm C)
    _ = (Fintype.card (identityLattice 1).genus : ℚ) * (1 / 2 : ℚ) := by
          simp
    _ = 1 / 2 := by
          rw [identityLattice_one_genus_card]
          norm_num

/-- Real-cast form of the rank-one identity ordinary genus mass endpoint. -/
theorem identityLattice_one_ordinaryGenusMass_real :
    (((identityLattice 1).ordinaryGenusMass : ℚ) : ℝ) = (1 / 2 : ℝ) := by
  rw [identityLattice_one_ordinaryGenusMass]
  norm_num

/-- The rank-one identity ordinary genus mass matches the Type I constant. -/
theorem identityLattice_one_ordinaryGenusMass_eq_typeIConstant :
    (identityLattice 1).ordinaryGenusMass = typeIConstant 1 := by
  rw [identityLattice_one_ordinaryGenusMass, typeIConstant_one]

/-- Real-cast form of the rank-one identity Type I ordinary mass endpoint. -/
theorem identityLattice_one_ordinaryGenusMass_real_eq_typeIConstant :
    (((identityLattice 1).ordinaryGenusMass : ℚ) : ℝ) = (typeIConstant 1 : ℝ) := by
  exact_mod_cast identityLattice_one_ordinaryGenusMass_eq_typeIConstant

/-- Every classically unimodular rank-one lattice has the Type I ordinary genus mass. -/
theorem ordinaryGenusMass_eq_typeIConstant_of_rank_one_isUnimodular
    (L : PositiveDefiniteIntegralLattice 1) (hL : L.IsUnimodular) :
    L.ordinaryGenusMass = typeIConstant 1 := by
  rw [ordinaryGenusMass_eq_of_isGlobalIsometry
    (isGlobalIsometry_identityLattice_one_of_isUnimodular L hL)]
  exact identityLattice_one_ordinaryGenusMass_eq_typeIConstant

/-- Real-cast form of the rank-one Type I ordinary genus mass endpoint under classical
unimodularity. -/
theorem ordinaryGenusMass_real_eq_typeIConstant_of_rank_one_isUnimodular
    (L : PositiveDefiniteIntegralLattice 1) (hL : L.IsUnimodular) :
    ((L.ordinaryGenusMass : ℚ) : ℝ) = (typeIConstant 1 : ℝ) := by
  exact_mod_cast ordinaryGenusMass_eq_typeIConstant_of_rank_one_isUnimodular L hL

/-- The rank-one Type I ordinary mass: a lattice with `pairingDeterminant = 1` and a
vector of odd norm has mass `typeIConstant 1`.  The odd-vector hypothesis is redundant in
rank one; it keeps the statement parallel to the Type I theorems in higher rank. -/
theorem ordinaryGenusMass_eq_typeIConstant_of_rank_one
    (L : PositiveDefiniteIntegralLattice 1) (hdet : L.pairingDeterminant = 1)
    (_hodd : ∃ x : Fin 1 → ℤ, Odd (L.quadForm x)) :
    L.ordinaryGenusMass = typeIConstant 1 :=
  ordinaryGenusMass_eq_typeIConstant_of_rank_one_isUnimodular L
    (by simpa [IsUnimodular] using hdet)

/-- Real-cast form of the theorem-facing rank-one Type I ordinary-mass endpoint. -/
theorem ordinaryGenusMass_real_eq_typeIConstant_of_rank_one
    (L : PositiveDefiniteIntegralLattice 1) (hdet : L.pairingDeterminant = 1)
    (hodd : ∃ x : Fin 1 → ℤ, Odd (L.quadForm x)) :
    ((L.ordinaryGenusMass : ℚ) : ℝ) = (typeIConstant 1 : ℝ) := by
  exact_mod_cast ordinaryGenusMass_eq_typeIConstant_of_rank_one L hdet hodd

/-- Codes for the signed permutation matrices in the rank-two identity stabilizer. -/
private inductive RankTwoSignedPermutationCode where
  | diagPP | diagPN | diagNP | diagNN | swapPP | swapPN | swapNP | swapNN
  deriving DecidableEq, Fintype

/-- The signed permutation matrix attached to a rank-two stabilizer code. -/
private def RankTwoSignedPermutationCode.matrix :
    RankTwoSignedPermutationCode → Matrix (Fin 2) (Fin 2) ℤ
  | .diagPP => !![(1 : ℤ), 0; 0, 1]
  | .diagPN => !![(1 : ℤ), 0; 0, -1]
  | .diagNP => !![(-1 : ℤ), 0; 0, 1]
  | .diagNN => !![(-1 : ℤ), 0; 0, -1]
  | .swapPP => !![0, (1 : ℤ); 1, 0]
  | .swapPN => !![0, (-1 : ℤ); 1, 0]
  | .swapNP => !![0, (1 : ℤ); -1, 0]
  | .swapNN => !![0, (-1 : ℤ); -1, 0]

private lemma matrix_fin_two_ext {M N : Matrix (Fin 2) (Fin 2) ℤ}
    (h00 : M 0 0 = N 0 0) (h01 : M 0 1 = N 0 1)
    (h10 : M 1 0 = N 1 0) (h11 : M 1 1 = N 1 1) : M = N := by
  ext i j
  fin_cases i
  · fin_cases j <;> assumption
  · fin_cases j <;> assumption

/-- Determinant of a rank-two lattice Gram matrix, expanded in coordinates. -/
theorem rank_two_pairingMatrix_det_eq (L : PositiveDefiniteIntegralLattice 2) :
    L.pairingMatrix.det =
      L.pairingMatrix 0 0 * L.pairingMatrix 1 1 -
        L.pairingMatrix 0 1 * L.pairingMatrix 1 0 := by
  rw [Matrix.det_fin_two]

/-- Determinant of a rank-two lattice Gram matrix, using symmetry. -/
theorem rank_two_pairingMatrix_det_eq_symm (L : PositiveDefiniteIntegralLattice 2) :
    L.pairingMatrix.det =
      L.pairingMatrix 0 0 * L.pairingMatrix 1 1 -
        L.pairingMatrix 0 1 * L.pairingMatrix 0 1 := by
  rw [rank_two_pairingMatrix_det_eq]
  have h10 : L.pairingMatrix 1 0 = L.pairingMatrix 0 1 := by
    exact (L.form_symm.apply 1 0).symm
  rw [h10]

/-- The rank-two determinant-one condition in binary quadratic form coordinates. -/
theorem rank_two_pairingMatrix_det_eq_one_of_isUnimodular
    (L : PositiveDefiniteIntegralLattice 2) (hL : L.IsUnimodular) :
    L.pairingMatrix 0 0 * L.pairingMatrix 1 1 -
        L.pairingMatrix 0 1 * L.pairingMatrix 0 1 = 1 := by
  have hdet : L.pairingMatrix.det = 1 := by
    simpa [IsUnimodular, pairingDeterminant] using hL
  rw [rank_two_pairingMatrix_det_eq_symm] at hdet
  exact hdet

/-- The first diagonal entry of a rank-two lattice Gram matrix is positive. -/
theorem rank_two_pairingMatrix_zero_zero_pos (L : PositiveDefiniteIntegralLattice 2) :
    0 < L.pairingMatrix 0 0 := by
  have hpos := L.quadForm_pos (x := Pi.single (0 : Fin 2) 1) (by
    intro hzero
    have hentry := congrFun hzero 0
    simp at hentry)
  simpa [quadForm_single_one] using hpos

/-- The second diagonal entry of a rank-two lattice Gram matrix is positive. -/
theorem rank_two_pairingMatrix_one_one_pos (L : PositiveDefiniteIntegralLattice 2) :
    0 < L.pairingMatrix 1 1 := by
  have hpos := L.quadForm_pos (x := Pi.single (1 : Fin 2) 1) (by
    intro hzero
    have hentry := congrFun hzero 1
    simp at hentry)
  simpa [quadForm_single_one] using hpos

/-- If the first diagonal entry is one, the first coordinate vector is a norm-one vector. -/
theorem exists_rank_two_quadForm_eq_one_of_pairingMatrix_zero_zero_eq_one
    (L : PositiveDefiniteIntegralLattice 2) (hdiag : L.pairingMatrix 0 0 = 1) :
    ∃ x : Fin 2 → ℤ, L.quadForm x = 1 := by
  refine ⟨Pi.single (0 : Fin 2) 1, ?_⟩
  simp [quadForm_single_one, hdiag]

/-- If the second diagonal entry is one, the second coordinate vector is a norm-one vector. -/
theorem exists_rank_two_quadForm_eq_one_of_pairingMatrix_one_one_eq_one
    (L : PositiveDefiniteIntegralLattice 2) (hdiag : L.pairingMatrix 1 1 = 1) :
    ∃ x : Fin 2 → ℤ, L.quadForm x = 1 := by
  refine ⟨Pi.single (1 : Fin 2) 1, ?_⟩
  simp [quadForm_single_one, hdiag]

/-- Without a norm-one vector, the first diagonal entry is strictly bigger than one. -/
theorem rank_two_one_lt_pairingMatrix_zero_zero_of_no_norm_one
    (L : PositiveDefiniteIntegralLattice 2) (hno : ¬ ∃ x : Fin 2 → ℤ, L.quadForm x = 1) :
    1 < L.pairingMatrix 0 0 := by
  by_contra hnot
  have hle : L.pairingMatrix 0 0 ≤ 1 := le_of_not_gt hnot
  have hpos := rank_two_pairingMatrix_zero_zero_pos L
  have hge : (1 : ℤ) ≤ L.pairingMatrix 0 0 := by omega
  have hdiag : L.pairingMatrix 0 0 = 1 := le_antisymm hle hge
  exact hno (exists_rank_two_quadForm_eq_one_of_pairingMatrix_zero_zero_eq_one L hdiag)

/-- Without a norm-one vector, the second diagonal entry is strictly bigger than one. -/
theorem rank_two_one_lt_pairingMatrix_one_one_of_no_norm_one
    (L : PositiveDefiniteIntegralLattice 2) (hno : ¬ ∃ x : Fin 2 → ℤ, L.quadForm x = 1) :
    1 < L.pairingMatrix 1 1 := by
  by_contra hnot
  have hle : L.pairingMatrix 1 1 ≤ 1 := le_of_not_gt hnot
  have hpos := rank_two_pairingMatrix_one_one_pos L
  have hge : (1 : ℤ) ≤ L.pairingMatrix 1 1 := by omega
  have hdiag : L.pairingMatrix 1 1 = 1 := le_antisymm hle hge
  exact hno (exists_rank_two_quadForm_eq_one_of_pairingMatrix_one_one_eq_one L hdiag)

/-- The two entries in the first row of a determinant-one rank-two Gram matrix are coprime. -/
theorem isCoprime_rank_two_pairingMatrix_zero_row_of_isUnimodular
    (L : PositiveDefiniteIntegralLattice 2) (hL : L.IsUnimodular) :
    IsCoprime (L.pairingMatrix 0 0) (L.pairingMatrix 0 1) := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  have hd_nonneg : 0 ≤
      ((Int.gcd (L.pairingMatrix 0 0) (L.pairingMatrix 0 1) : ℕ) : ℤ) := by
    exact Int.natCast_nonneg _
  have hd_left :
      ((Int.gcd (L.pairingMatrix 0 0) (L.pairingMatrix 0 1) : ℕ) : ℤ) ∣
        L.pairingMatrix 0 0 := by
    exact Int.gcd_dvd_left (L.pairingMatrix 0 0) (L.pairingMatrix 0 1)
  have hd_right :
      ((Int.gcd (L.pairingMatrix 0 0) (L.pairingMatrix 0 1) : ℕ) : ℤ) ∣
        L.pairingMatrix 0 1 := by
    exact Int.gcd_dvd_right (L.pairingMatrix 0 0) (L.pairingMatrix 0 1)
  have hd_det :
      ((Int.gcd (L.pairingMatrix 0 0) (L.pairingMatrix 0 1) : ℕ) : ℤ) ∣
      L.pairingMatrix 0 0 * L.pairingMatrix 1 1 -
        L.pairingMatrix 0 1 * L.pairingMatrix 0 1 := by
    exact dvd_sub (dvd_mul_of_dvd_left hd_left _) (dvd_mul_of_dvd_left hd_right _)
  have hd_one :
      ((Int.gcd (L.pairingMatrix 0 0) (L.pairingMatrix 0 1) : ℕ) : ℤ) ∣ 1 := by
    simpa [rank_two_pairingMatrix_det_eq_one_of_isUnimodular L hL] using hd_det
  have hd_eq :
      ((Int.gcd (L.pairingMatrix 0 0) (L.pairingMatrix 0 1) : ℕ) : ℤ) = 1 :=
    Int.eq_one_of_dvd_one hd_nonneg hd_one
  exact_mod_cast hd_eq

/-- The two entries in the second row of a determinant-one rank-two Gram matrix are coprime. -/
theorem isCoprime_rank_two_pairingMatrix_one_row_of_isUnimodular
    (L : PositiveDefiniteIntegralLattice 2) (hL : L.IsUnimodular) :
    IsCoprime (L.pairingMatrix 0 1) (L.pairingMatrix 1 1) := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  have hd_nonneg : 0 ≤
      ((Int.gcd (L.pairingMatrix 0 1) (L.pairingMatrix 1 1) : ℕ) : ℤ) := by
    exact Int.natCast_nonneg _
  have hd_left :
      ((Int.gcd (L.pairingMatrix 0 1) (L.pairingMatrix 1 1) : ℕ) : ℤ) ∣
        L.pairingMatrix 0 1 := by
    exact Int.gcd_dvd_left (L.pairingMatrix 0 1) (L.pairingMatrix 1 1)
  have hd_right :
      ((Int.gcd (L.pairingMatrix 0 1) (L.pairingMatrix 1 1) : ℕ) : ℤ) ∣
        L.pairingMatrix 1 1 := by
    exact Int.gcd_dvd_right (L.pairingMatrix 0 1) (L.pairingMatrix 1 1)
  have hd_det :
      ((Int.gcd (L.pairingMatrix 0 1) (L.pairingMatrix 1 1) : ℕ) : ℤ) ∣
      L.pairingMatrix 0 0 * L.pairingMatrix 1 1 -
        L.pairingMatrix 0 1 * L.pairingMatrix 0 1 := by
    exact dvd_sub (dvd_mul_of_dvd_right hd_right _) (dvd_mul_of_dvd_left hd_left _)
  have hd_one :
      ((Int.gcd (L.pairingMatrix 0 1) (L.pairingMatrix 1 1) : ℕ) : ℤ) ∣ 1 := by
    simpa [rank_two_pairingMatrix_det_eq_one_of_isUnimodular L hL] using hd_det
  have hd_eq :
      ((Int.gcd (L.pairingMatrix 0 1) (L.pairingMatrix 1 1) : ℕ) : ℤ) = 1 :=
    Int.eq_one_of_dvd_one hd_nonneg hd_one
  exact_mod_cast hd_eq

/-- The rank-two shear sending the second basis vector to `e₁ - q • e₀`. -/
def rankTwoShearMatrix (q : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![(1 : ℤ), -q; 0, 1]

/-- The determinant of a rank-two integral shear is one. -/
theorem rankTwoShearMatrix_det (q : ℤ) :
    (rankTwoShearMatrix q).det = 1 := by
  rw [Matrix.det_fin_two]
  simp [rankTwoShearMatrix]

/-- A rank-two integral shear is a unit matrix. -/
theorem rankTwoShearMatrix_isUnit (q : ℤ) : IsUnit (rankTwoShearMatrix q) := by
  rw [Matrix.isUnit_iff_isUnit_det, rankTwoShearMatrix_det]
  exact isUnit_one

/-- The `(0,0)` entry after a rank-two shear. -/
theorem rankTwoShearMatrix_gram00 (L : PositiveDefiniteIntegralLattice 2) (q : ℤ) :
    ((rankTwoShearMatrix q)ᵀ * L.pairingMatrix * rankTwoShearMatrix q) 0 0 =
      L.pairingMatrix 0 0 := by
  simp [rankTwoShearMatrix, Matrix.mul_apply, Fin.sum_univ_two]

/-- The `(0,1)` entry after a rank-two shear. -/
theorem rankTwoShearMatrix_gram01 (L : PositiveDefiniteIntegralLattice 2) (q : ℤ) :
    ((rankTwoShearMatrix q)ᵀ * L.pairingMatrix * rankTwoShearMatrix q) 0 1 =
      L.pairingMatrix 0 1 - q * L.pairingMatrix 0 0 := by
  simp [rankTwoShearMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- The `(1,0)` entry after a rank-two shear. -/
theorem rankTwoShearMatrix_gram10 (L : PositiveDefiniteIntegralLattice 2) (q : ℤ) :
    ((rankTwoShearMatrix q)ᵀ * L.pairingMatrix * rankTwoShearMatrix q) 1 0 =
      L.pairingMatrix 0 1 - q * L.pairingMatrix 0 0 := by
  have h10 : L.pairingMatrix 1 0 = L.pairingMatrix 0 1 := by
    exact (L.form_symm.apply 1 0).symm
  simp [rankTwoShearMatrix, Matrix.mul_apply, Fin.sum_univ_two, h10]
  ring

/-- The `(1,1)` entry after a rank-two shear. -/
theorem rankTwoShearMatrix_gram11 (L : PositiveDefiniteIntegralLattice 2) (q : ℤ) :
    ((rankTwoShearMatrix q)ᵀ * L.pairingMatrix * rankTwoShearMatrix q) 1 1 =
      L.pairingMatrix 1 1 - 2 * q * L.pairingMatrix 0 1 + q * q * L.pairingMatrix 0 0 := by
  have h10 : L.pairingMatrix 1 0 = L.pairingMatrix 0 1 := by
    exact (L.form_symm.apply 1 0).symm
  simp [rankTwoShearMatrix, Matrix.mul_apply, Fin.sum_univ_two, h10]
  ring

/-- The determinant is unchanged by a rank-two shear congruence. -/
theorem rankTwoShearMatrix_gram_det (L : PositiveDefiniteIntegralLattice 2) (q : ℤ) :
    ((rankTwoShearMatrix q)ᵀ * L.pairingMatrix * rankTwoShearMatrix q).det =
      L.pairingMatrix.det := by
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, rankTwoShearMatrix_det]
  ring

/-- The binary determinant identity behind the rank-two shear descent. -/
theorem rank_two_shear_det_identity (a b c q : ℤ) :
    a * (c - 2 * q * b + q * q * a) - (b - q * a) * (b - q * a) =
      a * c - b * b := by
  ring

/-- An integer is within half a positive modulus of some multiple of that modulus. -/
theorem exists_int_nearest_multiple (a b : ℤ) (ha : 0 < a) :
    ∃ q : ℤ, 2 * |b - q * a| ≤ a := by
  let q0 : ℤ := b / a
  let r : ℤ := b % a
  have hdecomp : q0 * a + r = b := by
    dsimp [q0, r]
    exact Int.ediv_mul_add_emod b a
  have hr_nonneg : 0 ≤ r := by
    dsimp [r]
    exact Int.emod_nonneg b (ne_of_gt ha)
  have hr_lt : r < a := by
    dsimp [r]
    exact Int.emod_lt_of_pos b ha
  by_cases hsmall : 2 * r ≤ a
  · refine ⟨q0, ?_⟩
    have hres : b - q0 * a = r := by omega
    rw [hres, abs_of_nonneg hr_nonneg]
    exact hsmall
  · refine ⟨q0 + 1, ?_⟩
    have hlarge : a < 2 * r := by omega
    have hres : b - (q0 + 1) * a = r - a := by
      ring_nf
      omega
    have hnonpos : r - a ≤ 0 := by omega
    rw [hres, abs_of_nonpos hnonpos]
    omega

/-- The sheared lower-right coefficient is positive under the determinant-one binary identity. -/
theorem rank_two_shear_lower_right_pos_of_det_one
    {a b c q : ℤ} (ha : 0 < a) (hdet : a * c - b * b = 1) :
    0 < c - 2 * q * b + q * q * a := by
  let r : ℤ := b - q * a
  let c' : ℤ := c - 2 * q * b + q * q * a
  have hid : a * c' - r * r = 1 := by
    dsimp [r, c']
    rw [show a * (c - 2 * q * b + q * q * a) - (b - q * a) * (b - q * a) =
        a * c - b * b by ring]
    exact hdet
  have hr_nonneg : 0 ≤ r * r := mul_self_nonneg r
  have hmul_pos : 0 < a * c' := by nlinarith
  have hc'_pos : 0 < c' := by
    by_contra hnot
    have hc'_le : c' ≤ 0 := le_of_not_gt hnot
    have hmul_nonpos : a * c' ≤ 0 := by nlinarith
    omega
  exact hc'_pos

/-- A nearest-multiple shear strictly lowers the second diagonal coefficient when `1 < a`. -/
theorem rank_two_shear_lower_right_lt_of_nearest
    {a b c q : ℤ} (ha : 1 < a) (hdet : a * c - b * b = 1)
    (hbound : 2 * |b - q * a| ≤ a) :
    c - 2 * q * b + q * q * a < a := by
  let r : ℤ := b - q * a
  let c' : ℤ := c - 2 * q * b + q * q * a
  have hid : a * c' - r * r = 1 := by
    dsimp [r, c']
    rw [show a * (c - 2 * q * b + q * q * a) - (b - q * a) * (b - q * a) =
        a * c - b * b by ring]
    exact hdet
  have ha_pos : 0 < a := by omega
  have hsq_bound : 4 * (r * r) ≤ a * a := by
    have hx_nonneg : 0 ≤ 2 * |r| := by positivity
    have ha_nonneg : 0 ≤ a := by omega
    have hsq := mul_le_mul hbound hbound hx_nonneg ha_nonneg
    rw [show (2 * |r|) * (2 * |r|) = 4 * (|r| * |r|) by ring] at hsq
    rw [abs_mul_abs_self] at hsq
    nlinarith
  have hlt_sq : r * r + 1 < a * a := by
    have ha_ge_two : 2 ≤ a := by omega
    have hr_sq_nonneg : 0 ≤ r * r := mul_self_nonneg r
    nlinarith
  have hmul : a * c' = r * r + 1 := by omega
  have hmul_lt : a * c' < a * a := by omega
  exact (Int.mul_lt_mul_left ha_pos).mp hmul_lt

/-- The determinant-one binary descent package supplied by a nearest-multiple shear. -/
theorem exists_rank_two_shear_lower_right_pos_lt
    {a b c : ℤ} (ha : 1 < a) (hdet : a * c - b * b = 1) :
    ∃ q : ℤ, 0 < c - 2 * q * b + q * q * a ∧
      c - 2 * q * b + q * q * a < a := by
  have ha_pos : 0 < a := by omega
  rcases exists_int_nearest_multiple a b ha_pos with ⟨q, hq⟩
  exact ⟨q, rank_two_shear_lower_right_pos_of_det_one ha_pos hdet,
    rank_two_shear_lower_right_lt_of_nearest ha hdet hq⟩


/-- The rank-two coordinate-swap matrix. -/
def rankTwoSwapMatrix : Matrix (Fin 2) (Fin 2) ℤ :=
  !![0, (1 : ℤ); 1, 0]

/-- The determinant of the rank-two coordinate-swap matrix. -/
theorem rankTwoSwapMatrix_det : rankTwoSwapMatrix.det = -1 := by
  rw [Matrix.det_fin_two]
  simp [rankTwoSwapMatrix]

/-- The rank-two coordinate-swap matrix is a unit. -/
theorem rankTwoSwapMatrix_isUnit : IsUnit rankTwoSwapMatrix := by
  rw [Matrix.isUnit_iff_isUnit_det, rankTwoSwapMatrix_det]
  norm_num

/-- Swapping coordinates moves the lower-right entry to the upper-left entry. -/
theorem rankTwoSwapMatrix_conj00 (M : Matrix (Fin 2) (Fin 2) ℤ) :
    (rankTwoSwapMatrixᵀ * M * rankTwoSwapMatrix) 0 0 = M 1 1 := by
  simp [rankTwoSwapMatrix, Matrix.mul_apply, Fin.sum_univ_two]

/-- A rank-two shear followed by a coordinate swap. -/
def rankTwoShearSwapMatrix (q : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  rankTwoShearMatrix q * rankTwoSwapMatrix

/-- The shear-swap matrix is a unit. -/
theorem rankTwoShearSwapMatrix_isUnit (q : ℤ) : IsUnit (rankTwoShearSwapMatrix q) := by
  dsimp [rankTwoShearSwapMatrix]
  exact IsUnit.mul (rankTwoShearMatrix_isUnit q) rankTwoSwapMatrix_isUnit

/-- The leading Gram entry after shear-swap is the sheared lower-right coefficient. -/
theorem rankTwoShearSwapMatrix_gram00 (L : PositiveDefiniteIntegralLattice 2) (q : ℤ) :
    ((rankTwoShearSwapMatrix q)ᵀ * L.pairingMatrix * rankTwoShearSwapMatrix q) 0 0 =
      L.pairingMatrix 1 1 - 2 * q * L.pairingMatrix 0 1 + q * q * L.pairingMatrix 0 0 := by
  rw [rankTwoShearSwapMatrix]
  rw [Matrix.transpose_mul]
  rw [show rankTwoSwapMatrixᵀ * (rankTwoShearMatrix q)ᵀ * L.pairingMatrix *
        (rankTwoShearMatrix q * rankTwoSwapMatrix) =
      rankTwoSwapMatrixᵀ * ((rankTwoShearMatrix q)ᵀ * L.pairingMatrix * rankTwoShearMatrix q) *
        rankTwoSwapMatrix by
    simp [Matrix.mul_assoc]]
  rw [rankTwoSwapMatrix_conj00]
  exact rankTwoShearMatrix_gram11 L q

/-- The determinant is unchanged by a shear-swap congruence. -/
theorem rankTwoShearSwapMatrix_gram_det (L : PositiveDefiniteIntegralLattice 2) (q : ℤ) :
    ((rankTwoShearSwapMatrix q)ᵀ * L.pairingMatrix * rankTwoShearSwapMatrix q).det =
      L.pairingMatrix.det := by
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  have hdet_sq : (rankTwoShearSwapMatrix q).det * (rankTwoShearSwapMatrix q).det = 1 := by
    dsimp [rankTwoShearSwapMatrix]
    rw [Matrix.det_mul, rankTwoShearMatrix_det, rankTwoSwapMatrix_det]
    norm_num
  calc
    (rankTwoShearSwapMatrix q).det * L.pairingMatrix.det * (rankTwoShearSwapMatrix q).det =
        ((rankTwoShearSwapMatrix q).det * (rankTwoShearSwapMatrix q).det) * L.pairingMatrix.det := by
          ring
    _ = 1 * L.pairingMatrix.det := by rw [hdet_sq]
    _ = L.pairingMatrix.det := by ring

/-- If a rank-two determinant-one lattice has no norm-one vector, a shear-swap
congruence produces a positive determinant-one form with strictly smaller leading diagonal. -/
theorem exists_rank_two_shear_swap_pairingMatrix_zero_zero_pos_lt
    (L : PositiveDefiniteIntegralLattice 2) (hL : L.IsUnimodular)
    (hno : ¬ ∃ x : Fin 2 → ℤ, L.quadForm x = 1) :
    ∃ q : ℤ,
      0 < ((rankTwoShearSwapMatrix q)ᵀ * L.pairingMatrix * rankTwoShearSwapMatrix q) 0 0 ∧
      ((rankTwoShearSwapMatrix q)ᵀ * L.pairingMatrix * rankTwoShearSwapMatrix q) 0 0 <
        L.pairingMatrix 0 0 ∧
      ((rankTwoShearSwapMatrix q)ᵀ * L.pairingMatrix * rankTwoShearSwapMatrix q).det = 1 ∧
      IsUnit (rankTwoShearSwapMatrix q) := by
  have ha : 1 < L.pairingMatrix 0 0 :=
    rank_two_one_lt_pairingMatrix_zero_zero_of_no_norm_one L hno
  have hdet := rank_two_pairingMatrix_det_eq_one_of_isUnimodular L hL
  rcases exists_rank_two_shear_lower_right_pos_lt ha hdet with ⟨q, hpos, hlt⟩
  refine ⟨q, ?_, ?_, ?_, rankTwoShearSwapMatrix_isUnit q⟩
  · rw [rankTwoShearSwapMatrix_gram00]
    exact hpos
  · rw [rankTwoShearSwapMatrix_gram00]
    exact hlt
  · rw [rankTwoShearSwapMatrix_gram_det]
    simpa [IsUnimodular, pairingDeterminant] using hL


/-- A positive determinant-one integral binary form represents one.

This is the Euclidean descent behind the rank-two norm-one endpoint. The descent is by the
positive leading coefficient; the recursive step is the nearest-residue shear followed by a
coordinate swap. -/
theorem binary_det_one_repr_one :
    ∀ a b c : ℤ, 0 < a → a * c - b * b = 1 →
      ∃ x y : ℤ, a * x * x + 2 * b * x * y + c * y * y = 1 := by
  intro a0 b0 c0 ha0 hdet0
  let P : ℕ → Prop := fun n =>
    ∀ a b c : ℤ, Int.toNat a = n → 0 < a → a * c - b * b = 1 →
      ∃ x y : ℤ, a * x * x + 2 * b * x * y + c * y * y = 1
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro a b c hnat ha hdet
      by_cases ha_one : a = 1
      · refine ⟨1, 0, ?_⟩
        simp [ha_one]
      · have ha_gt : 1 < a := by omega
        rcases exists_rank_two_shear_lower_right_pos_lt (a := a) (b := b) (c := c) ha_gt hdet with
          ⟨q, hcpos, hclt⟩
        let r : ℤ := b - q * a
        let cnew : ℤ := c - 2 * q * b + q * q * a
        have hdet_new : cnew * a - r * r = 1 := by
          dsimp [cnew, r]
          rw [show (c - 2 * q * b + q * q * a) * a - (b - q * a) * (b - q * a) =
              a * c - b * b by ring]
          exact hdet
        have hnat_lt : Int.toNat cnew < n := by
          rw [← hnat]
          exact (Int.toNat_lt_toNat ha).mpr hclt
        rcases ih (Int.toNat cnew) hnat_lt cnew r a rfl hcpos hdet_new with ⟨x, y, hxy⟩
        refine ⟨y - q * x, x, ?_⟩
        dsimp [cnew, r] at hxy
        rw [← hxy]
        ring
  exact hP (Int.toNat a0) a0 b0 c0 rfl ha0 hdet0

/-- Every classically unimodular rank-two lattice has a norm-one vector. -/
theorem exists_rank_two_quadForm_eq_one_of_isUnimodular
    (L : PositiveDefiniteIntegralLattice 2) (hL : L.IsUnimodular) :
    ∃ x : Fin 2 → ℤ, L.quadForm x = 1 := by
  have ha : 0 < L.pairingMatrix 0 0 := rank_two_pairingMatrix_zero_zero_pos L
  have hdet := rank_two_pairingMatrix_det_eq_one_of_isUnimodular L hL
  rcases binary_det_one_repr_one (L.pairingMatrix 0 0) (L.pairingMatrix 0 1) (L.pairingMatrix 1 1) ha hdet with
    ⟨x0, x1, hrep⟩
  refine ⟨fun i => if i = 0 then x0 else x1, ?_⟩
  rw [L.quadForm_eq_dotProduct]
  have h10 : L.pairingMatrix 1 0 = L.pairingMatrix 0 1 := by
    exact (L.form_symm.apply 1 0).symm
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h10]
  rw [← hrep]
  ring

/-- The rank-two matrix with prescribed first and second columns. -/
def rankTwoColumnMatrix (x y : Fin 2 → ℤ) : Matrix (Fin 2) (Fin 2) ℤ
  | i, j => if j = 0 then x i else y i

@[simp] theorem rankTwoColumnMatrix_apply_zero (x y : Fin 2 → ℤ) (i : Fin 2) :
    rankTwoColumnMatrix x y i 0 = x i := by
  simp [rankTwoColumnMatrix]

@[simp] theorem rankTwoColumnMatrix_apply_one (x y : Fin 2 → ℤ) (i : Fin 2) :
    rankTwoColumnMatrix x y i 1 = y i := by
  simp [rankTwoColumnMatrix]

/-- Determinant of the rank-two matrix with columns `x` and `y`. -/
theorem rankTwoColumnMatrix_det (x y : Fin 2 → ℤ) :
    (rankTwoColumnMatrix x y).det = x 0 * y 1 - y 0 * x 1 := by
  rw [Matrix.det_fin_two]
  simp [rankTwoColumnMatrix]

/-- A rank-two column matrix of determinant one is a unit. -/
theorem rankTwoColumnMatrix_isUnit_of_det_one {x y : Fin 2 → ℤ}
    (hdet : x 0 * y 1 - y 0 * x 1 = 1) : IsUnit (rankTwoColumnMatrix x y) := by
  rw [Matrix.isUnit_iff_isUnit_det, rankTwoColumnMatrix_det, hdet]
  exact isUnit_one

/-- A primitive binary vector admits an integral determinant-one complement. -/
theorem exists_rankTwoColumnMatrix_det_one_of_isCoprime (x : Fin 2 → ℤ)
    (hcop : IsCoprime (x 0) (x 1)) :
    ∃ y : Fin 2 → ℤ, x 0 * y 1 - y 0 * x 1 = 1 := by
  refine ⟨fun i => if i = 0 then -Int.gcdB (x 0) (x 1) else Int.gcdA (x 0) (x 1), ?_⟩
  have hgcd : (x 0).gcd (x 1) = 1 := Int.isCoprime_iff_gcd_eq_one.mp hcop
  have hbez := Int.gcd_eq_gcd_ab (x 0) (x 1)
  rw [hgcd] at hbez
  calc
    x 0 * (if (1 : Fin 2) = 0 then -Int.gcdB (x 0) (x 1) else Int.gcdA (x 0) (x 1)) -
        (if (0 : Fin 2) = 0 then -Int.gcdB (x 0) (x 1) else Int.gcdA (x 0) (x 1)) * x 1 =
        x 0 * Int.gcdA (x 0) (x 1) + x 1 * Int.gcdB (x 0) (x 1) := by
      norm_num
      ring
    _ = 1 := hbez.symm

/-- A primitive binary vector can be completed to an integral unit matrix as
the first column. -/
theorem exists_rankTwoColumnMatrix_isUnit_of_isCoprime (x : Fin 2 → ℤ)
    (hcop : IsCoprime (x 0) (x 1)) :
    ∃ y : Fin 2 → ℤ, IsUnit (rankTwoColumnMatrix x y) := by
  rcases exists_rankTwoColumnMatrix_det_one_of_isCoprime x hcop with ⟨y, hy⟩
  exact ⟨y, rankTwoColumnMatrix_isUnit_of_det_one hy⟩

/-- The `(0,0)` Gram entry of a rank-two column matrix. -/
lemma rankTwoColumnMatrix_gram00 (L : PositiveDefiniteIntegralLattice 2) (x y : Fin 2 → ℤ) :
    ((rankTwoColumnMatrix x y)ᵀ * L.pairingMatrix * rankTwoColumnMatrix x y) 0 0 =
      L.quadForm x := by
  rw [L.quadForm_eq_dotProduct]
  simp [rankTwoColumnMatrix, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- The `(0,1)` Gram entry of a rank-two column matrix. -/
lemma rankTwoColumnMatrix_gram01 (L : PositiveDefiniteIntegralLattice 2) (x y : Fin 2 → ℤ) :
    ((rankTwoColumnMatrix x y)ᵀ * L.pairingMatrix * rankTwoColumnMatrix x y) 0 1 =
      dotProduct x (L.pairingMatrix.mulVec y) := by
  simp [rankTwoColumnMatrix, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- The `(1,0)` Gram entry of a rank-two column matrix. -/
lemma rankTwoColumnMatrix_gram10 (L : PositiveDefiniteIntegralLattice 2) (x y : Fin 2 → ℤ) :
    ((rankTwoColumnMatrix x y)ᵀ * L.pairingMatrix * rankTwoColumnMatrix x y) 1 0 =
      dotProduct y (L.pairingMatrix.mulVec x) := by
  simp [rankTwoColumnMatrix, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- The `(1,1)` Gram entry of a rank-two column matrix. -/
lemma rankTwoColumnMatrix_gram11 (L : PositiveDefiniteIntegralLattice 2) (x y : Fin 2 → ℤ) :
    ((rankTwoColumnMatrix x y)ᵀ * L.pairingMatrix * rankTwoColumnMatrix x y) 1 1 =
      L.quadForm y := by
  rw [L.quadForm_eq_dotProduct]
  simp [rankTwoColumnMatrix, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- A primitive norm-one vector in a classically unimodular rank-two lattice
can be completed and sheared to an orthonormal integral basis. -/
theorem identityLattice_two_isGlobalIsometry_of_primitive_norm_one
    (L : PositiveDefiniteIntegralLattice 2) (hL : L.IsUnimodular) (x : Fin 2 → ℤ)
    (hcop : IsCoprime (x 0) (x 1)) (hx : L.quadForm x = 1) :
    (identityLattice 2).IsGlobalIsometry L := by
  rcases exists_rankTwoColumnMatrix_det_one_of_isCoprime x hcop with ⟨y, hdetxy⟩
  let k : ℤ := dotProduct x (L.pairingMatrix.mulVec y)
  let z : Fin 2 → ℤ := fun i => y i - k * x i
  have hdetxz : x 0 * z 1 - z 0 * x 1 = 1 := by
    dsimp [z]
    rw [show x 0 * (y 1 - k * x 1) - (y 0 - k * x 0) * x 1 =
        x 0 * y 1 - y 0 * x 1 by ring]
    exact hdetxy
  let U : Matrix (Fin 2) (Fin 2) ℤ := rankTwoColumnMatrix x z
  let M : Matrix (Fin 2) (Fin 2) ℤ := Uᵀ * L.pairingMatrix * U
  have hxx : dotProduct x (L.pairingMatrix.mulVec x) = 1 := by
    simpa [L.quadForm_eq_dotProduct] using hx
  have hxz_dot : dotProduct x (L.pairingMatrix.mulVec z) = 0 := by
    have hlin : dotProduct x (L.pairingMatrix.mulVec z) =
        dotProduct x (L.pairingMatrix.mulVec y) - k * dotProduct x (L.pairingMatrix.mulVec x) := by
      dsimp [z]
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      ring
    rw [hlin, hxx]
    dsimp [k]
    ring
  have hzx_dot_eq : dotProduct z (L.pairingMatrix.mulVec x) = dotProduct x (L.pairingMatrix.mulVec z) := by
    dsimp [z]
    have h10 : L.pairingMatrix 1 0 = L.pairingMatrix 0 1 := by
      exact (L.form_symm.apply 1 0).symm
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h10]
    ring
  have hM00 : M 0 0 = 1 := by
    dsimp [M, U]
    rw [rankTwoColumnMatrix_gram00, hx]
  have hM01 : M 0 1 = 0 := by
    dsimp [M, U]
    rw [rankTwoColumnMatrix_gram01]
    exact hxz_dot
  have hM10 : M 1 0 = 0 := by
    dsimp [M, U]
    rw [rankTwoColumnMatrix_gram10, hzx_dot_eq]
    exact hxz_dot
  have hdetF : L.pairingMatrix.det = 1 := by
    simpa [IsUnimodular, pairingDeterminant] using hL
  have hdetU : U.det = 1 := by
    dsimp [U]
    rw [rankTwoColumnMatrix_det]
    exact hdetxz
  have hdetM : M.det = 1 := by
    dsimp [M]
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hdetU, hdetF]
    norm_num
  have hM11 : M 1 1 = 1 := by
    have hdetM' := hdetM
    rw [Matrix.det_fin_two, hM00, hM01, hM10] at hdetM'
    simpa using hdetM'
  refine ⟨U, ?_, ?_⟩
  · dsimp [U]
    exact rankTwoColumnMatrix_isUnit_of_det_one hdetxz
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [M, identityLattice] at hM00 hM01 hM10 hM11 ⊢
    · exact hM00
    · exact hM01
    · exact hM10
    · exact hM11

/-- The classification-oriented direction of
`identityLattice_two_isGlobalIsometry_of_primitive_norm_one`. -/
theorem isGlobalIsometry_identityLattice_two_of_primitive_norm_one
    (L : PositiveDefiniteIntegralLattice 2) (hL : L.IsUnimodular) (x : Fin 2 → ℤ)
    (hcop : IsCoprime (x 0) (x 1)) (hx : L.quadForm x = 1) :
    L.IsGlobalIsometry (identityLattice 2) :=
  isGlobalIsometry_symm
    (identityLattice_two_isGlobalIsometry_of_primitive_norm_one L hL x hcop hx)

/-- In a rank-two integral lattice, any vector of norm one is primitive.  Thus
the rank-two classification input can ask only for norm-one vectors. -/
theorem isCoprime_of_rank_two_quadForm_eq_one
    (L : PositiveDefiniteIntegralLattice 2) {x : Fin 2 → ℤ} (hx : L.quadForm x = 1) :
    IsCoprime (x 0) (x 1) := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  let d : ℤ := ((x 0).gcd (x 1) : ℤ)
  have hd_nonneg : 0 ≤ d := by
    dsimp [d]
    exact Int.natCast_nonneg _
  have hd0 : d ∣ x 0 := by
    dsimp [d]
    exact Int.gcd_dvd_left (x 0) (x 1)
  have hd1 : d ∣ x 1 := by
    dsimp [d]
    exact Int.gcd_dvd_right (x 0) (x 1)
  have hdq : d ∣ L.quadForm x := by
    rw [L.quadForm_eq_dotProduct]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    exact dvd_add (dvd_mul_of_dvd_left hd0 _) (dvd_mul_of_dvd_left hd1 _)
  have hd_one : d ∣ (1 : ℤ) := by
    simpa [hx] using hdq
  exact Int.ofNat_inj.mp (Int.eq_one_of_dvd_one hd_nonneg hd_one)

/-- A norm-one vector in a classically unimodular rank-two lattice can be
completed and sheared to an orthonormal integral basis.  This is the primitive
classification reduction with primitivity supplied by
`isCoprime_of_rank_two_quadForm_eq_one`. -/
theorem identityLattice_two_isGlobalIsometry_of_norm_one
    (L : PositiveDefiniteIntegralLattice 2) (hL : L.IsUnimodular) (x : Fin 2 → ℤ)
    (hx : L.quadForm x = 1) :
    (identityLattice 2).IsGlobalIsometry L :=
  identityLattice_two_isGlobalIsometry_of_primitive_norm_one L hL x
    (isCoprime_of_rank_two_quadForm_eq_one L hx) hx

/-- The classification-oriented direction of
`identityLattice_two_isGlobalIsometry_of_norm_one`. -/
theorem isGlobalIsometry_identityLattice_two_of_norm_one
    (L : PositiveDefiniteIntegralLattice 2) (hL : L.IsUnimodular) (x : Fin 2 → ℤ)
    (hx : L.quadForm x = 1) :
    L.IsGlobalIsometry (identityLattice 2) :=
  isGlobalIsometry_symm
    (identityLattice_two_isGlobalIsometry_of_norm_one L hL x hx)

/-- Every classically unimodular rank-two lattice is globally isometric to the
rank-two identity lattice. -/
theorem isGlobalIsometry_identityLattice_two_of_isUnimodular
    (L : PositiveDefiniteIntegralLattice 2) (hL : L.IsUnimodular) :
    L.IsGlobalIsometry (identityLattice 2) := by
  rcases exists_rank_two_quadForm_eq_one_of_isUnimodular L hL with ⟨x, hx⟩
  exact isGlobalIsometry_identityLattice_two_of_norm_one L hL x hx

/-- The inverse orientation of
`isGlobalIsometry_identityLattice_two_of_isUnimodular`. -/
theorem identityLattice_two_isGlobalIsometry_of_isUnimodular
    (L : PositiveDefiniteIntegralLattice 2) (hL : L.IsUnimodular) :
    (identityLattice 2).IsGlobalIsometry L :=
  isGlobalIsometry_symm (isGlobalIsometry_identityLattice_two_of_isUnimodular L hL)

/-- The rank-two identity genus has a single ordinary class.  The proof uses
the determinant-one binary descent. -/
theorem identityLattice_two_genus_subsingleton :
    Subsingleton (identityLattice 2).genus :=
  identityLattice_two_genus_subsingleton_of_rank_two_unimodular_classification
    (fun L hL => isGlobalIsometry_identityLattice_two_of_isUnimodular L hL)

/-- The rank-two identity genus has cardinality one. -/
theorem identityLattice_two_genus_card :
    Fintype.card (identityLattice 2).genus = 1 :=
  identityLattice_two_genus_card_of_rank_two_unimodular_classification
    (fun L hL => isGlobalIsometry_identityLattice_two_of_isUnimodular L hL)

/-- Existence of a primitive norm-one vector in every classically unimodular
rank-two lattice collapses the rank-two identity genus to one ordinary class. -/
theorem identityLattice_two_genus_subsingleton_of_rank_two_primitive_norm_one
    (hprim : ∀ L : PositiveDefiniteIntegralLattice 2, L.IsUnimodular →
      ∃ x : Fin 2 → ℤ, IsCoprime (x 0) (x 1) ∧ L.quadForm x = 1) :
    Subsingleton (identityLattice 2).genus := by
  refine identityLattice_two_genus_subsingleton_of_rank_two_unimodular_classification ?_
  intro M hM
  rcases hprim M hM with ⟨x, hcop, hx⟩
  exact isGlobalIsometry_identityLattice_two_of_primitive_norm_one M hM x hcop hx

/-- Existence of a primitive norm-one vector in every classically unimodular
rank-two lattice gives one ordinary class in the rank-two identity genus. -/
theorem identityLattice_two_genus_card_of_rank_two_primitive_norm_one
    (hprim : ∀ L : PositiveDefiniteIntegralLattice 2, L.IsUnimodular →
      ∃ x : Fin 2 → ℤ, IsCoprime (x 0) (x 1) ∧ L.quadForm x = 1) :
    Fintype.card (identityLattice 2).genus = 1 := by
  haveI := identityLattice_two_genus_subsingleton_of_rank_two_primitive_norm_one hprim
  rw [Fintype.card_eq_one_iff]
  exact ⟨⟨(identityLattice 2).globalIsometryClass, mem_genus_self _⟩,
    fun C => Subsingleton.elim C _⟩

/-- Existence of a norm-one vector in every classically unimodular rank-two
lattice collapses the rank-two identity genus to one ordinary class; primitivity
follows automatically from `isCoprime_of_rank_two_quadForm_eq_one`. -/
theorem identityLattice_two_genus_subsingleton_of_rank_two_norm_one
    (hnorm : ∀ L : PositiveDefiniteIntegralLattice 2, L.IsUnimodular →
      ∃ x : Fin 2 → ℤ, L.quadForm x = 1) :
    Subsingleton (identityLattice 2).genus := by
  refine identityLattice_two_genus_subsingleton_of_rank_two_unimodular_classification ?_
  intro M hM
  rcases hnorm M hM with ⟨x, hx⟩
  exact isGlobalIsometry_identityLattice_two_of_norm_one M hM x hx

/-- Existence of a norm-one vector in every classically unimodular rank-two
lattice gives one ordinary class in the rank-two identity genus. -/
theorem identityLattice_two_genus_card_of_rank_two_norm_one
    (hnorm : ∀ L : PositiveDefiniteIntegralLattice 2, L.IsUnimodular →
      ∃ x : Fin 2 → ℤ, L.quadForm x = 1) :
    Fintype.card (identityLattice 2).genus = 1 := by
  haveI := identityLattice_two_genus_subsingleton_of_rank_two_norm_one hnorm
  rw [Fintype.card_eq_one_iff]
  exact ⟨⟨(identityLattice 2).globalIsometryClass, mem_genus_self _⟩,
    fun C => Subsingleton.elim C _⟩

private lemma RankTwoSignedPermutationCode.matrix_injective :
    Function.Injective RankTwoSignedPermutationCode.matrix := by
  intro c d h
  cases c <;> cases d <;> simp [RankTwoSignedPermutationCode.matrix] at h ⊢

private lemma RankTwoSignedPermutationCode.isometry (c : RankTwoSignedPermutationCode) :
    (identityLattice 2).IsIsometry c.matrix := by
  cases c <;> constructor
  all_goals
    first
    | rw [Matrix.isUnit_iff_isUnit_det]
      decide
    | ext i j
      fin_cases i
      · fin_cases j <;> norm_num [identityLattice, Matrix.mul_apply,
          RankTwoSignedPermutationCode.matrix]
      · fin_cases j <;> norm_num [identityLattice, Matrix.mul_apply,
          RankTwoSignedPermutationCode.matrix]

private lemma int_sq_add_sq_eq_one_cases {a b : ℤ} (h : a * a + b * b = 1) :
    (a = 1 ∧ b = 0) ∨ (a = -1 ∧ b = 0) ∨ (a = 0 ∧ b = 1) ∨ (a = 0 ∧ b = -1) := by
  have ha_nonneg : 0 ≤ a * a := mul_self_nonneg a
  have hb_nonneg : 0 ≤ b * b := mul_self_nonneg b
  have ha_le : a * a ≤ 1 := by nlinarith
  have hb_le : b * b ≤ 1 := by nlinarith
  have ha_low : -1 ≤ a := by nlinarith [sq_nonneg (a + 1)]
  have ha_high : a ≤ 1 := by nlinarith [sq_nonneg (a - 1)]
  have hb_low : -1 ≤ b := by nlinarith [sq_nonneg (b + 1)]
  have hb_high : b ≤ 1 := by nlinarith [sq_nonneg (b - 1)]
  interval_cases a <;> interval_cases b <;> omega

private lemma exists_rankTwoSignedPermutationCode_of_identityLattice_two_isometry
    (U : (identityLattice 2).IsometryGroup) :
    ∃ c : RankTwoSignedPermutationCode, U.1 = c.matrix := by
  have hcol0 : U.1 0 0 * U.1 0 0 + U.1 1 0 * U.1 1 0 = 1 := by
    have h := congrFun (congrFun U.2.2 0) 0
    simpa [identityLattice, Matrix.mul_apply, dotProduct, Fin.sum_univ_two] using h
  have hcol1 : U.1 0 1 * U.1 0 1 + U.1 1 1 * U.1 1 1 = 1 := by
    have h := congrFun (congrFun U.2.2 1) 1
    simpa [identityLattice, Matrix.mul_apply, dotProduct, Fin.sum_univ_two] using h
  have hdot : U.1 0 0 * U.1 0 1 + U.1 1 0 * U.1 1 1 = 0 := by
    have h := congrFun (congrFun U.2.2 0) 1
    simpa [identityLattice, Matrix.mul_apply, dotProduct, Fin.sum_univ_two] using h
  rcases int_sq_add_sq_eq_one_cases hcol0 with h0 | h0 | h0 | h0
  · rcases h0 with ⟨h00, h10⟩
    rcases int_sq_add_sq_eq_one_cases hcol1 with h1 | h1 | h1 | h1
    · rcases h1 with ⟨h01, h11⟩
      simp [h00, h10, h01, h11] at hdot
    · rcases h1 with ⟨h01, h11⟩
      simp [h00, h10, h01, h11] at hdot
    · rcases h1 with ⟨h01, h11⟩
      exact ⟨RankTwoSignedPermutationCode.diagPP,
        matrix_fin_two_ext h00 h01 h10 h11⟩
    · rcases h1 with ⟨h01, h11⟩
      exact ⟨RankTwoSignedPermutationCode.diagPN,
        matrix_fin_two_ext h00 h01 h10 h11⟩
  · rcases h0 with ⟨h00, h10⟩
    rcases int_sq_add_sq_eq_one_cases hcol1 with h1 | h1 | h1 | h1
    · rcases h1 with ⟨h01, h11⟩
      simp [h00, h10, h01, h11] at hdot
    · rcases h1 with ⟨h01, h11⟩
      simp [h00, h10, h01, h11] at hdot
    · rcases h1 with ⟨h01, h11⟩
      exact ⟨RankTwoSignedPermutationCode.diagNP,
        matrix_fin_two_ext h00 h01 h10 h11⟩
    · rcases h1 with ⟨h01, h11⟩
      exact ⟨RankTwoSignedPermutationCode.diagNN,
        matrix_fin_two_ext h00 h01 h10 h11⟩
  · rcases h0 with ⟨h00, h10⟩
    rcases int_sq_add_sq_eq_one_cases hcol1 with h1 | h1 | h1 | h1
    · rcases h1 with ⟨h01, h11⟩
      exact ⟨RankTwoSignedPermutationCode.swapPP,
        matrix_fin_two_ext h00 h01 h10 h11⟩
    · rcases h1 with ⟨h01, h11⟩
      exact ⟨RankTwoSignedPermutationCode.swapPN,
        matrix_fin_two_ext h00 h01 h10 h11⟩
    · rcases h1 with ⟨h01, h11⟩
      simp [h00, h10, h01, h11] at hdot
    · rcases h1 with ⟨h01, h11⟩
      simp [h00, h10, h01, h11] at hdot
  · rcases h0 with ⟨h00, h10⟩
    rcases int_sq_add_sq_eq_one_cases hcol1 with h1 | h1 | h1 | h1
    · rcases h1 with ⟨h01, h11⟩
      exact ⟨RankTwoSignedPermutationCode.swapNP,
        matrix_fin_two_ext h00 h01 h10 h11⟩
    · rcases h1 with ⟨h01, h11⟩
      exact ⟨RankTwoSignedPermutationCode.swapNN,
        matrix_fin_two_ext h00 h01 h10 h11⟩
    · rcases h1 with ⟨h01, h11⟩
      simp [h00, h10, h01, h11] at hdot
    · rcases h1 with ⟨h01, h11⟩
      simp [h00, h10, h01, h11] at hdot

/-- The ordinary isometry group of the rank-two identity seed is the signed
permutation group on two basis vectors. -/
private def identityLatticeTwoIsometryGroupEquivCode :
    (identityLattice 2).IsometryGroup ≃ RankTwoSignedPermutationCode where
  toFun U := Classical.choose (exists_rankTwoSignedPermutationCode_of_identityLattice_two_isometry U)
  invFun c := ⟨c.matrix, RankTwoSignedPermutationCode.isometry c⟩
  left_inv U := by
    apply Subtype.ext
    exact (Classical.choose_spec
      (exists_rankTwoSignedPermutationCode_of_identityLattice_two_isometry U)).symm
  right_inv c := by
    apply RankTwoSignedPermutationCode.matrix_injective
    exact (Classical.choose_spec
      (exists_rankTwoSignedPermutationCode_of_identityLattice_two_isometry
        (⟨c.matrix, RankTwoSignedPermutationCode.isometry c⟩))).symm

/-- The explicit stabilizer count for the rank-two identity lattice. -/
theorem identityLattice_two_isometryGroup_card :
    Fintype.card (identityLattice 2).IsometryGroup = 8 := by
  rw [Fintype.card_congr identityLatticeTwoIsometryGroupEquivCode]
  decide

/-- If the rank-two identity genus has one ordinary class, its ordinary mass is `1 / 8`. -/
theorem identityLattice_two_ordinaryGenusMass_of_genus_subsingleton
    (hgenus : Subsingleton (identityLattice 2).genus) :
    (identityLattice 2).ordinaryGenusMass = (1 / 8 : ℚ) := by
  classical
  letI := hgenus
  let C0 : (identityLattice 2).genus :=
    ⟨(identityLattice 2).globalIsometryClass, mem_genus_self _⟩
  have hcard_genus : Fintype.card (identityLattice 2).genus = 1 := by
    rw [Fintype.card_eq_one_iff]
    exact ⟨C0, fun C => Subsingleton.elim C C0⟩
  unfold ordinaryGenusMass
  have hterm : ∀ C : (identityLattice 2).genus,
      ((Fintype.card (genusClassRepresentative (identityLattice 2) C).IsometryGroup : ℚ)⁻¹) =
        (1 / 8 : ℚ) := by
    intro C
    have hC : C = C0 := Subsingleton.elim C C0
    have hrep := genusClassRepresentative_globalIsometryClass (identityLattice 2) C
    have hclass : (genusClassRepresentative (identityLattice 2) C).globalIsometryClass =
        (identityLattice 2).globalIsometryClass := by
      rw [← hrep, hC]
    have hIso := isGlobalIsometry_of_globalIsometryClass_eq hclass
    have hcard := isometryGroup_card_eq_of_isGlobalIsometry hIso
    rw [hcard, identityLattice_two_isometryGroup_card]
    norm_num
  calc
    (∑ C : (identityLattice 2).genus,
        ((Fintype.card (genusClassRepresentative (identityLattice 2) C).IsometryGroup : ℚ)⁻¹))
        = ∑ C : (identityLattice 2).genus, (1 / 8 : ℚ) := by
          exact Finset.sum_congr rfl (fun C _ => hterm C)
    _ = (Fintype.card (identityLattice 2).genus : ℚ) * (1 / 8 : ℚ) := by
          simp
    _ = 1 / 8 := by
          rw [hcard_genus]
          norm_num

/-- If the rank-two identity genus has one ordinary class, its ordinary mass matches the Type I
constant. -/
theorem identityLattice_two_ordinaryGenusMass_eq_typeIConstant_of_genus_subsingleton
    (hgenus : Subsingleton (identityLattice 2).genus) :
    (identityLattice 2).ordinaryGenusMass = typeIConstant 2 := by
  rw [identityLattice_two_ordinaryGenusMass_of_genus_subsingleton hgenus,
    typeIConstant_two]

/-- A global classification of classically unimodular rank-two lattices gives
the rank-two identity ordinary mass endpoint. -/
theorem identityLattice_two_ordinaryGenusMass_of_rank_two_unimodular_classification
    (hclass : ∀ L : PositiveDefiniteIntegralLattice 2, L.IsUnimodular → L.IsGlobalIsometry (identityLattice 2)) :
    (identityLattice 2).ordinaryGenusMass = (1 / 8 : ℚ) :=
  identityLattice_two_ordinaryGenusMass_of_genus_subsingleton
    (identityLattice_two_genus_subsingleton_of_rank_two_unimodular_classification hclass)

/-- A global classification of classically unimodular rank-two lattices gives
the rank-two Type I ordinary mass endpoint. -/
theorem identityLattice_two_ordinaryGenusMass_eq_typeIConstant_of_rank_two_unimodular_classification
    (hclass : ∀ L : PositiveDefiniteIntegralLattice 2, L.IsUnimodular → L.IsGlobalIsometry (identityLattice 2)) :
    (identityLattice 2).ordinaryGenusMass = typeIConstant 2 :=
  identityLattice_two_ordinaryGenusMass_eq_typeIConstant_of_genus_subsingleton
    (identityLattice_two_genus_subsingleton_of_rank_two_unimodular_classification hclass)

/-- Existence of a primitive norm-one vector in every classically unimodular
rank-two lattice gives the rank-two identity ordinary mass endpoint. -/
theorem identityLattice_two_ordinaryGenusMass_of_rank_two_primitive_norm_one
    (hprim : ∀ L : PositiveDefiniteIntegralLattice 2, L.IsUnimodular →
      ∃ x : Fin 2 → ℤ, IsCoprime (x 0) (x 1) ∧ L.quadForm x = 1) :
    (identityLattice 2).ordinaryGenusMass = (1 / 8 : ℚ) :=
  identityLattice_two_ordinaryGenusMass_of_genus_subsingleton
    (identityLattice_two_genus_subsingleton_of_rank_two_primitive_norm_one hprim)

/-- Existence of a primitive norm-one vector in every classically unimodular
rank-two lattice gives the rank-two identity Type I ordinary mass endpoint. -/
theorem identityLattice_two_ordinaryGenusMass_eq_typeIConstant_of_rank_two_primitive_norm_one
    (hprim : ∀ L : PositiveDefiniteIntegralLattice 2, L.IsUnimodular →
      ∃ x : Fin 2 → ℤ, IsCoprime (x 0) (x 1) ∧ L.quadForm x = 1) :
    (identityLattice 2).ordinaryGenusMass = typeIConstant 2 :=
  identityLattice_two_ordinaryGenusMass_eq_typeIConstant_of_genus_subsingleton
    (identityLattice_two_genus_subsingleton_of_rank_two_primitive_norm_one hprim)

/-- Existence of a norm-one vector in every classically unimodular rank-two
lattice gives the rank-two identity ordinary mass endpoint. -/
theorem identityLattice_two_ordinaryGenusMass_of_rank_two_norm_one
    (hnorm : ∀ L : PositiveDefiniteIntegralLattice 2, L.IsUnimodular →
      ∃ x : Fin 2 → ℤ, L.quadForm x = 1) :
    (identityLattice 2).ordinaryGenusMass = (1 / 8 : ℚ) :=
  identityLattice_two_ordinaryGenusMass_of_genus_subsingleton
    (identityLattice_two_genus_subsingleton_of_rank_two_norm_one hnorm)

/-- Existence of a norm-one vector in every classically unimodular rank-two
lattice gives the rank-two identity Type I ordinary mass endpoint. -/
theorem identityLattice_two_ordinaryGenusMass_eq_typeIConstant_of_rank_two_norm_one
    (hnorm : ∀ L : PositiveDefiniteIntegralLattice 2, L.IsUnimodular →
      ∃ x : Fin 2 → ℤ, L.quadForm x = 1) :
    (identityLattice 2).ordinaryGenusMass = typeIConstant 2 :=
  identityLattice_two_ordinaryGenusMass_eq_typeIConstant_of_genus_subsingleton
    (identityLattice_two_genus_subsingleton_of_rank_two_norm_one hnorm)

/-- A supplied global classification of classically unimodular rank-two lattices
transports the rank-two Type I ordinary mass endpoint to every classically
unimodular rank-two lattice. -/
theorem ordinaryGenusMass_eq_typeIConstant_of_rank_two_unimodular_classification
    (hclass : ∀ L : PositiveDefiniteIntegralLattice 2, L.IsUnimodular → L.IsGlobalIsometry (identityLattice 2))
    (L : PositiveDefiniteIntegralLattice 2) (hL : L.IsUnimodular) :
    L.ordinaryGenusMass = typeIConstant 2 := by
  rw [ordinaryGenusMass_eq_of_isGlobalIsometry (hclass L hL)]
  exact identityLattice_two_ordinaryGenusMass_eq_typeIConstant_of_rank_two_unimodular_classification
    hclass

/-- Existence of a primitive norm-one vector in every classically unimodular
rank-two lattice is enough to prove the rank-two Type I ordinary mass endpoint.
This isolates the remaining rank-two classification input without proving it. -/
theorem ordinaryGenusMass_eq_typeIConstant_of_rank_two_primitive_norm_one
    (hprim : ∀ L : PositiveDefiniteIntegralLattice 2, L.IsUnimodular →
      ∃ x : Fin 2 → ℤ, IsCoprime (x 0) (x 1) ∧ L.quadForm x = 1)
    (L : PositiveDefiniteIntegralLattice 2) (hL : L.IsUnimodular) :
    L.ordinaryGenusMass = typeIConstant 2 := by
  rcases hprim L hL with ⟨x, hcop, hx⟩
  rw [ordinaryGenusMass_eq_of_isGlobalIsometry
    (isGlobalIsometry_identityLattice_two_of_primitive_norm_one L hL x hcop hx)]
  exact identityLattice_two_ordinaryGenusMass_eq_typeIConstant_of_rank_two_primitive_norm_one
    hprim

/-- Existence of a norm-one vector in every classically unimodular rank-two
lattice is enough to prove the rank-two Type I ordinary mass endpoint.
Primitivity follows automatically from norm one. -/
theorem ordinaryGenusMass_eq_typeIConstant_of_rank_two_norm_one
    (hnorm : ∀ L : PositiveDefiniteIntegralLattice 2, L.IsUnimodular →
      ∃ x : Fin 2 → ℤ, L.quadForm x = 1)
    (L : PositiveDefiniteIntegralLattice 2) (hL : L.IsUnimodular) :
    L.ordinaryGenusMass = typeIConstant 2 := by
  rcases hnorm L hL with ⟨x, hx⟩
  rw [ordinaryGenusMass_eq_of_isGlobalIsometry
    (isGlobalIsometry_identityLattice_two_of_norm_one L hL x hx)]
  exact identityLattice_two_ordinaryGenusMass_eq_typeIConstant_of_rank_two_norm_one hnorm

/-- The rank-two identity-lattice ordinary mass is `1/8`. -/
theorem identityLattice_two_ordinaryGenusMass :
    (identityLattice 2).ordinaryGenusMass = (1 / 8 : ℚ) :=
  identityLattice_two_ordinaryGenusMass_of_genus_subsingleton
    identityLattice_two_genus_subsingleton

/-- Real-cast form of the rank-two identity-lattice ordinary mass. -/
theorem identityLattice_two_ordinaryGenusMass_real :
    (((identityLattice 2).ordinaryGenusMass : ℚ) : ℝ) = (1 / 8 : ℝ) := by
  rw [identityLattice_two_ordinaryGenusMass]
  norm_num

/-- The rank-two identity-lattice ordinary mass equals `typeIConstant 2`. -/
theorem identityLattice_two_ordinaryGenusMass_eq_typeIConstant :
    (identityLattice 2).ordinaryGenusMass = typeIConstant 2 :=
  by rw [identityLattice_two_ordinaryGenusMass, typeIConstant_two]

/-- Real-cast form of the rank-two identity-lattice Type I ordinary mass. -/
theorem identityLattice_two_ordinaryGenusMass_real_eq_typeIConstant :
    (((identityLattice 2).ordinaryGenusMass : ℚ) : ℝ) = (typeIConstant 2 : ℝ) := by
  exact_mod_cast identityLattice_two_ordinaryGenusMass_eq_typeIConstant

/-- Every classically unimodular rank-two lattice has the Type I ordinary genus mass. -/
theorem ordinaryGenusMass_eq_typeIConstant_of_rank_two_isUnimodular
    (L : PositiveDefiniteIntegralLattice 2) (hL : L.IsUnimodular) :
    L.ordinaryGenusMass = typeIConstant 2 :=
  ordinaryGenusMass_eq_typeIConstant_of_rank_two_norm_one
    (fun M hM => exists_rank_two_quadForm_eq_one_of_isUnimodular M hM) L hL

/-- Real-cast form of the rank-two Type I ordinary genus mass endpoint under classical
unimodularity. -/
theorem ordinaryGenusMass_real_eq_typeIConstant_of_rank_two_isUnimodular
    (L : PositiveDefiniteIntegralLattice 2) (hL : L.IsUnimodular) :
    ((L.ordinaryGenusMass : ℚ) : ℝ) = (typeIConstant 2 : ℝ) := by
  exact_mod_cast ordinaryGenusMass_eq_typeIConstant_of_rank_two_isUnimodular L hL

/-- The rank-two Type I ordinary mass: a lattice with `pairingDeterminant = 1` and a
vector of odd norm has mass `typeIConstant 2`.  The odd-vector hypothesis follows from
the classical results on unimodular rank-two lattices and is not used in the proof; it
makes the statement match the Type I theorems in other ranks. -/
theorem ordinaryGenusMass_eq_typeIConstant_of_rank_two
    (L : PositiveDefiniteIntegralLattice 2) (hdet : L.pairingDeterminant = 1)
    (_hodd : ∃ x : Fin 2 → ℤ, Odd (L.quadForm x)) :
    L.ordinaryGenusMass = typeIConstant 2 :=
  ordinaryGenusMass_eq_typeIConstant_of_rank_two_isUnimodular L
    (by simpa [IsUnimodular] using hdet)

/-- Real-cast form of the theorem-facing rank-two Type I ordinary-mass endpoint. -/
theorem ordinaryGenusMass_real_eq_typeIConstant_of_rank_two
    (L : PositiveDefiniteIntegralLattice 2) (hdet : L.pairingDeterminant = 1)
    (hodd : ∃ x : Fin 2 → ℤ, Odd (L.quadForm x)) :
    ((L.ordinaryGenusMass : ℚ) : ℝ) = (typeIConstant 2 : ℝ) := by
  exact_mod_cast ordinaryGenusMass_eq_typeIConstant_of_rank_two L hdet hodd

end PositiveDefiniteIntegralLattice
