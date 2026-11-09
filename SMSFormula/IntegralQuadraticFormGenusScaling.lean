import SMSFormula.IntegralQuadraticFormEvenCharacterCompatibility

/-!
# Genus scaling for converted integral forms

For a stored integral quadratic matrix `F`, the scaled integral model of its
integral-quadratic-form conversion stores `2F`.  This module begins the
comparison of the complete genera by packaging the scaling and proving
the crucial dyadic descent: every integral matrix locally isometric to `2F`
over `Z_2` has even entries.
-/

open Matrix

noncomputable section

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- Scale the stored integral quadratic matrix by two. -/
def scaleByTwo (L : PositiveDefiniteIntegralLattice n) : PositiveDefiniteIntegralLattice n where
  pairingMatrix := (2 : ℤ) • L.pairingMatrix
  form_symm := by
    ext i j
    change 2 * L.pairingMatrix j i = 2 * L.pairingMatrix i j
    rw [(L.form_symm.apply j i).symm]
  form_posDef := by
    apply Matrix.PosDef.of_dotProduct_mulVec_pos
    · ext i j
      simp only [Matrix.conjTranspose_apply, Matrix.map_apply,
        Matrix.smul_apply, star_trivial, smul_eq_mul, Int.cast_mul,
        Int.cast_ofNat]
      rw [(L.form_symm.apply j i).symm]
    · intro x hx
      have h := L.form_posDef.dotProduct_mulVec_pos hx
      have hmap :
          (((2 : ℤ) • L.pairingMatrix).map (Int.cast : ℤ → ℝ)) =
            (2 : ℝ) • L.pairingMatrix.map (Int.cast : ℤ → ℝ) := by
        ext i j
        simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
          Int.cast_mul, Int.cast_ofNat]
      rw [hmap, Matrix.smul_mulVec, dotProduct_smul]
      exact mul_pos (by norm_num) h

/-- The scaled integral model of the conversion to an integral quadratic form is literally the
old lattice scaled by two. -/
theorem toIntegralQuadraticForm_latticeOfPolarForm_eq_scaleByTwo
    (L : PositiveDefiniteIntegralLattice n) :
    L.toIntegralQuadraticForm.latticeOfPolarForm = L.scaleByTwo := by
  rfl

/-- Solve a local congruence to a twice-scaled form for the middle matrix.
This retains an explicit factor of two over the dyadic integers. -/
lemma pairingMatrix_padic_eq_two_smul_of_scaleByTwo_isLocallyIsometricAt_two
    (L M : PositiveDefiniteIntegralLattice n)
    (h : L.scaleByTwo.IsLocallyIsometricAt M 2) :
    ∃ B : Matrix (Fin n) (Fin n) ℤ_[2],
      M.pairingMatrix_padic 2 = (2 : ℤ_[2]) • B := by
  rcases h with ⟨U, hUunit, hU⟩
  have hUdet : IsUnit U.det := by
    rwa [Matrix.isUnit_iff_isUnit_det] at hUunit
  have hU_mul_inv : U * U⁻¹ = 1 := Matrix.mul_nonsing_inv U hUdet
  have hleft : (U⁻¹).transpose * U.transpose = 1 := by
    rw [← Matrix.transpose_mul, hU_mul_inv, Matrix.transpose_one]
  let B : Matrix (Fin n) (Fin n) ℤ_[2] :=
    (U⁻¹).transpose * L.pairingMatrix_padic 2 * U⁻¹
  refine ⟨B, ?_⟩
  have hscale :
      L.scaleByTwo.pairingMatrix_padic 2 =
        (2 : ℤ_[2]) • L.pairingMatrix_padic 2 := by
    ext i j
    simp only [scaleByTwo, pairingMatrix_padic, Matrix.map_apply,
      Matrix.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_ofNat]
  rw [hscale] at hU
  have hsolve :
      (U⁻¹).transpose *
          (U.transpose * M.pairingMatrix_padic 2 * U) * U⁻¹ =
        M.pairingMatrix_padic 2 := by
    calc
      (U⁻¹).transpose *
          (U.transpose * M.pairingMatrix_padic 2 * U) * U⁻¹ =
          ((U⁻¹).transpose * U.transpose) * M.pairingMatrix_padic 2 *
            (U * U⁻¹) := by
        simp [Matrix.mul_assoc]
      _ = M.pairingMatrix_padic 2 := by
        rw [hleft, hU_mul_inv]
        simp
  calc
    M.pairingMatrix_padic 2 =
        (U⁻¹).transpose *
          (U.transpose * M.pairingMatrix_padic 2 * U) * U⁻¹ := hsolve.symm
    _ = (U⁻¹).transpose *
          ((2 : ℤ_[2]) • L.pairingMatrix_padic 2) * U⁻¹ := by
      rw [hU]
    _ = (2 : ℤ_[2]) • B := by
      simp [B]

/-- The crucial dyadic descent: every integral quadratic matrix locally
isometric to `2F` at two has even entries. -/
theorem pairingMatrix_even_of_scaleByTwo_isLocallyIsometricAt_two
    (L M : PositiveDefiniteIntegralLattice n)
    (h : L.scaleByTwo.IsLocallyIsometricAt M 2) :
    ∀ i j, Even (M.pairingMatrix i j) := by
  rcases pairingMatrix_padic_eq_two_smul_of_scaleByTwo_isLocallyIsometricAt_two
      L M h with ⟨B, hB⟩
  intro i j
  have hentry := congr_fun (congr_fun hB i) j
  have hdiv : (2 : ℤ_[2]) ^ 1 ∣ ((M.pairingMatrix i j : ℤ) : ℤ_[2]) := by
    refine ⟨B i j, ?_⟩
    simpa [pairingMatrix_padic, Matrix.smul_apply, smul_eq_mul] using hentry
  have hz :=
    (padicInt_primePow_dvd_intCast_iff_zmod_eq_zero 2 1
      (M.pairingMatrix i j)).mp hdiv
  have hdvd : (2 : ℤ) ∣ M.pairingMatrix i j := by
    have hdvd' :
        ((primePowModulus 2 1 : ℕ) : ℤ) ∣ M.pairingMatrix i j :=
      by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        exact hz
    simpa [primePowModulus] using hdvd'
  exact even_iff_two_dvd.mpr hdvd

/-- Every representative in the genus of `2F` has an entrywise-even stored
matrix. -/
theorem pairingMatrix_even_of_isSameGenus_scaleByTwo
    (L M : PositiveDefiniteIntegralLattice n) (h : L.scaleByTwo.IsSameGenus M) :
    ∀ i j, Even (M.pairingMatrix i j) := by
  exact pairingMatrix_even_of_scaleByTwo_isLocallyIsometricAt_two L M (h.1 2)

/-! ## Canonical halving of an even integral matrix -/

/-- The entrywise integral half of an even matrix. -/
def halfFormMatrix (M : PositiveDefiniteIntegralLattice n) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => M.pairingMatrix i j / 2

/-- Halve an entrywise-even stored integral quadratic matrix. -/
def halveOfEven (M : PositiveDefiniteIntegralLattice n)
    (hEven : ∀ i j, Even (M.pairingMatrix i j)) : PositiveDefiniteIntegralLattice n where
  pairingMatrix := M.halfFormMatrix
  form_symm := by
    ext i j
    change M.halfFormMatrix j i = M.halfFormMatrix i j
    simp only [halfFormMatrix]
    rw [(M.form_symm.apply j i).symm]
  form_posDef := by
    apply Matrix.PosDef.of_dotProduct_mulVec_pos
    · ext i j
      simp only [Matrix.conjTranspose_apply, Matrix.map_apply,
        halfFormMatrix, star_trivial]
      rw [(M.form_symm.apply j i).symm]
    · intro x hx
      have hMpos := M.form_posDef.dotProduct_mulVec_pos hx
      have hmatrix :
          (2 : ℝ) •
              (M.halfFormMatrix.map (Int.cast : ℤ → ℝ)) =
            M.pairingMatrix.map (Int.cast : ℤ → ℝ) := by
        ext i j
        simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
          halfFormMatrix]
        change (2 : ℝ) * (M.pairingMatrix i j / 2 : ℤ) =
          (M.pairingMatrix i j : ℝ)
        norm_cast
        rw [mul_comm, Int.ediv_mul_cancel
          (even_iff_two_dvd.mp (hEven i j))]
      have hdot :
          2 * (star x ⬝ᵥ
              (M.halfFormMatrix.map (Int.cast : ℤ → ℝ)) *ᵥ x) =
            star x ⬝ᵥ
              (M.pairingMatrix.map (Int.cast : ℤ → ℝ)) *ᵥ x := by
        rw [← hmatrix, Matrix.smul_mulVec, dotProduct_smul]
        rfl
      linarith

/-- Scaling the canonical half recovers the original even lattice. -/
theorem scaleByTwo_halveOfEven
    (M : PositiveDefiniteIntegralLattice n)
    (hEven : ∀ i j, Even (M.pairingMatrix i j)) :
    (M.halveOfEven hEven).scaleByTwo = M := by
  apply PositiveDefiniteIntegralLattice.ext_pairingMatrix
  ext i j
  change 2 * (M.halfFormMatrix i j) = M.pairingMatrix i j
  simp only [halfFormMatrix]
  rw [mul_comm, Int.ediv_mul_cancel (even_iff_two_dvd.mp (hEven i j))]

/-- Halving a twice-scaled lattice recovers the original lattice. -/
theorem halveOfEven_scaleByTwo (L : PositiveDefiniteIntegralLattice n) :
    L.scaleByTwo.halveOfEven
        (fun i j => by
          change Even (2 * L.pairingMatrix i j)
          exact even_two_mul _) = L := by
  apply PositiveDefiniteIntegralLattice.ext_pairingMatrix
  ext i j
  change (L.scaleByTwo.pairingMatrix i j) / 2 = L.pairingMatrix i j
  simp only [scaleByTwo, Matrix.smul_apply, smul_eq_mul]
  exact Int.mul_ediv_cancel_left _ (by norm_num)

/-! ## Isometry and genus transport under scaling -/

/-- Scaling commutes with extension to the `p`-adic integers. -/
theorem scaleByTwo_pairingMatrix_padic (L : PositiveDefiniteIntegralLattice n)
    (p : ℕ) [Fact (Nat.Prime p)] :
    L.scaleByTwo.pairingMatrix_padic p =
      (2 : ℤ_[p]) • L.pairingMatrix_padic p := by
  ext i j
  simp only [pairingMatrix_padic, scaleByTwo, Matrix.map_apply,
    Matrix.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_ofNat]

/-- Scaling commutes with extension to the reals. -/
theorem scaleByTwo_pairingMatrix_real (L : PositiveDefiniteIntegralLattice n) :
    L.scaleByTwo.pairingMatrix_real = (2 : ℝ) • L.pairingMatrix_real := by
  ext i j
  simp only [pairingMatrix_real, scaleByTwo, Matrix.map_apply,
    Matrix.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_ofNat]

/-- Global integral isometry is unchanged by scaling both matrices by two. -/
theorem scaleByTwo_isGlobalIsometry_iff (L M : PositiveDefiniteIntegralLattice n) :
    L.scaleByTwo.IsGlobalIsometry M.scaleByTwo ↔
      L.IsGlobalIsometry M := by
  constructor
  · rintro ⟨U, hU, hEq⟩
    refine ⟨U, hU, ?_⟩
    change Uᵀ * ((2 : ℤ) • M.pairingMatrix) * U =
      (2 : ℤ) • L.pairingMatrix at hEq
    rw [Matrix.mul_smul, Matrix.smul_mul] at hEq
    ext i j
    have hij := congr_fun₂ hEq i j
    change 2 * (Uᵀ * M.pairingMatrix * U) i j =
      2 * L.pairingMatrix i j at hij
    have htwo : (2 : ℤ) ≠ 0 := by norm_num
    exact mul_left_cancel₀ htwo hij
  · rintro ⟨U, hU, hEq⟩
    refine ⟨U, hU, ?_⟩
    change Uᵀ * ((2 : ℤ) • M.pairingMatrix) * U =
      (2 : ℤ) • L.pairingMatrix
    rw [Matrix.mul_smul, Matrix.smul_mul, hEq]

/-- Finite-prime local isometry is unchanged by scaling both matrices by
two, including at the dyadic prime. -/
theorem scaleByTwo_isLocallyIsometricAt_iff
    (L M : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    L.scaleByTwo.IsLocallyIsometricAt M.scaleByTwo p ↔
      L.IsLocallyIsometricAt M p := by
  constructor
  · rintro ⟨U, hU, hEq⟩
    refine ⟨U, hU, ?_⟩
    rw [L.scaleByTwo_pairingMatrix_padic p,
      M.scaleByTwo_pairingMatrix_padic p] at hEq
    rw [Matrix.mul_smul, Matrix.smul_mul] at hEq
    ext i j
    have hij := congr_fun₂ hEq i j
    change 2 * (Uᵀ * M.pairingMatrix_padic p * U) i j =
      2 * L.pairingMatrix_padic p i j at hij
    have htwo : (2 : ℤ_[p]) ≠ 0 := by norm_num
    exact mul_left_cancel₀ htwo hij
  · rintro ⟨U, hU, hEq⟩
    refine ⟨U, hU, ?_⟩
    rw [L.scaleByTwo_pairingMatrix_padic p,
      M.scaleByTwo_pairingMatrix_padic p]
    rw [Matrix.mul_smul, Matrix.smul_mul, hEq]

/-- Archimedean local isometry is unchanged by scaling both matrices. -/
theorem scaleByTwo_isLocallyIsometricAtInfinity_iff
    (L M : PositiveDefiniteIntegralLattice n) :
    L.scaleByTwo.IsLocallyIsometricAtInfinity M.scaleByTwo ↔
      L.IsLocallyIsometricAtInfinity M := by
  constructor
  · rintro ⟨U, hU, hEq⟩
    refine ⟨U, hU, ?_⟩
    rw [L.scaleByTwo_pairingMatrix_real,
      M.scaleByTwo_pairingMatrix_real] at hEq
    rw [Matrix.mul_smul, Matrix.smul_mul] at hEq
    ext i j
    have hij := congr_fun₂ hEq i j
    change 2 * (Uᵀ * M.pairingMatrix_real * U) i j =
      2 * L.pairingMatrix_real i j at hij
    exact mul_left_cancel₀ (by norm_num : (2 : ℝ) ≠ 0) hij
  · rintro ⟨U, hU, hEq⟩
    refine ⟨U, hU, ?_⟩
    rw [L.scaleByTwo_pairingMatrix_real,
      M.scaleByTwo_pairingMatrix_real]
    rw [Matrix.mul_smul, Matrix.smul_mul, hEq]

/-- The same-genus relation is invariant under scaling both lattices by two. -/
theorem scaleByTwo_isSameGenus_iff (L M : PositiveDefiniteIntegralLattice n) :
    L.scaleByTwo.IsSameGenus M.scaleByTwo ↔ L.IsSameGenus M := by
  constructor
  · intro h
    exact ⟨fun p _ => (scaleByTwo_isLocallyIsometricAt_iff L M p).mp (h.1 p),
      (scaleByTwo_isLocallyIsometricAtInfinity_iff L M).mp h.2⟩
  · intro h
    exact ⟨fun p _ => (scaleByTwo_isLocallyIsometricAt_iff L M p).mpr (h.1 p),
      (scaleByTwo_isLocallyIsometricAtInfinity_iff L M).mpr h.2⟩

/-! ## Equivalence of complete genera -/

/-- Scale a global isometry class in the genus of `L`. -/
def scaleGenusClass (L : PositiveDefiniteIntegralLattice n) (C : L.genus) :
    L.scaleByTwo.genus := by
  let M := genusClassRepresentative L C
  refine ⟨M.scaleByTwo.globalIsometryClass, M.scaleByTwo, ?_, rfl⟩
  exact (scaleByTwo_isSameGenus_iff L M).mpr
    (genusClassRepresentative_isSameGenus L C)

/-- Halve a global isometry class in the genus of `2L`.  Entrywise evenness
is supplied by the dyadic local component of the genus relation. -/
def halveGenusClass (L : PositiveDefiniteIntegralLattice n) (C : L.scaleByTwo.genus) :
    L.genus := by
  let M := genusClassRepresentative L.scaleByTwo C
  have hM : L.scaleByTwo.IsSameGenus M :=
    genusClassRepresentative_isSameGenus L.scaleByTwo C
  let hEven : ∀ i j, Even (M.pairingMatrix i j) :=
    pairingMatrix_even_of_isSameGenus_scaleByTwo L M hM
  let N := M.halveOfEven hEven
  refine ⟨N.globalIsometryClass, N, ?_, rfl⟩
  apply (scaleByTwo_isSameGenus_iff L N).mp
  rw [scaleByTwo_halveOfEven M hEven]
  exact hM

/-- Scaling and canonical halving give an equivalence between the complete
sets of global isometry classes in the genera of `F` and `2F`. -/
def genusEquivScaleByTwo (L : PositiveDefiniteIntegralLattice n) :
    L.genus ≃ L.scaleByTwo.genus where
  toFun := scaleGenusClass L
  invFun := halveGenusClass L
  left_inv := by
    intro C
    apply Subtype.ext
    let M := genusClassRepresentative L C
    let S := genusClassRepresentative L.scaleByTwo (scaleGenusClass L C)
    let hSEven : ∀ i j, Even (S.pairingMatrix i j) :=
      pairingMatrix_even_of_isSameGenus_scaleByTwo L S
        (genusClassRepresentative_isSameGenus L.scaleByTwo
          (scaleGenusClass L C))
    let N := S.halveOfEven hSEven
    have hclassS : M.scaleByTwo.globalIsometryClass = S.globalIsometryClass := by
      simpa [scaleGenusClass, M, S] using
        genusClassRepresentative_globalIsometryClass L.scaleByTwo
          (scaleGenusClass L C)
    have hscale : M.scaleByTwo.IsGlobalIsometry S :=
      isGlobalIsometry_of_globalIsometryClass_eq hclassS
    have hscaleN : M.scaleByTwo.IsGlobalIsometry N.scaleByTwo := by
      rw [scaleByTwo_halveOfEven S hSEven]
      exact hscale
    have hMN : M.IsGlobalIsometry N :=
      (scaleByTwo_isGlobalIsometry_iff M N).mp hscaleN
    change N.globalIsometryClass = C.1
    calc
      N.globalIsometryClass = M.globalIsometryClass :=
        globalIsometryClass_eq_of_isGlobalIsometry (isGlobalIsometry_symm hMN)
      _ = C.1 := (genusClassRepresentative_globalIsometryClass L C).symm
  right_inv := by
    intro C
    apply Subtype.ext
    let M := genusClassRepresentative L.scaleByTwo C
    let hMEven : ∀ i j, Even (M.pairingMatrix i j) :=
      pairingMatrix_even_of_isSameGenus_scaleByTwo L M
        (genusClassRepresentative_isSameGenus L.scaleByTwo C)
    let N := M.halveOfEven hMEven
    let R := genusClassRepresentative L (halveGenusClass L C)
    have hclassR : N.globalIsometryClass = R.globalIsometryClass := by
      simpa [halveGenusClass, M, hMEven, N, R] using
        genusClassRepresentative_globalIsometryClass L (halveGenusClass L C)
    have hNR : N.IsGlobalIsometry R :=
      isGlobalIsometry_of_globalIsometryClass_eq hclassR
    have hscaled : N.scaleByTwo.IsGlobalIsometry R.scaleByTwo :=
      (scaleByTwo_isGlobalIsometry_iff N R).mpr hNR
    have hMR : M.IsGlobalIsometry R.scaleByTwo := by
      rw [← scaleByTwo_halveOfEven M hMEven]
      exact hscaled
    change R.scaleByTwo.globalIsometryClass = C.1
    calc
      R.scaleByTwo.globalIsometryClass = M.globalIsometryClass :=
        globalIsometryClass_eq_of_isGlobalIsometry (isGlobalIsometry_symm hMR)
      _ = C.1 :=
        (genusClassRepresentative_globalIsometryClass L.scaleByTwo C).symm

/-! ## Automorphism and mass compatibility -/

/-- An integral matrix preserves `2F` exactly when it preserves `F`. -/
theorem scaleByTwo_isIsometry_iff (L : PositiveDefiniteIntegralLattice n)
    (U : Matrix (Fin n) (Fin n) ℤ) :
    L.scaleByTwo.IsIsometry U ↔ L.IsIsometry U := by
  constructor
  · rintro ⟨hU, hEq⟩
    refine ⟨hU, ?_⟩
    change Uᵀ * ((2 : ℤ) • L.pairingMatrix) * U =
      (2 : ℤ) • L.pairingMatrix at hEq
    rw [Matrix.mul_smul, Matrix.smul_mul] at hEq
    ext i j
    have hij := congr_fun₂ hEq i j
    change 2 * (Uᵀ * L.pairingMatrix * U) i j =
      2 * L.pairingMatrix i j at hij
    exact mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) hij
  · rintro ⟨hU, hEq⟩
    refine ⟨hU, ?_⟩
    change Uᵀ * ((2 : ℤ) • L.pairingMatrix) * U =
      (2 : ℤ) • L.pairingMatrix
    rw [Matrix.mul_smul, Matrix.smul_mul, hEq]

/-- Proper integral automorphisms are likewise unchanged by scaling. -/
theorem scaleByTwo_isProperIsometry_iff (L : PositiveDefiniteIntegralLattice n)
    (U : Matrix (Fin n) (Fin n) ℤ) :
    L.scaleByTwo.IsProperIsometry U ↔ L.IsProperIsometry U := by
  rw [IsProperIsometry, IsProperIsometry, L.scaleByTwo_isIsometry_iff U]

/-- Literal carrier equivalence of ordinary automorphism groups under
scaling. -/
def isometryGroupEquivScaleByTwo (L : PositiveDefiniteIntegralLattice n) :
    L.IsometryGroup ≃ L.scaleByTwo.IsometryGroup where
  toFun U := ⟨U.1, (L.scaleByTwo_isIsometry_iff U.1).mpr U.2⟩
  invFun U := ⟨U.1, (L.scaleByTwo_isIsometry_iff U.1).mp U.2⟩
  left_inv U := by rfl
  right_inv U := by rfl

/-- Literal carrier equivalence of proper automorphism groups under scaling. -/
def properIsometryGroupEquivScaleByTwo (L : PositiveDefiniteIntegralLattice n) :
    L.ProperIsometryGroup ≃ L.scaleByTwo.ProperIsometryGroup where
  toFun U := ⟨U.1, (L.scaleByTwo_isProperIsometry_iff U.1).mpr U.2⟩
  invFun U := ⟨U.1, (L.scaleByTwo_isProperIsometry_iff U.1).mp U.2⟩
  left_inv U := by rfl
  right_inv U := by rfl

/-- Ordinary automorphism cardinality is invariant under scaling. -/
theorem isometryGroup_card_scaleByTwo (L : PositiveDefiniteIntegralLattice n) :
    Fintype.card L.IsometryGroup =
      Fintype.card L.scaleByTwo.IsometryGroup :=
  Fintype.card_congr L.isometryGroupEquivScaleByTwo

/-- Proper automorphism cardinality is invariant under scaling. -/
theorem properIsometryGroup_card_scaleByTwo (L : PositiveDefiniteIntegralLattice n) :
    Fintype.card L.ProperIsometryGroup =
      Fintype.card L.scaleByTwo.ProperIsometryGroup :=
  Fintype.card_congr L.properIsometryGroupEquivScaleByTwo

/-- The complete ordinary genus mass is invariant under scaling the quadratic
matrix by two. -/
theorem ordinaryGenusMass_scaleByTwo (L : PositiveDefiniteIntegralLattice n) :
    L.scaleByTwo.ordinaryGenusMass = L.ordinaryGenusMass := by
  classical
  symm
  unfold ordinaryGenusMass
  refine Fintype.sum_equiv L.genusEquivScaleByTwo _ _ ?_
  intro C
  let M := genusClassRepresentative L C
  let S := genusClassRepresentative L.scaleByTwo (L.genusEquivScaleByTwo C)
  have hclass : M.scaleByTwo.globalIsometryClass = S.globalIsometryClass := by
    simpa [genusEquivScaleByTwo, scaleGenusClass, M, S] using
      genusClassRepresentative_globalIsometryClass L.scaleByTwo
        (L.genusEquivScaleByTwo C)
  have hMS : M.scaleByTwo.IsGlobalIsometry S :=
    isGlobalIsometry_of_globalIsometryClass_eq hclass
  calc
    ((Fintype.card M.IsometryGroup : ℚ)⁻¹) =
        ((Fintype.card M.scaleByTwo.IsometryGroup : ℚ)⁻¹) := by
      rw [M.isometryGroup_card_scaleByTwo]
    _ = ((Fintype.card S.IsometryGroup : ℚ)⁻¹) :=
      ordinaryGenusMass_summand_eq_of_isGlobalIsometry hMS

/-- The complete proper genus mass is invariant under scaling the quadratic
matrix by two. -/
theorem ordinaryClassSOStabilizerMass_scaleByTwo (L : PositiveDefiniteIntegralLattice n) :
    L.scaleByTwo.ordinaryClassSOStabilizerMass = L.ordinaryClassSOStabilizerMass := by
  classical
  symm
  unfold ordinaryClassSOStabilizerMass
  refine Fintype.sum_equiv L.genusEquivScaleByTwo _ _ ?_
  intro C
  let M := genusClassRepresentative L C
  let S := genusClassRepresentative L.scaleByTwo (L.genusEquivScaleByTwo C)
  have hclass : M.scaleByTwo.globalIsometryClass = S.globalIsometryClass := by
    simpa [genusEquivScaleByTwo, scaleGenusClass, M, S] using
      genusClassRepresentative_globalIsometryClass L.scaleByTwo
        (L.genusEquivScaleByTwo C)
  have hMS : M.scaleByTwo.IsGlobalIsometry S :=
    isGlobalIsometry_of_globalIsometryClass_eq hclass
  calc
    ((Fintype.card M.ProperIsometryGroup : ℚ)⁻¹) =
        ((Fintype.card M.scaleByTwo.ProperIsometryGroup : ℚ)⁻¹) := by
      rw [M.properIsometryGroup_card_scaleByTwo]
    _ = ((Fintype.card S.ProperIsometryGroup : ℚ)⁻¹) :=
      ordinaryClassSOStabilizerMass_summand_eq_of_isGlobalIsometry hMS

/-- The mass of the integral quadratic form of an integral lattice is the ordinary genus mass
of the lattice. -/
theorem toIntegralQuadraticForm_transportedOrdinaryGenusMass (L : PositiveDefiniteIntegralLattice n) :
    L.toIntegralQuadraticForm.transportedOrdinaryGenusMass = L.ordinaryGenusMass := by
  rw [PositiveDefiniteIntegralQuadraticForm.transportedOrdinaryGenusMass_eq_latticeOfPolarForm,
    L.toIntegralQuadraticForm_latticeOfPolarForm_eq_scaleByTwo,
    L.ordinaryGenusMass_scaleByTwo]

/-- The transported proper mass of a conversion to an integral quadratic form is the
old proper genus mass. -/
theorem toIntegralQuadraticForm_transportedOrdinaryClassSOStabilizerMass
    (L : PositiveDefiniteIntegralLattice n) :
    L.toIntegralQuadraticForm.transportedOrdinaryClassSOStabilizerMass = L.ordinaryClassSOStabilizerMass := by
  rw [PositiveDefiniteIntegralQuadraticForm.transportedOrdinaryClassSOStabilizerMass,
    L.toIntegralQuadraticForm_latticeOfPolarForm_eq_scaleByTwo,
    L.ordinaryClassSOStabilizerMass_scaleByTwo]

/-! ## Compatibility of the explicit formula conclusions -/

/-- For the integral quadratic form of an integral lattice, the odd-rank `ENNReal` formula is
literally equivalent to the formula for the lattice. -/
theorem toIntegralQuadraticForm_oddRankExplicitFormulaENNReal_iff
    (L : PositiveDefiniteIntegralLattice n) (N s : ℕ) :
    (ENNReal.ofReal
          (((L.toIntegralQuadraticForm.transportedOrdinaryGenusMass : ℚ) : ℝ)) =
        ENNReal.ofReal
          (L.toIntegralQuadraticForm.massFormulaProductSide
            (L.toIntegralQuadraticForm
              |>.oddRankOrdinaryMassProductLimit N s))) ↔
      (ENNReal.ofReal (((L.ordinaryGenusMass : ℚ) : ℝ)) =
        ENNReal.ofReal
          (L.massFormulaProductSide
            (L.oddRankOrdinaryMassProductLimit N s))) := by
  rw [L.toIntegralQuadraticForm_transportedOrdinaryGenusMass,
    L.toIntegralQuadraticForm_oddRankOrdinaryMassProductLimit,
    L.toIntegralQuadraticForm_massFormulaProductSide]

/-- Real-valued odd-rank formula conclusion compatibility. -/
theorem toIntegralQuadraticForm_oddRankExplicitFormula_iff
    (L : PositiveDefiniteIntegralLattice n) (N s : ℕ) :
    ((((L.toIntegralQuadraticForm.transportedOrdinaryGenusMass : ℚ) : ℝ)) =
        L.toIntegralQuadraticForm.massFormulaProductSide
          (L.toIntegralQuadraticForm
            |>.oddRankOrdinaryMassProductLimit N s)) ↔
      ((((L.ordinaryGenusMass : ℚ) : ℝ)) =
        L.massFormulaProductSide
          (L.oddRankOrdinaryMassProductLimit N s)) := by
  rw [L.toIntegralQuadraticForm_transportedOrdinaryGenusMass,
    L.toIntegralQuadraticForm_oddRankOrdinaryMassProductLimit,
    L.toIntegralQuadraticForm_massFormulaProductSide]

/-- For the integral quadratic form of an integral lattice, the even-rank `ENNReal` formula is
equivalent to the non-endpoint formula for the lattice. -/
theorem toIntegralQuadraticForm_evenRankExplicitFormulaENNReal_iff
    (L : PositiveDefiniteIntegralLattice n) (N s : ℕ) (hn : n = 2 * s) (hs : 1 < s) :
    (ENNReal.ofReal
          (((L.toIntegralQuadraticForm.transportedOrdinaryGenusMass : ℚ) : ℝ)) =
        ENNReal.ofReal
          (L.toIntegralQuadraticForm.massFormulaProductSide
            (L.toIntegralQuadraticForm
              |>.evenRankOrdinaryMassProductLimit N s))) ↔
      (ENNReal.ofReal (((L.ordinaryGenusMass : ℚ) : ℝ)) =
        ENNReal.ofReal
          (L.massFormulaProductSide
            (L.evenRankOrdinaryMassProductLimit N s))) := by
  rw [L.toIntegralQuadraticForm_transportedOrdinaryGenusMass,
    L.toIntegralQuadraticForm_evenRankOrdinaryMassProductLimit
      N s hn hs,
    L.toIntegralQuadraticForm_massFormulaProductSide]

/-- Real-valued even-rank formula conclusion compatibility. -/
theorem toIntegralQuadraticForm_evenRankExplicitFormula_iff
    (L : PositiveDefiniteIntegralLattice n) (N s : ℕ) (hn : n = 2 * s) (hs : 1 < s) :
    ((((L.toIntegralQuadraticForm.transportedOrdinaryGenusMass : ℚ) : ℝ)) =
        L.toIntegralQuadraticForm.massFormulaProductSide
          (L.toIntegralQuadraticForm
            |>.evenRankOrdinaryMassProductLimit N s)) ↔
      ((((L.ordinaryGenusMass : ℚ) : ℝ)) =
        L.massFormulaProductSide
          (L.evenRankOrdinaryMassProductLimit N s)) := by
  rw [L.toIntegralQuadraticForm_transportedOrdinaryGenusMass,
    L.toIntegralQuadraticForm_evenRankOrdinaryMassProductLimit
      N s hn hs,
    L.toIntegralQuadraticForm_massFormulaProductSide]

end PositiveDefiniteIntegralLattice

end
