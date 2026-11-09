import SMSFormula.Finiteness

/-!
# Ordinary-class genus masses

This file packages the finite genus and finite automorphism-group results into
the ordinary genus mass and the ordinary-class-indexed mass with `SO`
stabilizers, `ordinaryClassSOStabilizerMass`. The proper-class
mass is defined separately in `SMSFormula.ProperMass`.

The sums are indexed by the finite genus `L.genus`.  For each genus class we
choose one representative lattice; the summands do not depend on that choice
(`ordinaryGenusMass_summand_eq_of_isGlobalIsometry`), and the masses depend
only on the genus (`ordinaryGenusMass_eq_of_isSameGenus`).
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- A chosen lattice representative of a genus class. -/
def genusClassRepresentative (L : PositiveDefiniteIntegralLattice n) (C : L.genus) :
    PositiveDefiniteIntegralLattice n :=
  Classical.choose C.property

/-- The chosen representative of a genus class is in the same genus as the base
lattice and represents the class. -/
lemma genusClassRepresentative_spec (L : PositiveDefiniteIntegralLattice n) (C : L.genus) :
    L.IsSameGenus (genusClassRepresentative L C) ∧
      C.1 = (genusClassRepresentative L C).globalIsometryClass :=
  Classical.choose_spec C.property

/-- The chosen representative of a genus class is in the same genus as the base
lattice. -/
lemma genusClassRepresentative_isSameGenus (L : PositiveDefiniteIntegralLattice n) (C : L.genus) :
    L.IsSameGenus (genusClassRepresentative L C) :=
  (genusClassRepresentative_spec L C).1

/-- The chosen representative of a genus class represents that class. -/
lemma genusClassRepresentative_globalIsometryClass (L : PositiveDefiniteIntegralLattice n)
    (C : L.genus) :
    C.1 = (genusClassRepresentative L C).globalIsometryClass :=
  (genusClassRepresentative_spec L C).2

/-- The ordinary genus mass, using a chosen representative for each global
isometry class in the genus. -/
def ordinaryGenusMass (L : PositiveDefiniteIntegralLattice n) : ℚ :=
  ∑ C : L.genus,
    ((Fintype.card (genusClassRepresentative L C).IsometryGroup : ℚ)⁻¹)

/-- The mass indexed by ordinary `O`-genus classes with reciprocal
`SO`-stabilizer orders.  This is not the proper-class mass
`properClassGenusMass` defined in `SMSFormula.ProperMass`, whose index set
consists of proper (`SO`) classes. -/
def ordinaryClassSOStabilizerMass (L : PositiveDefiniteIntegralLattice n) : ℚ :=
  ∑ C : L.genus,
    ((Fintype.card (genusClassRepresentative L C).ProperIsometryGroup : ℚ)⁻¹)

/-- Globally isometric lattices have ordinary automorphism groups of the same
cardinality. -/
lemma isometryGroup_card_eq_of_isGlobalIsometry {L₀ L₁ : PositiveDefiniteIntegralLattice n}
    (h : L₀.IsGlobalIsometry L₁) :
    Fintype.card L₀.IsometryGroup = Fintype.card L₁.IsometryGroup := by
  classical
  rcases h with ⟨P, hP_unit, hP⟩
  have hP_det_unit : IsUnit P.det := by
    rwa [Matrix.isUnit_iff_isUnit_det] at hP_unit
  have hPinv_unit : IsUnit (P⁻¹) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_nonsing_inv]
    exact isUnit_ringInverse.mpr hP_det_unit
  have hP_mul_inv : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hP_det_unit
  have hPinv_mul : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hP_det_unit
  have hleft : (P⁻¹).transpose * P.transpose = 1 := by
    rw [← Matrix.transpose_mul, hP_mul_inv, Matrix.transpose_one]
  have hPinv_form : (P⁻¹).transpose * L₀.pairingMatrix * P⁻¹ = L₁.pairingMatrix := by
    calc
      (P⁻¹).transpose * L₀.pairingMatrix * P⁻¹ =
          (P⁻¹).transpose * (P.transpose * L₁.pairingMatrix * P) * P⁻¹ := by
        rw [hP]
      _ = ((P⁻¹).transpose * P.transpose) * L₁.pairingMatrix * (P * P⁻¹) := by
        simp [Matrix.mul_assoc]
      _ = L₁.pairingMatrix := by
        rw [hleft, hP_mul_inv]
        simp
  refine Fintype.card_congr ?_
  refine
  { toFun := fun A => ⟨P * A.1 * P⁻¹, ?_⟩
    invFun := fun B => ⟨P⁻¹ * B.1 * P, ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · constructor
    · simpa [Matrix.mul_assoc] using hP_unit.mul (A.property.1.mul hPinv_unit)
    · calc
        (P * A.1 * P⁻¹).transpose * L₁.pairingMatrix * (P * A.1 * P⁻¹)
            = (P⁻¹).transpose *
                (A.1.transpose * (P.transpose * L₁.pairingMatrix * P) * A.1) * P⁻¹ := by
              simp [Matrix.transpose_mul, Matrix.mul_assoc]
        _ = (P⁻¹).transpose * (A.1.transpose * L₀.pairingMatrix * A.1) * P⁻¹ := by
              rw [hP]
        _ = (P⁻¹).transpose * L₀.pairingMatrix * P⁻¹ := by
              rw [A.property.2]
        _ = L₁.pairingMatrix := hPinv_form
  · constructor
    · simpa [Matrix.mul_assoc] using hPinv_unit.mul (B.property.1.mul hP_unit)
    · calc
        (P⁻¹ * B.1 * P).transpose * L₀.pairingMatrix * (P⁻¹ * B.1 * P)
            = P.transpose *
                (B.1.transpose * ((P⁻¹).transpose * L₀.pairingMatrix * P⁻¹) * B.1) * P := by
              simp [Matrix.transpose_mul, Matrix.mul_assoc]
        _ = P.transpose * (B.1.transpose * L₁.pairingMatrix * B.1) * P := by
              rw [hPinv_form]
        _ = P.transpose * L₁.pairingMatrix * P := by
              rw [B.property.2]
        _ = L₀.pairingMatrix := hP
  · intro A
    apply Subtype.ext
    calc
      P⁻¹ * (P * A.1 * P⁻¹) * P = P⁻¹ * (P * A.1) * (P⁻¹ * P) := by
        simp [Matrix.mul_assoc]
      _ = P⁻¹ * (P * A.1) := by
        rw [hPinv_mul]
        simp
      _ = (P⁻¹ * P) * A.1 := by
        rw [Matrix.mul_assoc]
      _ = A.1 := by
        rw [hPinv_mul]
        simp
  · intro B
    apply Subtype.ext
    calc
      P * (P⁻¹ * B.1 * P) * P⁻¹ = P * (P⁻¹ * B.1) * (P * P⁻¹) := by
        simp [Matrix.mul_assoc]
      _ = P * (P⁻¹ * B.1) := by
        rw [hP_mul_inv]
        simp
      _ = (P * P⁻¹) * B.1 := by
        rw [Matrix.mul_assoc]
      _ = B.1 := by
        rw [hP_mul_inv]
        simp

/-- Globally isometric lattices have proper automorphism groups of the same
cardinality. -/
lemma properIsometryGroup_card_eq_of_isGlobalIsometry {L₀ L₁ : PositiveDefiniteIntegralLattice n}
    (h : L₀.IsGlobalIsometry L₁) :
    Fintype.card L₀.ProperIsometryGroup = Fintype.card L₁.ProperIsometryGroup := by
  classical
  rcases h with ⟨P, hP_unit, hP⟩
  have hP_det_unit : IsUnit P.det := by
    rwa [Matrix.isUnit_iff_isUnit_det] at hP_unit
  have hPinv_unit : IsUnit (P⁻¹) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_nonsing_inv]
    exact isUnit_ringInverse.mpr hP_det_unit
  have hP_mul_inv : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hP_det_unit
  have hPinv_mul : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hP_det_unit
  have hleft : (P⁻¹).transpose * P.transpose = 1 := by
    rw [← Matrix.transpose_mul, hP_mul_inv, Matrix.transpose_one]
  have hPinv_form : (P⁻¹).transpose * L₀.pairingMatrix * P⁻¹ = L₁.pairingMatrix := by
    calc
      (P⁻¹).transpose * L₀.pairingMatrix * P⁻¹ =
          (P⁻¹).transpose * (P.transpose * L₁.pairingMatrix * P) * P⁻¹ := by
        rw [hP]
      _ = ((P⁻¹).transpose * P.transpose) * L₁.pairingMatrix * (P * P⁻¹) := by
        simp [Matrix.mul_assoc]
      _ = L₁.pairingMatrix := by
        rw [hleft, hP_mul_inv]
        simp
  refine Fintype.card_congr ?_
  refine
  { toFun := fun A => ⟨P * A.1 * P⁻¹, ?_⟩
    invFun := fun B => ⟨P⁻¹ * B.1 * P, ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · constructor
    · constructor
      · simpa [Matrix.mul_assoc] using hP_unit.mul (A.property.1.1.mul hPinv_unit)
      · calc
          (P * A.1 * P⁻¹).transpose * L₁.pairingMatrix * (P * A.1 * P⁻¹)
              = (P⁻¹).transpose *
                  (A.1.transpose * (P.transpose * L₁.pairingMatrix * P) * A.1) * P⁻¹ := by
                simp [Matrix.transpose_mul, Matrix.mul_assoc]
          _ = (P⁻¹).transpose * (A.1.transpose * L₀.pairingMatrix * A.1) * P⁻¹ := by
                rw [hP]
          _ = (P⁻¹).transpose * L₀.pairingMatrix * P⁻¹ := by
                rw [A.property.1.2]
          _ = L₁.pairingMatrix := hPinv_form
    · calc
        (P * A.1 * P⁻¹).det = P.det * A.1.det * (P⁻¹).det := by
          simp [Matrix.det_mul, mul_assoc]
        _ = P.det * 1 * Ring.inverse P.det := by
          rw [A.property.2, Matrix.det_nonsing_inv]
        _ = 1 := by
          simpa [mul_assoc] using Ring.mul_inverse_cancel P.det hP_det_unit
  · constructor
    · constructor
      · simpa [Matrix.mul_assoc] using hPinv_unit.mul (B.property.1.1.mul hP_unit)
      · calc
          (P⁻¹ * B.1 * P).transpose * L₀.pairingMatrix * (P⁻¹ * B.1 * P)
              = P.transpose *
                  (B.1.transpose * ((P⁻¹).transpose * L₀.pairingMatrix * P⁻¹) * B.1) * P := by
                simp [Matrix.transpose_mul, Matrix.mul_assoc]
          _ = P.transpose * (B.1.transpose * L₁.pairingMatrix * B.1) * P := by
                rw [hPinv_form]
          _ = P.transpose * L₁.pairingMatrix * P := by
                rw [B.property.1.2]
          _ = L₀.pairingMatrix := hP
    · calc
        (P⁻¹ * B.1 * P).det = (P⁻¹).det * B.1.det * P.det := by
          simp [Matrix.det_mul, mul_assoc]
        _ = Ring.inverse P.det * 1 * P.det := by
          rw [B.property.2, Matrix.det_nonsing_inv]
        _ = 1 := by
          simpa [mul_assoc] using Ring.inverse_mul_cancel P.det hP_det_unit
  · intro A
    apply Subtype.ext
    calc
      P⁻¹ * (P * A.1 * P⁻¹) * P = P⁻¹ * (P * A.1) * (P⁻¹ * P) := by
        simp [Matrix.mul_assoc]
      _ = P⁻¹ * (P * A.1) := by
        rw [hPinv_mul]
        simp
      _ = (P⁻¹ * P) * A.1 := by
        rw [Matrix.mul_assoc]
      _ = A.1 := by
        rw [hPinv_mul]
        simp
  · intro B
    apply Subtype.ext
    calc
      P * (P⁻¹ * B.1 * P) * P⁻¹ = P * (P⁻¹ * B.1) * (P * P⁻¹) := by
        simp [Matrix.mul_assoc]
      _ = P * (P⁻¹ * B.1) := by
        rw [hP_mul_inv]
        simp
      _ = (P * P⁻¹) * B.1 := by
        rw [Matrix.mul_assoc]
      _ = B.1 := by
        rw [hP_mul_inv]
        simp

/-- The ordinary mass summand is independent of replacing a representative by a
globally isometric lattice. -/
lemma ordinaryGenusMass_summand_eq_of_isGlobalIsometry {L₀ L₁ : PositiveDefiniteIntegralLattice n}
    (h : L₀.IsGlobalIsometry L₁) :
    ((Fintype.card L₀.IsometryGroup : ℚ)⁻¹) =
      ((Fintype.card L₁.IsometryGroup : ℚ)⁻¹) := by
  rw [isometryGroup_card_eq_of_isGlobalIsometry h]

/-- The proper mass summand is independent of replacing a representative by a
globally isometric lattice. -/
lemma ordinaryClassSOStabilizerMass_summand_eq_of_isGlobalIsometry {L₀ L₁ : PositiveDefiniteIntegralLattice n}
    (h : L₀.IsGlobalIsometry L₁) :
    ((Fintype.card L₀.ProperIsometryGroup : ℚ)⁻¹) =
      ((Fintype.card L₁.ProperIsometryGroup : ℚ)⁻¹) := by
  rw [properIsometryGroup_card_eq_of_isGlobalIsometry h]

/-- A global isometry of base lattices identifies their genera. -/
def genusEquivOfIsGlobalIsometry {L₀ L₁ : PositiveDefiniteIntegralLattice n}
    (h : L₀.IsGlobalIsometry L₁) : L₀.genus ≃ L₁.genus where
  toFun C := by
    refine ⟨C.1, ?_⟩
    rcases C.2 with ⟨M, hM, hC⟩
    exact ⟨M, isSameGenus_trans
      (isSameGenus_symm (isSameGenus_of_isGlobalIsometry h)) hM, hC⟩
  invFun C := by
    refine ⟨C.1, ?_⟩
    rcases C.2 with ⟨M, hM, hC⟩
    exact ⟨M, isSameGenus_trans (isSameGenus_of_isGlobalIsometry h) hM, hC⟩
  left_inv C := by
    rfl
  right_inv C := by
    rfl

/-- A same-genus relation of base lattices identifies their genera. -/
def genusEquivOfIsSameGenus {L₀ L₁ : PositiveDefiniteIntegralLattice n}
    (h : L₀.IsSameGenus L₁) : L₀.genus ≃ L₁.genus where
  toFun C := by
    refine ⟨C.1, ?_⟩
    rcases C.2 with ⟨M, hM, hC⟩
    exact ⟨M, isSameGenus_trans (isSameGenus_symm h) hM, hC⟩
  invFun C := by
    refine ⟨C.1, ?_⟩
    rcases C.2 with ⟨M, hM, hC⟩
    exact ⟨M, isSameGenus_trans h hM, hC⟩
  left_inv C := by
    rfl
  right_inv C := by
    rfl

/-- The chosen ordinary genus mass is invariant under replacing the base
lattice by a globally isometric lattice. -/
lemma ordinaryGenusMass_eq_of_isGlobalIsometry {L₀ L₁ : PositiveDefiniteIntegralLattice n}
    (h : L₀.IsGlobalIsometry L₁) :
    L₀.ordinaryGenusMass = L₁.ordinaryGenusMass := by
  classical
  let e := genusEquivOfIsGlobalIsometry h
  unfold ordinaryGenusMass
  refine Fintype.sum_equiv e _ _ ?_
  intro C
  apply ordinaryGenusMass_summand_eq_of_isGlobalIsometry
  have hmem : genusClassRepresentative L₁ (e C) ∈ C.1 := by
    change genusClassRepresentative L₁ (e C) ∈ (e C).1
    rw [genusClassRepresentative_globalIsometryClass]
    exact mem_globalIsometryClass_self _
  rw [genusClassRepresentative_globalIsometryClass L₀ C] at hmem
  exact hmem

/-- The chosen ordinary genus mass is invariant under replacing the base
lattice by another lattice in the same genus. -/
lemma ordinaryGenusMass_eq_of_isSameGenus {L₀ L₁ : PositiveDefiniteIntegralLattice n}
    (h : L₀.IsSameGenus L₁) :
    L₀.ordinaryGenusMass = L₁.ordinaryGenusMass := by
  classical
  let e := genusEquivOfIsSameGenus h
  unfold ordinaryGenusMass
  refine Fintype.sum_equiv e _ _ ?_
  intro C
  apply ordinaryGenusMass_summand_eq_of_isGlobalIsometry
  have hmem : genusClassRepresentative L₁ (e C) ∈ C.1 := by
    change genusClassRepresentative L₁ (e C) ∈ (e C).1
    rw [genusClassRepresentative_globalIsometryClass]
    exact mem_globalIsometryClass_self _
  rw [genusClassRepresentative_globalIsometryClass L₀ C] at hmem
  exact hmem

/-- The chosen proper genus mass is invariant under replacing the base lattice
by a globally isometric lattice. -/
lemma ordinaryClassSOStabilizerMass_eq_of_isGlobalIsometry {L₀ L₁ : PositiveDefiniteIntegralLattice n}
    (h : L₀.IsGlobalIsometry L₁) :
    L₀.ordinaryClassSOStabilizerMass = L₁.ordinaryClassSOStabilizerMass := by
  classical
  let e := genusEquivOfIsGlobalIsometry h
  unfold ordinaryClassSOStabilizerMass
  refine Fintype.sum_equiv e _ _ ?_
  intro C
  apply ordinaryClassSOStabilizerMass_summand_eq_of_isGlobalIsometry
  have hmem : genusClassRepresentative L₁ (e C) ∈ C.1 := by
    change genusClassRepresentative L₁ (e C) ∈ (e C).1
    rw [genusClassRepresentative_globalIsometryClass]
    exact mem_globalIsometryClass_self _
  rw [genusClassRepresentative_globalIsometryClass L₀ C] at hmem
  exact hmem

/-- The chosen proper genus mass is invariant under replacing the base lattice
by another lattice in the same genus. -/
lemma ordinaryClassSOStabilizerMass_eq_of_isSameGenus {L₀ L₁ : PositiveDefiniteIntegralLattice n}
    (h : L₀.IsSameGenus L₁) :
    L₀.ordinaryClassSOStabilizerMass = L₁.ordinaryClassSOStabilizerMass := by
  classical
  let e := genusEquivOfIsSameGenus h
  unfold ordinaryClassSOStabilizerMass
  refine Fintype.sum_equiv e _ _ ?_
  intro C
  apply ordinaryClassSOStabilizerMass_summand_eq_of_isGlobalIsometry
  have hmem : genusClassRepresentative L₁ (e C) ∈ C.1 := by
    change genusClassRepresentative L₁ (e C) ∈ (e C).1
    rw [genusClassRepresentative_globalIsometryClass]
    exact mem_globalIsometryClass_self _
  rw [genusClassRepresentative_globalIsometryClass L₀ C] at hmem
  exact hmem

/-- The chosen ordinary genus mass depends only on the global isometry class of
the base lattice. -/
lemma ordinaryGenusMass_eq_of_globalIsometryClass_eq {L₀ L₁ : PositiveDefiniteIntegralLattice n}
    (h : L₀.globalIsometryClass = L₁.globalIsometryClass) :
    L₀.ordinaryGenusMass = L₁.ordinaryGenusMass :=
  ordinaryGenusMass_eq_of_isGlobalIsometry
    (isGlobalIsometry_of_globalIsometryClass_eq h)

/-- The chosen proper genus mass depends only on the global isometry class of
the base lattice. -/
lemma ordinaryClassSOStabilizerMass_eq_of_globalIsometryClass_eq {L₀ L₁ : PositiveDefiniteIntegralLattice n}
    (h : L₀.globalIsometryClass = L₁.globalIsometryClass) :
    L₀.ordinaryClassSOStabilizerMass = L₁.ordinaryClassSOStabilizerMass :=
  ordinaryClassSOStabilizerMass_eq_of_isGlobalIsometry
    (isGlobalIsometry_of_globalIsometryClass_eq h)

/-- Each ordinary mass summand is positive. -/
lemma ordinaryGenusMass_summand_pos (L : PositiveDefiniteIntegralLattice n) (C : L.genus) :
    0 < ((Fintype.card (genusClassRepresentative L C).IsometryGroup : ℚ)⁻¹) := by
  exact inv_pos.mpr (Nat.cast_pos.mpr
    ((genusClassRepresentative L C).isometryGroup_card_pos))

/-- Each proper mass summand is positive. -/
lemma ordinaryClassSOStabilizerMass_summand_pos (L : PositiveDefiniteIntegralLattice n) (C : L.genus) :
    0 < ((Fintype.card (genusClassRepresentative L C).ProperIsometryGroup : ℚ)⁻¹) := by
  exact inv_pos.mpr (Nat.cast_pos.mpr
    ((genusClassRepresentative L C).properIsometryGroup_card_pos))

/-- The ordinary genus mass is a positive rational number. -/
theorem ordinaryGenusMass_pos (L : PositiveDefiniteIntegralLattice n) :
    0 < L.ordinaryGenusMass := by
  classical
  unfold ordinaryGenusMass
  refine Finset.sum_pos (fun C _ => ordinaryGenusMass_summand_pos L C) ?_
  exact ⟨⟨L.globalIsometryClass, L.mem_genus_self⟩, Finset.mem_univ _⟩

/-- The proper genus mass is a positive rational number. -/
theorem ordinaryClassSOStabilizerMass_pos (L : PositiveDefiniteIntegralLattice n) :
    0 < L.ordinaryClassSOStabilizerMass := by
  classical
  unfold ordinaryClassSOStabilizerMass
  refine Finset.sum_pos (fun C _ => ordinaryClassSOStabilizerMass_summand_pos L C) ?_
  exact ⟨⟨L.globalIsometryClass, L.mem_genus_self⟩, Finset.mem_univ _⟩

end PositiveDefiniteIntegralLattice

end
