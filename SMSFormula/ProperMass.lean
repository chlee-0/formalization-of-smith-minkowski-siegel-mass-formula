import SMSFormula.Mass

/-!
# Proper genus classes

This file defines the proper `SO`-class mass and separates it from
`ordinaryClassSOStabilizerMass` in `SMSFormula.Mass`.

`ordinaryClassSOStabilizerMass` is indexed by ordinary `O`-genus classes and
uses proper stabilizers in the denominator.  It is therefore **not** the
proper-class mass, despite its former name `properGenusMass`.  Schulze--Pillot's proper formula
is instead indexed by determinant-one global isometry classes.  We name that
index set here and prove the elementary splitting statement by finite fibres
over ordinary genus classes.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- An ordinary automorphism with determinant `-1`, i.e. an
orientation-reversing integral isometry of a based lattice. -/
def HasOrientationReversingIsometry (L : PositiveDefiniteIntegralLattice n) : Prop :=
  ∃ U : Matrix (Fin n) (Fin n) ℤ, L.IsIsometry U ∧ U.det = -1

/-- The determinant-`-1` part of the ordinary automorphism group. -/
def OrientationReversingIsometryGroup (L : PositiveDefiniteIntegralLattice n) : Type :=
  { U : Matrix (Fin n) (Fin n) ℤ // L.IsIsometry U ∧ U.det = -1 }

/-- View the determinant-`-1` part as a subtype of the ordinary automorphism
group. -/
def orientationReversingIsometryGroupEquivIsometryGroupSubtype
    (L : PositiveDefiniteIntegralLattice n) :
    L.OrientationReversingIsometryGroup ≃
      { U : L.IsometryGroup // U.1.det = -1 } where
  toFun U := ⟨⟨U.1, U.2.1⟩, U.2.2⟩
  invFun U := ⟨U.1.1, U.1.2, U.2⟩
  left_inv U := by
    rfl
  right_inv U := by
    rfl

/-- The determinant-`-1` part of the ordinary automorphism group is finite. -/
noncomputable instance orientationReversingIsometryGroup_fintype
    (L : PositiveDefiniteIntegralLattice n) :
    Fintype L.OrientationReversingIsometryGroup :=
  Fintype.ofEquiv { U : L.IsometryGroup // U.1.det = -1 }
    (L.orientationReversingIsometryGroupEquivIsometryGroupSubtype).symm

/-- Split the ordinary automorphism group by determinant sign. -/
def isometryGroupEquivProperSumOrientationReversing
    (L : PositiveDefiniteIntegralLattice n) :
    L.IsometryGroup ≃
      L.ProperIsometryGroup ⊕ L.OrientationReversingIsometryGroup where
  toFun U := by
    have hU_det_unit : IsUnit U.1.det := by
      have hunit : IsUnit U.1 := U.2.1
      rwa [Matrix.isUnit_iff_isUnit_det] at hunit
    by_cases hdet : U.1.det = 1
    · exact Sum.inl ⟨U.1, U.2, hdet⟩
    · have hneg : U.1.det = -1 := by
        rcases Int.isUnit_iff.mp hU_det_unit with hpos | hneg
        · exact (hdet hpos).elim
        · exact hneg
      exact Sum.inr ⟨U.1, U.2, hneg⟩
  invFun s :=
    match s with
    | Sum.inl U => ⟨U.1, U.2.1⟩
    | Sum.inr U => ⟨U.1, U.2.1⟩
  left_inv U := by
    dsimp
    have hU_det_unit : IsUnit U.1.det := by
      have hunit : IsUnit U.1 := U.2.1
      rwa [Matrix.isUnit_iff_isUnit_det] at hunit
    by_cases hdet : U.1.det = 1
    · simp [hdet]
    · have hneg : U.1.det = -1 := by
        rcases Int.isUnit_iff.mp hU_det_unit with hpos | hneg
        · exact (hdet hpos).elim
        · exact hneg
      simp [hneg]
  right_inv s := by
    cases s with
    | inl U =>
        dsimp
        simp [U.2.2]
    | inr U =>
        dsimp
        simp [U.2.2]

/-- The ordinary automorphism group is the disjoint union of its determinant
`1` and determinant `-1` parts. -/
lemma isometryGroup_card_eq_proper_add_orientationReversing
    (L : PositiveDefiniteIntegralLattice n) :
    Fintype.card L.IsometryGroup =
      Fintype.card L.ProperIsometryGroup +
        Fintype.card L.OrientationReversingIsometryGroup := by
  calc
    Fintype.card L.IsometryGroup =
        Fintype.card
          (L.ProperIsometryGroup ⊕ L.OrientationReversingIsometryGroup) :=
      Fintype.card_congr (L.isometryGroupEquivProperSumOrientationReversing)
    _ = Fintype.card L.ProperIsometryGroup +
        Fintype.card L.OrientationReversingIsometryGroup :=
      Fintype.card_sum

/-- The product of two ordinary isometries is an ordinary isometry. -/
lemma isIsometry_mul (L : PositiveDefiniteIntegralLattice n)
    {U V : Matrix (Fin n) (Fin n) ℤ}
    (hU : L.IsIsometry U) (hV : L.IsIsometry V) :
    L.IsIsometry (U * V) := by
  constructor
  · exact hU.1.mul hV.1
  · calc
      (U * V).transpose * L.pairingMatrix * (U * V) =
          V.transpose * (U.transpose * L.pairingMatrix * U) * V := by
        simp [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = V.transpose * L.pairingMatrix * V := by
        rw [hU.2]
      _ = L.pairingMatrix := hV.2

/-- The inverse of an ordinary isometry is an ordinary isometry. -/
lemma isIsometry_nonsing_inv (L : PositiveDefiniteIntegralLattice n)
    {U : Matrix (Fin n) (Fin n) ℤ} (hU : L.IsIsometry U) :
    L.IsIsometry U⁻¹ := by
  have hU_det_unit : IsUnit U.det := by
    have hunit : IsUnit U := hU.1
    rwa [Matrix.isUnit_iff_isUnit_det] at hunit
  have hU_mul_inv : U * U⁻¹ = 1 := Matrix.mul_nonsing_inv U hU_det_unit
  have hleft : (U⁻¹).transpose * U.transpose = 1 := by
    rw [← Matrix.transpose_mul, hU_mul_inv, Matrix.transpose_one]
  constructor
  · rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_nonsing_inv]
    exact isUnit_ringInverse.mpr hU_det_unit
  · calc
      (U⁻¹).transpose * L.pairingMatrix * U⁻¹ =
          (U⁻¹).transpose * (U.transpose * L.pairingMatrix * U) * U⁻¹ := by
        rw [hU.2]
      _ = ((U⁻¹).transpose * U.transpose) * L.pairingMatrix * (U * U⁻¹) := by
        simp [Matrix.mul_assoc]
      _ = L.pairingMatrix := by
        rw [hleft, hU_mul_inv]
        simp

/-- A fixed orientation-reversing automorphism bijects proper automorphisms
with orientation-reversing ordinary automorphisms. -/
def properIsometryGroupEquivOrientationReversingOfOrientationReversing
    (L : PositiveDefiniteIntegralLattice n) {R : Matrix (Fin n) (Fin n) ℤ}
    (hR : L.IsIsometry R) (hRdet : R.det = -1) :
    L.ProperIsometryGroup ≃ L.OrientationReversingIsometryGroup where
  toFun A := by
    refine ⟨R * A.1, ?_⟩
    constructor
    · exact L.isIsometry_mul hR A.2.1
    · simp [Matrix.det_mul, hRdet, A.2.2]
  invFun B := by
    refine ⟨R⁻¹ * B.1, ?_⟩
    constructor
    · exact L.isIsometry_mul (L.isIsometry_nonsing_inv hR) B.2.1
    · rw [Matrix.det_mul, Matrix.det_nonsing_inv, hRdet, B.2.2]
      have hunit : IsUnit (-1 : ℤ) := Int.isUnit_iff.mpr (Or.inr rfl)
      simpa using Ring.inverse_mul_cancel (-1 : ℤ) hunit
  left_inv A := by
    apply Subtype.ext
    have hR_det_unit : IsUnit R.det := by
      have hunit : IsUnit R := hR.1
      rwa [Matrix.isUnit_iff_isUnit_det] at hunit
    have hR_inv_mul : R⁻¹ * R = 1 := Matrix.nonsing_inv_mul R hR_det_unit
    calc
      R⁻¹ * (R * A.1) = (R⁻¹ * R) * A.1 := by
        rw [Matrix.mul_assoc]
      _ = A.1 := by
        rw [hR_inv_mul]
        simp
  right_inv B := by
    apply Subtype.ext
    have hR_det_unit : IsUnit R.det := by
      have hunit : IsUnit R := hR.1
      rwa [Matrix.isUnit_iff_isUnit_det] at hunit
    have hR_mul_inv : R * R⁻¹ = 1 := Matrix.mul_nonsing_inv R hR_det_unit
    calc
      R * (R⁻¹ * B.1) = (R * R⁻¹) * B.1 := by
        rw [Matrix.mul_assoc]
      _ = B.1 := by
        rw [hR_mul_inv]
        simp

/-- If an orientation-reversing automorphism exists, the determinant-`1` and
determinant-`-1` parts of the ordinary automorphism group have equal
cardinality. -/
lemma properIsometryGroup_card_eq_orientationReversingIsometryGroup_card
    (L : PositiveDefiniteIntegralLattice n) (h : L.HasOrientationReversingIsometry) :
    Fintype.card L.ProperIsometryGroup =
      Fintype.card L.OrientationReversingIsometryGroup := by
  rcases h with ⟨R, hR, hRdet⟩
  exact Fintype.card_congr
    (properIsometryGroupEquivOrientationReversingOfOrientationReversing
      L hR hRdet)

/-- In the orientation-reversing case, the proper automorphism group has index
two in the ordinary automorphism group. -/
lemma isometryGroup_card_eq_two_mul_properIsometryGroup_card_of_hasOrientationReversing
    (L : PositiveDefiniteIntegralLattice n) (h : L.HasOrientationReversingIsometry) :
    Fintype.card L.IsometryGroup =
      2 * Fintype.card L.ProperIsometryGroup := by
  rw [L.isometryGroup_card_eq_proper_add_orientationReversing]
  rw [← L.properIsometryGroup_card_eq_orientationReversingIsometryGroup_card h]
  omega

/-- If a lattice has no orientation-reversing automorphism, every ordinary
isometry is proper. -/
lemma isProperIsometry_of_isIsometry_of_not_hasOrientationReversing
    (L : PositiveDefiniteIntegralLattice n) (hno : ¬ L.HasOrientationReversingIsometry)
    {U : Matrix (Fin n) (Fin n) ℤ} (hU : L.IsIsometry U) :
    L.IsProperIsometry U := by
  constructor
  · exact hU
  · have hU_det_unit : IsUnit U.det := by
      have hunit : IsUnit U := hU.1
      rwa [Matrix.isUnit_iff_isUnit_det] at hunit
    rcases Int.isUnit_iff.mp hU_det_unit with hdet | hdet
    · exact hdet
    · exfalso
      exact hno ⟨U, hU, hdet⟩

/-- When no orientation-reversing automorphism exists, ordinary and proper
automorphism groups are the same finite type. -/
def isometryGroupEquivProperIsometryGroupOfNoOrientationReversing
    (L : PositiveDefiniteIntegralLattice n) (hno : ¬ L.HasOrientationReversingIsometry) :
    L.IsometryGroup ≃ L.ProperIsometryGroup where
  toFun U :=
    ⟨U.1, isProperIsometry_of_isIsometry_of_not_hasOrientationReversing
      L hno U.2⟩
  invFun U := ⟨U.1, U.2.1⟩
  left_inv U := by
    rfl
  right_inv U := by
    rfl

/-- Cardinality comparison in the no-orientation-reversing case. -/
lemma isometryGroup_card_eq_properIsometryGroup_card_of_noOrientationReversing
    (L : PositiveDefiniteIntegralLattice n) (hno : ¬ L.HasOrientationReversingIsometry) :
    Fintype.card L.IsometryGroup = Fintype.card L.ProperIsometryGroup := by
  exact Fintype.card_congr
    (isometryGroupEquivProperIsometryGroupOfNoOrientationReversing L hno)

/-- Determinant-one global integral isometry between two based lattices. -/
def IsProperGlobalIsometry (L L' : PositiveDefiniteIntegralLattice n) : Prop :=
  ∃ U : Matrix (Fin n) (Fin n) ℤ,
    IsUnit U ∧ (U.det = 1) ∧ (U.transpose * L'.pairingMatrix * U = L.pairingMatrix)

/-- A proper global isometry is, in particular, an ordinary global isometry. -/
lemma isGlobalIsometry_of_isProperGlobalIsometry {L L' : PositiveDefiniteIntegralLattice n}
    (h : L.IsProperGlobalIsometry L') : L.IsGlobalIsometry L' := by
  rcases h with ⟨U, hU_unit, _hU_det, hU_form⟩
  exact ⟨U, hU_unit, hU_form⟩

/-- Proper global isometry is reflexive. -/
theorem isProperGlobalIsometry_refl (L : PositiveDefiniteIntegralLattice n) :
    L.IsProperGlobalIsometry L := by
  exact ⟨1, isUnit_one, by simp, by simp⟩

/-- Proper global isometry is symmetric. -/
theorem isProperGlobalIsometry_symm {L L' : PositiveDefiniteIntegralLattice n}
    (h : L.IsProperGlobalIsometry L') : L'.IsProperGlobalIsometry L := by
  rcases h with ⟨U, hU_unit, hU_det, hU_form⟩
  have hU_det_unit : IsUnit U.det := by
    rwa [Matrix.isUnit_iff_isUnit_det] at hU_unit
  have hU_mul_inv : U * U⁻¹ = 1 := Matrix.mul_nonsing_inv U hU_det_unit
  have hleft : (U⁻¹).transpose * U.transpose = 1 := by
    rw [← Matrix.transpose_mul, hU_mul_inv, Matrix.transpose_one]
  use U⁻¹
  constructor
  · simp_all +decide [Matrix.isUnit_iff_isUnit_det]
  constructor
  · rw [Matrix.det_nonsing_inv]
    simp [hU_det]
  · calc
      (U⁻¹).transpose * L.pairingMatrix * U⁻¹ =
          (U⁻¹).transpose * (U.transpose * L'.pairingMatrix * U) * U⁻¹ := by
        rw [hU_form]
      _ = ((U⁻¹).transpose * U.transpose) * L'.pairingMatrix * (U * U⁻¹) := by
        simp [Matrix.mul_assoc]
      _ = L'.pairingMatrix := by
        rw [hleft, hU_mul_inv]
        simp

/-- Proper global isometry is transitive. -/
theorem isProperGlobalIsometry_trans {L L' L'' : PositiveDefiniteIntegralLattice n}
    (h1 : L.IsProperGlobalIsometry L')
    (h2 : L'.IsProperGlobalIsometry L'') :
    L.IsProperGlobalIsometry L'' := by
  rcases h1 with ⟨U, hU_unit, hU_det, hU_form⟩
  rcases h2 with ⟨V, hV_unit, hV_det, hV_form⟩
  use V * U
  constructor
  · exact hV_unit.mul hU_unit
  constructor
  · simp [Matrix.det_mul, hV_det, hU_det]
  · simp_all +decide [Matrix.mul_assoc, Matrix.transpose_mul]
    simp_all +decide [← Matrix.mul_assoc]

/-- The determinant-one global isometry class represented by `L`. -/
def properGlobalIsometryClass (L : PositiveDefiniteIntegralLattice n) :
    Set (PositiveDefiniteIntegralLattice n) :=
  { L' | L.IsProperGlobalIsometry L' }

/-- Properly isometric representatives define the same determinant-one class. -/
lemma properGlobalIsometryClass_eq_of_isProperGlobalIsometry
    {L L' : PositiveDefiniteIntegralLattice n} (h : L.IsProperGlobalIsometry L') :
    L.properGlobalIsometryClass = L'.properGlobalIsometryClass := by
  ext M
  constructor
  · intro hM
    exact isProperGlobalIsometry_trans (isProperGlobalIsometry_symm h) hM
  · intro hM
    exact isProperGlobalIsometry_trans h hM

/-- Equality of determinant-one proper classes gives a proper global isometry
between their representatives. -/
lemma isProperGlobalIsometry_of_properGlobalIsometryClass_eq
    {L L' : PositiveDefiniteIntegralLattice n}
    (h : L.properGlobalIsometryClass = L'.properGlobalIsometryClass) :
    L.IsProperGlobalIsometry L' := by
  have hmem : L' ∈ L.properGlobalIsometryClass := by
    rw [h]
    exact L'.isProperGlobalIsometry_refl
  exact hmem

/-- Proper classes refine ordinary global isometry classes. -/
lemma properGlobalIsometryClass_subset_globalIsometryClass
    (L : PositiveDefiniteIntegralLattice n) :
    L.properGlobalIsometryClass ⊆ L.globalIsometryClass := by
  intro L' hL'
  exact isGlobalIsometry_of_isProperGlobalIsometry hL'

/-- If the target lattice has an orientation-reversing automorphism, any
ordinary global isometry into it can be adjusted to determinant `1`. -/
lemma isProperGlobalIsometry_of_isGlobalIsometry_of_hasOrientationReversing_target
    {L M : PositiveDefiniteIntegralLattice n} (h : L.IsGlobalIsometry M)
    (hrev : M.HasOrientationReversingIsometry) :
    L.IsProperGlobalIsometry M := by
  rcases h with ⟨U, hU_unit, hU_form⟩
  have hU_det_unit : IsUnit U.det := by
    rwa [Matrix.isUnit_iff_isUnit_det] at hU_unit
  rcases Int.isUnit_iff.mp hU_det_unit with hU_det | hU_det
  · exact ⟨U, hU_unit, hU_det, hU_form⟩
  · rcases hrev with ⟨R, hR_iso, hR_det⟩
    refine ⟨R * U, hR_iso.1.mul hU_unit, ?_, ?_⟩
    · simp [Matrix.det_mul, hR_det, hU_det]
    · calc
        (R * U).transpose * M.pairingMatrix * (R * U) =
            U.transpose * (R.transpose * M.pairingMatrix * R) * U := by
          simp [Matrix.transpose_mul, Matrix.mul_assoc]
        _ = U.transpose * M.pairingMatrix * U := by
          rw [hR_iso.2]
        _ = L.pairingMatrix := hU_form

/-- The representative belongs to its own proper global isometry class. -/
lemma mem_properGlobalIsometryClass_self (L : PositiveDefiniteIntegralLattice n) :
    L ∈ L.properGlobalIsometryClass :=
  L.isProperGlobalIsometry_refl

/-- The proof-note proper genus: determinant-one global isometry classes
represented by lattices in the same ordinary genus as `L`. -/
def properGenus (L : PositiveDefiniteIntegralLattice n) : Set (Set (PositiveDefiniteIntegralLattice n)) :=
  { C | ∃ L' : PositiveDefiniteIntegralLattice n,
      L.IsSameGenus L' ∧ C = L'.properGlobalIsometryClass }

/-- The proper class of `L` belongs to the proper genus of `L`. -/
theorem mem_properGenus_self (L : PositiveDefiniteIntegralLattice n) :
    L.properGlobalIsometryClass ∈ L.properGenus :=
  ⟨L, L.isSameGenus_refl, rfl⟩

/-- A chosen representative of a determinant-one proper genus class. -/
def properGenusClassRepresentative (L : PositiveDefiniteIntegralLattice n)
    (C : L.properGenus) : PositiveDefiniteIntegralLattice n :=
  Classical.choose C.property

/-- The chosen proper representative is in the same genus as the base lattice
and represents the determinant-one proper class. -/
lemma properGenusClassRepresentative_spec (L : PositiveDefiniteIntegralLattice n)
    (C : L.properGenus) :
    L.IsSameGenus (properGenusClassRepresentative L C) ∧
      C.1 = (properGenusClassRepresentative L C).properGlobalIsometryClass :=
  Classical.choose_spec C.property

/-- The chosen proper representative is in the same ordinary genus as the base
lattice. -/
lemma properGenusClassRepresentative_isSameGenus (L : PositiveDefiniteIntegralLattice n)
    (C : L.properGenus) :
    L.IsSameGenus (properGenusClassRepresentative L C) :=
  (properGenusClassRepresentative_spec L C).1

/-- The ordinary genus class under a proper genus class. -/
def ordinaryClassOfProperGenusClass (L : PositiveDefiniteIntegralLattice n)
    (C : L.properGenus) : L.genus :=
  ⟨(properGenusClassRepresentative L C).globalIsometryClass,
    ⟨properGenusClassRepresentative L C,
      properGenusClassRepresentative_isSameGenus L C, rfl⟩⟩

/-- The determinant-one proper classes lying above a fixed ordinary genus
class. -/
def properGenusFiber (L : PositiveDefiniteIntegralLattice n) (C : L.genus) : Type :=
  { Cp : L.properGenus // ordinaryClassOfProperGenusClass L Cp = C }

/-- The determinant-one proper class represented by the chosen ordinary genus
representative. -/
def properGenusClassOfOrdinaryRepresentative
    (L : PositiveDefiniteIntegralLattice n) (C : L.genus) : L.properGenus :=
  ⟨(genusClassRepresentative L C).properGlobalIsometryClass,
    ⟨genusClassRepresentative L C,
      genusClassRepresentative_isSameGenus L C, rfl⟩⟩

/-- The proper class represented by the chosen ordinary representative lies in
the fibre over that ordinary class. -/
lemma ordinaryClassOf_properGenusClassOfOrdinaryRepresentative
    (L : PositiveDefiniteIntegralLattice n) (C : L.genus) :
    ordinaryClassOfProperGenusClass L
      (properGenusClassOfOrdinaryRepresentative L C) = C := by
  let M := genusClassRepresentative L C
  let Cp := properGenusClassOfOrdinaryRepresentative L C
  have hCp_class : Cp.1 =
      (properGenusClassRepresentative L Cp).properGlobalIsometryClass :=
    (properGenusClassRepresentative_spec L Cp).2
  have hproper :
      M.IsProperGlobalIsometry (properGenusClassRepresentative L Cp) :=
    isProperGlobalIsometry_of_properGlobalIsometryClass_eq hCp_class
  apply Subtype.ext
  change
    (properGenusClassRepresentative L Cp).globalIsometryClass = C.1
  have hglobal :=
    globalIsometryClass_eq_of_isGlobalIsometry
      (isGlobalIsometry_of_isProperGlobalIsometry hproper)
  rw [genusClassRepresentative_globalIsometryClass L C]
  exact hglobal.symm

/-- A representative of a proper fibre is globally isometric to the chosen
ordinary representative of the base ordinary class. -/
lemma properGenusFiberRepresentative_isGlobalIsometry
    (L : PositiveDefiniteIntegralLattice n) (C : L.genus) (Cp : L.properGenusFiber C) :
    (properGenusClassRepresentative L Cp.1).IsGlobalIsometry
      (genusClassRepresentative L C) := by
  have hclass :
      (properGenusClassRepresentative L Cp.1).globalIsometryClass =
        (genusClassRepresentative L C).globalIsometryClass := by
    have hordinary := congrArg Subtype.val Cp.2
    change
      (properGenusClassRepresentative L Cp.1).globalIsometryClass =
        C.1 at hordinary
    rw [hordinary, genusClassRepresentative_globalIsometryClass L C]
  exact isGlobalIsometry_of_globalIsometryClass_eq hclass

/-- A chosen ordinary isometry from a proper-fibre representative to the chosen
ordinary representative of its ordinary class. -/
def properGenusFiberRepresentativeIsometryMatrix
    (L : PositiveDefiniteIntegralLattice n) (C : L.genus) (Cp : L.properGenusFiber C) :
    Matrix (Fin n) (Fin n) ℤ :=
  Classical.choose (properGenusFiberRepresentative_isGlobalIsometry L C Cp)

lemma properGenusFiberRepresentativeIsometryMatrix_spec
    (L : PositiveDefiniteIntegralLattice n) (C : L.genus) (Cp : L.properGenusFiber C) :
    IsUnit (properGenusFiberRepresentativeIsometryMatrix L C Cp) ∧
      (properGenusFiberRepresentativeIsometryMatrix L C Cp).transpose *
          (genusClassRepresentative L C).pairingMatrix *
          properGenusFiberRepresentativeIsometryMatrix L C Cp =
        (properGenusClassRepresentative L Cp.1).pairingMatrix :=
  Classical.choose_spec (properGenusFiberRepresentative_isGlobalIsometry L C Cp)

lemma properGenusFiberRepresentativeIsometryMatrix_det_isUnit
    (L : PositiveDefiniteIntegralLattice n) (C : L.genus) (Cp : L.properGenusFiber C) :
    IsUnit (properGenusFiberRepresentativeIsometryMatrix L C Cp).det := by
  have hunit := (properGenusFiberRepresentativeIsometryMatrix_spec L C Cp).1
  rwa [Matrix.isUnit_iff_isUnit_det] at hunit

/-- The determinant sign of a proper fibre representative, measured by a
chosen ordinary isometry to the chosen ordinary representative. -/
def properGenusFiberDetSign
    (L : PositiveDefiniteIntegralLattice n) (C : L.genus) (Cp : L.properGenusFiber C) : Bool :=
  decide ((properGenusFiberRepresentativeIsometryMatrix L C Cp).det = 1)

lemma properGenusFiber_eq_of_representativeIsometry_det_eq
    (L : PositiveDefiniteIntegralLattice n) (C : L.genus) (Cp Cp' : L.properGenusFiber C)
    (hdet :
      (properGenusFiberRepresentativeIsometryMatrix L C Cp).det =
        (properGenusFiberRepresentativeIsometryMatrix L C Cp').det) :
    Cp = Cp' := by
  let M := genusClassRepresentative L C
  let P := properGenusClassRepresentative L Cp.1
  let Q := properGenusClassRepresentative L Cp'.1
  let U := properGenusFiberRepresentativeIsometryMatrix L C Cp
  let V := properGenusFiberRepresentativeIsometryMatrix L C Cp'
  have hU_spec : IsUnit U ∧ U.transpose * M.pairingMatrix * U = P.pairingMatrix :=
    properGenusFiberRepresentativeIsometryMatrix_spec L C Cp
  have hV_spec : IsUnit V ∧ V.transpose * M.pairingMatrix * V = Q.pairingMatrix :=
    properGenusFiberRepresentativeIsometryMatrix_spec L C Cp'
  have hV_det_unit : IsUnit V.det := by
    have hunit : IsUnit V := hV_spec.1
    rwa [Matrix.isUnit_iff_isUnit_det] at hunit
  have hVinv_unit : IsUnit V⁻¹ := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_nonsing_inv]
    exact isUnit_ringInverse.mpr hV_det_unit
  have hV_mul_inv : V * V⁻¹ = 1 := Matrix.mul_nonsing_inv V hV_det_unit
  have hleft : (V⁻¹).transpose * V.transpose = 1 := by
    rw [← Matrix.transpose_mul, hV_mul_inv, Matrix.transpose_one]
  have hVinv_form : (V⁻¹).transpose * Q.pairingMatrix * V⁻¹ = M.pairingMatrix := by
    calc
      (V⁻¹).transpose * Q.pairingMatrix * V⁻¹ =
          (V⁻¹).transpose * (V.transpose * M.pairingMatrix * V) * V⁻¹ := by
        rw [hV_spec.2]
      _ = ((V⁻¹).transpose * V.transpose) * M.pairingMatrix * (V * V⁻¹) := by
        simp [Matrix.mul_assoc]
      _ = M.pairingMatrix := by
        rw [hleft, hV_mul_inv]
        simp
  have hproper : P.IsProperGlobalIsometry Q := by
    refine ⟨V⁻¹ * U, hVinv_unit.mul hU_spec.1, ?_, ?_⟩
    · calc
        (V⁻¹ * U).det = (V⁻¹).det * U.det := Matrix.det_mul _ _
        _ = Ring.inverse V.det * U.det := by rw [Matrix.det_nonsing_inv]
        _ = Ring.inverse V.det * V.det := by rw [hdet]
        _ = 1 := Ring.inverse_mul_cancel V.det hV_det_unit
    · calc
        (V⁻¹ * U).transpose * Q.pairingMatrix * (V⁻¹ * U) =
            U.transpose * ((V⁻¹).transpose * Q.pairingMatrix * V⁻¹) * U := by
          simp [Matrix.transpose_mul, Matrix.mul_assoc]
        _ = U.transpose * M.pairingMatrix * U := by
          rw [hVinv_form]
        _ = P.pairingMatrix := hU_spec.2
  have hproper_class :
      P.properGlobalIsometryClass = Q.properGlobalIsometryClass :=
    properGlobalIsometryClass_eq_of_isProperGlobalIsometry hproper
  apply Subtype.ext
  apply Subtype.ext
  have hCp_class : Cp.1.1 = P.properGlobalIsometryClass :=
    (properGenusClassRepresentative_spec L Cp.1).2
  have hCp'_class : Cp'.1.1 = Q.properGlobalIsometryClass :=
    (properGenusClassRepresentative_spec L Cp'.1).2
  change Cp.1.1 = Cp'.1.1
  rw [hCp_class, hCp'_class]
  exact hproper_class

/-- The determinant-sign map on a proper fibre is injective. -/
lemma properGenusFiberDetSign_injective
    (L : PositiveDefiniteIntegralLattice n) (C : L.genus) :
    Function.Injective (properGenusFiberDetSign L C) := by
  intro Cp Cp' hsign
  let U := properGenusFiberRepresentativeIsometryMatrix L C Cp
  let V := properGenusFiberRepresentativeIsometryMatrix L C Cp'
  have hU_det_unit :
      IsUnit (properGenusFiberRepresentativeIsometryMatrix L C Cp).det :=
    properGenusFiberRepresentativeIsometryMatrix_det_isUnit L C Cp
  have hV_det_unit :
      IsUnit (properGenusFiberRepresentativeIsometryMatrix L C Cp').det :=
    properGenusFiberRepresentativeIsometryMatrix_det_isUnit L C Cp'
  have hdet :
      (properGenusFiberRepresentativeIsometryMatrix L C Cp).det =
        (properGenusFiberRepresentativeIsometryMatrix L C Cp').det := by
    by_cases hU_one :
        (properGenusFiberRepresentativeIsometryMatrix L C Cp).det = 1
    · have hV_one :
          (properGenusFiberRepresentativeIsometryMatrix L C Cp').det = 1 := by
        by_contra hV_not
        simp [properGenusFiberDetSign, hU_one, hV_not] at hsign
      rw [hU_one, hV_one]
    · have hU_neg :
          (properGenusFiberRepresentativeIsometryMatrix L C Cp).det = -1 := by
        rcases Int.isUnit_iff.mp hU_det_unit with h | h
        · exact (hU_one h).elim
        · exact h
      have hV_not :
          ¬ (properGenusFiberRepresentativeIsometryMatrix L C Cp').det = 1 := by
        intro hV_one
        simp [properGenusFiberDetSign, hU_one, hV_one] at hsign
      have hV_neg :
          (properGenusFiberRepresentativeIsometryMatrix L C Cp').det = -1 := by
        rcases Int.isUnit_iff.mp hV_det_unit with h | h
        · exact (hV_not h).elim
        · exact h
      rw [hU_neg, hV_neg]
  exact properGenusFiber_eq_of_representativeIsometry_det_eq L C Cp Cp' hdet

/-- The fibre above an ordinary genus class is finite via determinant sign. -/
noncomputable instance properGenusFiber_fintype
    (L : PositiveDefiniteIntegralLattice n) (C : L.genus) :
    Fintype (L.properGenusFiber C) :=
  Fintype.ofInjective (properGenusFiberDetSign L C)
    (properGenusFiberDetSign_injective L C)

/-- Every proper fibre has at most the two determinant-sign classes. -/
theorem properGenusFiber_card_le_two
    (L : PositiveDefiniteIntegralLattice n) (C : L.genus) :
    Fintype.card (L.properGenusFiber C) ≤ 2 := by
  classical
  calc
    Fintype.card (L.properGenusFiber C) ≤ Fintype.card Bool :=
      Fintype.card_le_of_injective (properGenusFiberDetSign L C)
        (properGenusFiberDetSign_injective L C)
    _ = 2 := Fintype.card_bool

/-- The proper genus decomposes as the sigma of its fibres over ordinary genus
classes. -/
def properGenusSigmaFiberEquiv (L : PositiveDefiniteIntegralLattice n) :
    L.properGenus ≃ Σ C : L.genus, L.properGenusFiber C where
  toFun Cp := ⟨ordinaryClassOfProperGenusClass L Cp, ⟨Cp, rfl⟩⟩
  invFun x := x.2.1
  left_inv Cp := by
    rfl
  right_inv x := by
    rcases x with ⟨C, Cp, hCp⟩
    dsimp at hCp ⊢
    subst C
    rfl

/-- The proper genus can be used as a finite index type. -/
noncomputable instance properGenus_fintype (L : PositiveDefiniteIntegralLattice n) :
    Fintype L.properGenus :=
  Fintype.ofEquiv (Σ C : L.genus, L.properGenusFiber C)
    (L.properGenusSigmaFiberEquiv).symm

/-- The determinant-one proper genus is finite.  This is derived from
ordinary genus finiteness and the determinant-sign injection on each fibre. -/
theorem properGenus_finite (L : PositiveDefiniteIntegralLattice n) :
    L.properGenus.Finite := by
  classical
  exact Set.toFinite L.properGenus

/-- The proof-note proper genus mass, indexed by determinant-one proper
classes. -/
def properClassGenusMass (L : PositiveDefiniteIntegralLattice n) : ℚ :=
  ∑ C : L.properGenus,
    ((Fintype.card
      (properGenusClassRepresentative L C).ProperIsometryGroup : ℚ)⁻¹)

/-- The contribution of the determinant-one proper classes lying over one
ordinary genus class. -/
def properGenusFiberMass (L : PositiveDefiniteIntegralLattice n) (C : L.genus) : ℚ :=
  ∑ Cp : L.properGenusFiber C,
    ((Fintype.card
      (properGenusClassRepresentative L Cp.1).ProperIsometryGroup : ℚ)⁻¹)

/-- Each proper-class mass summand is positive. -/
lemma properClassGenusMass_summand_pos
    (L : PositiveDefiniteIntegralLattice n) (C : L.properGenus) :
    0 < ((Fintype.card
      (properGenusClassRepresentative L C).ProperIsometryGroup : ℚ)⁻¹) := by
  exact inv_pos.mpr (Nat.cast_pos.mpr
    ((properGenusClassRepresentative L C).properIsometryGroup_card_pos))

/-- The proof-note proper genus mass is positive. -/
theorem properClassGenusMass_pos (L : PositiveDefiniteIntegralLattice n) :
    0 < L.properClassGenusMass := by
  classical
  unfold properClassGenusMass
  refine Finset.sum_pos (fun C _ => properClassGenusMass_summand_pos L C) ?_
  exact ⟨⟨L.properGlobalIsometryClass, L.mem_properGenus_self⟩,
    Finset.mem_univ _⟩

/-- Reindex the proper-class mass as a sum over ordinary genus classes and
their determinant-one proper fibres. -/
lemma properClassGenusMass_eq_sum_fibers (L : PositiveDefiniteIntegralLattice n) :
    L.properClassGenusMass =
      ∑ C : L.genus, L.properGenusFiberMass C := by
  classical
  unfold properClassGenusMass
  calc
    (∑ Cp : L.properGenus,
        ((Fintype.card
          (properGenusClassRepresentative L Cp).ProperIsometryGroup : ℚ)⁻¹)) =
        ∑ x : Σ C : L.genus, L.properGenusFiber C,
          ((Fintype.card
            (properGenusClassRepresentative L x.2.1).ProperIsometryGroup : ℚ)⁻¹) := by
      refine Fintype.sum_equiv (L.properGenusSigmaFiberEquiv) _ _ ?_
      intro Cp
      rfl
    _ = ∑ C : L.genus, L.properGenusFiberMass C := by
      exact Fintype.sum_sigma
        (fun x : Σ C : L.genus, L.properGenusFiber C =>
          ((Fintype.card
            (properGenusClassRepresentative L x.2.1).ProperIsometryGroup : ℚ)⁻¹))

/-- In the orientation-reversing case, the proper fibre over an ordinary class
is explicitly equivalent to `Unit`. -/
def properGenusFiberEquivUnitOfHasOrientationReversing
    (L : PositiveDefiniteIntegralLattice n) (C : L.genus)
    (hrev : (genusClassRepresentative L C).HasOrientationReversingIsometry) :
    L.properGenusFiber C ≃ Unit where
  toFun _ := ()
  invFun _ :=
    ⟨properGenusClassOfOrdinaryRepresentative L C,
      ordinaryClassOf_properGenusClassOfOrdinaryRepresentative L C⟩
  left_inv Cp := by
    let M := genusClassRepresentative L C
    let P := properGenusClassRepresentative L Cp.1
    have hCp_class : Cp.1.1 = P.properGlobalIsometryClass :=
      (properGenusClassRepresentative_spec L Cp.1).2
    have hordinary := congrArg Subtype.val Cp.2
    change P.globalIsometryClass = C.1 at hordinary
    have hP_global_M : P.IsGlobalIsometry M :=
      isGlobalIsometry_of_globalIsometryClass_eq
        (by
          rw [hordinary, genusClassRepresentative_globalIsometryClass L C])
    have hP_proper_M : P.IsProperGlobalIsometry M :=
      isProperGlobalIsometry_of_isGlobalIsometry_of_hasOrientationReversing_target
        hP_global_M hrev
    have hP_class :
        P.properGlobalIsometryClass = M.properGlobalIsometryClass :=
      properGlobalIsometryClass_eq_of_isProperGlobalIsometry hP_proper_M
    apply Subtype.ext
    apply Subtype.ext
    change M.properGlobalIsometryClass = Cp.1.1
    rw [hCp_class]
    exact hP_class.symm
  right_inv u := by
    cases u
    rfl

/-- Over an ordinary class whose representative has a determinant-`-1`
automorphism there is exactly one determinant-one proper class. -/
theorem properGenusFiber_card_eq_one_of_hasOrientationReversing
    (L : PositiveDefiniteIntegralLattice n) (C : L.genus) :
    (genusClassRepresentative L C).HasOrientationReversingIsometry →
    Fintype.card (L.properGenusFiber C) = 1 := by
  classical
  intro hrev
  calc
    Fintype.card (L.properGenusFiber C) =
        Fintype.card Unit :=
      Fintype.card_congr
        (properGenusFiberEquivUnitOfHasOrientationReversing L C hrev)
    _ = 1 := by simp

/-- In the orientation-reversing case, the one-class fibre coverage plus the
formal stabilizer index computation give the fibre contribution. -/
theorem properGenusFiberMass_eq_two_ordinaryGenusMass_summand_of_hasOrientationReversing
    (L : PositiveDefiniteIntegralLattice n) (C : L.genus) :
    (genusClassRepresentative L C).HasOrientationReversingIsometry →
    L.properGenusFiberMass C =
      2 *
        ((Fintype.card
          (genusClassRepresentative L C).IsometryGroup : ℚ)⁻¹) := by
  classical
  intro hrev
  let M := genusClassRepresentative L C
  have hfiber_card :
      Fintype.card (L.properGenusFiber C) = 1 :=
    properGenusFiber_card_eq_one_of_hasOrientationReversing
      L C hrev
  have hsummand :
      ∀ Cp : L.properGenusFiber C,
        ((Fintype.card
          (properGenusClassRepresentative L Cp.1).ProperIsometryGroup : ℚ)⁻¹) =
          ((Fintype.card M.ProperIsometryGroup : ℚ)⁻¹) := by
    intro Cp
    apply ordinaryClassSOStabilizerMass_summand_eq_of_isGlobalIsometry
    have hclass :
        (properGenusClassRepresentative L Cp.1).globalIsometryClass =
          M.globalIsometryClass := by
      have hordinary := congrArg Subtype.val Cp.2
      change
        (properGenusClassRepresentative L Cp.1).globalIsometryClass =
          C.1 at hordinary
      rw [hordinary, genusClassRepresentative_globalIsometryClass L C]
    exact isGlobalIsometry_of_globalIsometryClass_eq hclass
  have hproper_ne :
      (Fintype.card M.ProperIsometryGroup : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt M.properIsometryGroup_card_pos)
  have hfiber :
      L.properGenusFiberMass C =
        ((Fintype.card M.ProperIsometryGroup : ℚ)⁻¹) := by
    unfold properGenusFiberMass
    calc
      (∑ Cp : L.properGenusFiber C,
          ((Fintype.card
            (properGenusClassRepresentative L Cp.1).ProperIsometryGroup : ℚ)⁻¹)) =
          ∑ _Cp : L.properGenusFiber C,
            ((Fintype.card M.ProperIsometryGroup : ℚ)⁻¹) := by
        exact Finset.sum_congr rfl (fun Cp _ => hsummand Cp)
      _ =
          (Fintype.card (L.properGenusFiber C) : ℚ) *
            ((Fintype.card M.ProperIsometryGroup : ℚ)⁻¹) := by
        simp
      _ = ((Fintype.card M.ProperIsometryGroup : ℚ)⁻¹) := by
        rw [hfiber_card]
        norm_num
  rw [hfiber]
  have hcard :
      (Fintype.card M.IsometryGroup : ℚ) =
        2 * (Fintype.card M.ProperIsometryGroup : ℚ) := by
    norm_num [M.isometryGroup_card_eq_two_mul_properIsometryGroup_card_of_hasOrientationReversing hrev]
  rw [hcard]
  field_simp [hproper_ne]

/-- A fixed determinant-`-1` integral basis change in positive rank. -/
def orientationReversingBasisChangeMatrix [Nonempty (Fin n)] :
    Matrix (Fin n) (Fin n) ℤ :=
  Matrix.diagonal fun i =>
    if i = Classical.arbitrary (Fin n) then (-1 : ℤ) else 1

lemma orientationReversingBasisChangeMatrix_det [Nonempty (Fin n)] :
    (orientationReversingBasisChangeMatrix (n := n)).det = -1 := by
  classical
  let a : Fin n := Classical.arbitrary (Fin n)
  rw [orientationReversingBasisChangeMatrix, Matrix.det_diagonal]
  change (∏ i : Fin n, (if i = a then (-1 : ℤ) else 1)) = -1
  rw [Finset.prod_eq_single a]
  · simp
  · intro b _ hb
    simp [hb]
  · intro ha
    exact (ha (Finset.mem_univ a)).elim

lemma orientationReversingBasisChangeMatrix_isUnit [Nonempty (Fin n)] :
    IsUnit (orientationReversingBasisChangeMatrix (n := n)) := by
  rw [Matrix.isUnit_iff_isUnit_det,
    orientationReversingBasisChangeMatrix_det]
  exact Int.isUnit_iff.mpr (Or.inr rfl)

lemma orientationReversingBasisChangeMatrix_real_det [Nonempty (Fin n)] :
    ((orientationReversingBasisChangeMatrix (n := n)).map
      (Int.cast : ℤ → ℝ)).det = -1 := by
  classical
  rw [orientationReversingBasisChangeMatrix]
  rw [Matrix.diagonal_map (show (Int.cast : ℤ → ℝ) 0 = 0 by norm_num)]
  rw [Matrix.det_diagonal]
  simp only [Int.cast_ite, Int.cast_neg, Int.cast_one]
  let a : Fin n := Classical.arbitrary (Fin n)
  change (∏ i : Fin n, (if i = a then (-1 : ℝ) else 1)) = -1
  rw [Finset.prod_eq_single a]
  · simp
  · intro b _ hb
    simp [hb]
  · intro ha
    exact (ha (Finset.mem_univ a)).elim

lemma orientationReversingBasisChangeMatrix_real_mulVec_injective
    [Nonempty (Fin n)] :
    Function.Injective
      ((orientationReversingBasisChangeMatrix (n := n)).map
        (Int.cast : ℤ → ℝ)).mulVec := by
  classical
  let B :=
    (orientationReversingBasisChangeMatrix (n := n)).map
      (Int.cast : ℤ → ℝ)
  have hdet : IsUnit B.det := by
    rw [show B.det = (-1 : ℝ) by
      exact orientationReversingBasisChangeMatrix_real_det]
    exact isUnit_iff_ne_zero.mpr (by norm_num : (-1 : ℝ) ≠ 0)
  intro x y hxy
  have hinv : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B hdet
  calc
    x = (1 : Matrix (Fin n) (Fin n) ℝ).mulVec x := by simp
    _ = (B⁻¹ * B).mulVec x := by rw [hinv]
    _ = B⁻¹.mulVec (B.mulVec x) := by rw [Matrix.mulVec_mulVec]
    _ = B⁻¹.mulVec (B.mulVec y) := by rw [hxy]
    _ = (B⁻¹ * B).mulVec y := by rw [Matrix.mulVec_mulVec]
    _ = (1 : Matrix (Fin n) (Fin n) ℝ).mulVec y := by rw [hinv]
    _ = y := by simp

lemma orientationReversingBasisChangeMatrix_posDef
    (M : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)] :
    (((orientationReversingBasisChangeMatrix (n := n)).transpose *
        M.pairingMatrix * orientationReversingBasisChangeMatrix).map
      (Int.cast : ℤ → ℝ)).PosDef := by
  classical
  let B :=
    (orientationReversingBasisChangeMatrix (n := n)).map
      (Int.cast : ℤ → ℝ)
  have h :=
    M.form_posDef.conjTranspose_mul_mul_same (B := B)
      (orientationReversingBasisChangeMatrix_real_mulVec_injective (n := n))
  convert h using 1
  ext i j
  simp [B, orientationReversingBasisChangeMatrix, Matrix.conjTranspose]

/-- The lattice obtained from `M` by the fixed determinant-`-1` basis change. -/
def orientationReversingBasisChangeLattice
    (M : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)] : PositiveDefiniteIntegralLattice n where
  pairingMatrix :=
    (orientationReversingBasisChangeMatrix (n := n)).transpose *
      M.pairingMatrix * orientationReversingBasisChangeMatrix
  form_symm := by
    rw [Matrix.IsSymm]
    calc
      ((orientationReversingBasisChangeMatrix (n := n)).transpose *
            M.pairingMatrix * orientationReversingBasisChangeMatrix).transpose =
          (orientationReversingBasisChangeMatrix (n := n)).transpose *
            M.pairingMatrix.transpose * orientationReversingBasisChangeMatrix := by
        simp [Matrix.transpose_mul, Matrix.mul_assoc]
      _ =
          (orientationReversingBasisChangeMatrix (n := n)).transpose *
            M.pairingMatrix * orientationReversingBasisChangeMatrix := by
        rw [M.form_symm.eq]
  form_posDef := orientationReversingBasisChangeMatrix_posDef M

lemma orientationReversingBasisChangeLattice_isGlobalIsometry
    (M : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)] :
    (orientationReversingBasisChangeLattice M).IsGlobalIsometry M := by
  exact
    ⟨orientationReversingBasisChangeMatrix,
      orientationReversingBasisChangeMatrix_isUnit, rfl⟩

lemma not_isProperGlobalIsometry_orientationReversingBasisChangeLattice
    (M : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (hno : ¬ M.HasOrientationReversingIsometry) :
    ¬ M.IsProperGlobalIsometry
      (orientationReversingBasisChangeLattice M) := by
  classical
  intro hproper
  rcases hproper with ⟨U, hU_unit, hU_det, hU_form⟩
  let R := orientationReversingBasisChangeMatrix (n := n)
  have hR_iso : M.IsIsometry (R * U) := by
    constructor
    · exact orientationReversingBasisChangeMatrix_isUnit.mul hU_unit
    · calc
        (R * U).transpose * M.pairingMatrix * (R * U) =
            U.transpose * (R.transpose * M.pairingMatrix * R) * U := by
          simp [R, Matrix.transpose_mul, Matrix.mul_assoc]
        _ = M.pairingMatrix := hU_form
  have hR_det : (R * U).det = -1 := by
    simp [R, Matrix.det_mul, orientationReversingBasisChangeMatrix_det,
      hU_det]
  exact hno ⟨R * U, hR_iso, hR_det⟩

/-- The proper class obtained by applying the determinant-`-1` basis change to
the chosen ordinary representative. -/
def properGenusClassOfOrientationReversingBasisChange
    (L : PositiveDefiniteIntegralLattice n) (C : L.genus) [Nonempty (Fin n)] :
    L.properGenus := by
  classical
  let M := genusClassRepresentative L C
  let P := orientationReversingBasisChangeLattice M
  refine ⟨P.properGlobalIsometryClass, ?_⟩
  refine ⟨P, ?_, rfl⟩
  have hM : L.IsSameGenus M := genusClassRepresentative_isSameGenus L C
  have hMP : M.IsGlobalIsometry P :=
    isGlobalIsometry_symm
      (orientationReversingBasisChangeLattice_isGlobalIsometry M)
  exact isSameGenus_trans hM (isSameGenus_of_isGlobalIsometry hMP)

/-- The determinant-`-1` basis-change proper class lies above the original
ordinary class. -/
lemma ordinaryClassOf_properGenusClassOfOrientationReversingBasisChange
    (L : PositiveDefiniteIntegralLattice n) (C : L.genus) [Nonempty (Fin n)] :
    ordinaryClassOfProperGenusClass L
      (properGenusClassOfOrientationReversingBasisChange L C) = C := by
  classical
  let M := genusClassRepresentative L C
  let P := orientationReversingBasisChangeLattice M
  let Cp := properGenusClassOfOrientationReversingBasisChange L C
  have hCp_class : Cp.1 =
      (properGenusClassRepresentative L Cp).properGlobalIsometryClass :=
    (properGenusClassRepresentative_spec L Cp).2
  have hclass :
      P.properGlobalIsometryClass =
        (properGenusClassRepresentative L Cp).properGlobalIsometryClass := by
    simpa [Cp, properGenusClassOfOrientationReversingBasisChange, P]
      using hCp_class
  have hP_proper :
      P.IsProperGlobalIsometry (properGenusClassRepresentative L Cp) :=
    isProperGlobalIsometry_of_properGlobalIsometryClass_eq hclass
  have hP_global_M : P.IsGlobalIsometry M :=
    orientationReversingBasisChangeLattice_isGlobalIsometry M
  have hQ_global_M :
      (properGenusClassRepresentative L Cp).IsGlobalIsometry M :=
    isGlobalIsometry_trans
      (isGlobalIsometry_symm
        (isGlobalIsometry_of_isProperGlobalIsometry hP_proper))
      hP_global_M
  apply Subtype.ext
  change
    (properGenusClassRepresentative L Cp).globalIsometryClass = C.1
  rw [genusClassRepresentative_globalIsometryClass L C]
  exact globalIsometryClass_eq_of_isGlobalIsometry hQ_global_M

def properGenusFiberOrientationReversingBasisChange
    (L : PositiveDefiniteIntegralLattice n) (C : L.genus) [Nonempty (Fin n)] :
    L.properGenusFiber C :=
  ⟨properGenusClassOfOrientationReversingBasisChange L C,
    ordinaryClassOf_properGenusClassOfOrientationReversingBasisChange L C⟩

lemma properGenusFiber_identity_ne_orientationReversingBasisChange
    (L : PositiveDefiniteIntegralLattice n) (C : L.genus) [Nonempty (Fin n)]
    (hno : ¬ (genusClassRepresentative L C).HasOrientationReversingIsometry) :
    (⟨properGenusClassOfOrdinaryRepresentative L C,
      ordinaryClassOf_properGenusClassOfOrdinaryRepresentative L C⟩ :
        L.properGenusFiber C) ≠
      properGenusFiberOrientationReversingBasisChange L C := by
  classical
  intro h
  let M := genusClassRepresentative L C
  let P := orientationReversingBasisChangeLattice M
  have hclass :
      M.properGlobalIsometryClass = P.properGlobalIsometryClass := by
    have hval :=
      congrArg (fun Cp : L.properGenusFiber C => Cp.1.1) h
    simpa [properGenusClassOfOrdinaryRepresentative,
      properGenusFiberOrientationReversingBasisChange,
      properGenusClassOfOrientationReversingBasisChange, M, P] using hval
  have hproper : M.IsProperGlobalIsometry P :=
    isProperGlobalIsometry_of_properGlobalIsometryClass_eq hclass
  exact
    not_isProperGlobalIsometry_orientationReversingBasisChangeLattice
      M hno hproper

/-- Fibre coverage in positive rank without orientation-reversing
automorphisms: over this ordinary class there are exactly two determinant-one
proper classes.

The determinant-sign map on the fibre is injective by
`properGenusFiberDetSign_injective`, so the positive-rank content is
surjectivity: both determinant signs must be represented.  The other sign is
obtained by applying a determinant-`-1` change of basis to the chosen ordinary
representative. -/
theorem properGenusFiber_card_eq_two_of_noOrientationReversing
    (L : PositiveDefiniteIntegralLattice n) (C : L.genus) [Nonempty (Fin n)] :
    ¬ (genusClassRepresentative L C).HasOrientationReversingIsometry →
    Fintype.card (L.properGenusFiber C) = 2 := by
  classical
  intro hno
  apply Nat.le_antisymm
  · exact properGenusFiber_card_le_two L C
  · have hlt : 1 < Fintype.card (L.properGenusFiber C) :=
      Fintype.one_lt_card_iff.mpr
        ⟨⟨properGenusClassOfOrdinaryRepresentative L C,
            ordinaryClassOf_properGenusClassOfOrdinaryRepresentative L C⟩,
          properGenusFiberOrientationReversingBasisChange L C,
          properGenusFiber_identity_ne_orientationReversingBasisChange
            L C hno⟩
    omega

/-- In the no-orientation-reversing case, the two-class fibre coverage plus the
formal stabilizer computation give the fibre contribution. -/
theorem properGenusFiberMass_eq_two_ordinaryGenusMass_summand_of_noOrientationReversing
    (L : PositiveDefiniteIntegralLattice n) (C : L.genus) [Nonempty (Fin n)] :
    ¬ (genusClassRepresentative L C).HasOrientationReversingIsometry →
    L.properGenusFiberMass C =
      2 *
        ((Fintype.card
          (genusClassRepresentative L C).IsometryGroup : ℚ)⁻¹) := by
  classical
  intro hno
  let M := genusClassRepresentative L C
  have hfiber_card :
      Fintype.card (L.properGenusFiber C) = 2 :=
    properGenusFiber_card_eq_two_of_noOrientationReversing
      L C hno
  have hsummand :
      ∀ Cp : L.properGenusFiber C,
        ((Fintype.card
          (properGenusClassRepresentative L Cp.1).ProperIsometryGroup : ℚ)⁻¹) =
          ((Fintype.card M.ProperIsometryGroup : ℚ)⁻¹) := by
    intro Cp
    apply ordinaryClassSOStabilizerMass_summand_eq_of_isGlobalIsometry
    have hclass :
        (properGenusClassRepresentative L Cp.1).globalIsometryClass =
          M.globalIsometryClass := by
      have hordinary := congrArg Subtype.val Cp.2
      change
        (properGenusClassRepresentative L Cp.1).globalIsometryClass =
          C.1 at hordinary
      rw [hordinary, genusClassRepresentative_globalIsometryClass L C]
    exact isGlobalIsometry_of_globalIsometryClass_eq hclass
  have hfiber :
      L.properGenusFiberMass C =
        2 * ((Fintype.card M.ProperIsometryGroup : ℚ)⁻¹) := by
    unfold properGenusFiberMass
    calc
      (∑ Cp : L.properGenusFiber C,
          ((Fintype.card
            (properGenusClassRepresentative L Cp.1).ProperIsometryGroup : ℚ)⁻¹)) =
          ∑ _Cp : L.properGenusFiber C,
            ((Fintype.card M.ProperIsometryGroup : ℚ)⁻¹) := by
        exact Finset.sum_congr rfl (fun Cp _ => hsummand Cp)
      _ =
          (Fintype.card (L.properGenusFiber C) : ℚ) *
            ((Fintype.card M.ProperIsometryGroup : ℚ)⁻¹) := by
        simp
      _ = 2 * ((Fintype.card M.ProperIsometryGroup : ℚ)⁻¹) := by
        rw [hfiber_card]
        norm_num
  rw [hfiber]
  have hcard :
      (Fintype.card M.IsometryGroup : ℚ) =
        (Fintype.card M.ProperIsometryGroup : ℚ) := by
    norm_num [M.isometryGroup_card_eq_properIsometryGroup_card_of_noOrientationReversing hno]
  rw [hcard]

/-- The fibre contribution follows by splitting on the determinant signs of
the ordinary automorphism group of the representative. -/
theorem properGenusFiberMass_eq_two_ordinaryGenusMass_summand
    (L : PositiveDefiniteIntegralLattice n) (C : L.genus) [Nonempty (Fin n)] :
    L.properGenusFiberMass C =
      2 *
        ((Fintype.card
          (genusClassRepresentative L C).IsometryGroup : ℚ)⁻¹) := by
  by_cases h : (genusClassRepresentative L C).HasOrientationReversingIsometry
  · exact
      properGenusFiberMass_eq_two_ordinaryGenusMass_summand_of_hasOrientationReversing
        L C h
  · exact
      properGenusFiberMass_eq_two_ordinaryGenusMass_summand_of_noOrientationReversing
        L C h

/-- The global determinant-sign splitting follows by summing the fibrewise
theorem over ordinary genus classes. -/
theorem properClassGenusMass_eq_two_ordinaryGenusMass
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)] :
    ((L.properClassGenusMass : ℚ) : ℝ) =
      2 * ((L.ordinaryGenusMass : ℚ) : ℝ) := by
  classical
  have hq : L.properClassGenusMass = 2 * L.ordinaryGenusMass := by
    rw [L.properClassGenusMass_eq_sum_fibers]
    unfold ordinaryGenusMass
    calc
      (∑ C : L.genus, L.properGenusFiberMass C) =
          ∑ C : L.genus,
            2 *
              ((Fintype.card
                (genusClassRepresentative L C).IsometryGroup : ℚ)⁻¹) := by
        refine Finset.sum_congr rfl ?_
        intro C _hC
        exact
          properGenusFiberMass_eq_two_ordinaryGenusMass_summand
            L C
      _ = 2 * ∑ C : L.genus,
            ((Fintype.card
              (genusClassRepresentative L C).IsometryGroup : ℚ)⁻¹) := by
        rw [Finset.mul_sum]
  rw [hq]
  norm_num

end PositiveDefiniteIntegralLattice

end
