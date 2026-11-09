import SMSFormula.Mass
import SMSFormula.StandardAxiomsGuard

/-!
# Ordinary genus mass in rank one

Every positive integral rank-one lattice has one ordinary genus class and
two integral isometries. No unimodularity or primitive-content assumption
is needed. The resulting mass is the ordinary full-O mass.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

/-- Local isometry at every place determines the actual based lattice in
rank one, since its sole quadratic matrix entry is its determinant. -/
theorem isSameGenus_iff_eq_rank_one (L M : PositiveDefiniteIntegralLattice 1) :
    L.IsSameGenus M ↔ L = M := by
  constructor
  · intro h
    exact rank_one_eq_of_pairingDeterminant_eq
      (pairingDeterminant_eq_of_isSameGenus L M h)
  · rintro rfl
    exact L.isSameGenus_refl

/-- Every rank-one ordinary genus has exactly one global isometry class. -/
theorem genus_card_rank_one (L : PositiveDefiniteIntegralLattice 1) :
    Fintype.card L.genus = 1 := by
  classical
  have same (C : L.genus) : C.1 = L.globalIsometryClass := by
    obtain ⟨M, hM, hC⟩ := C.2
    exact hC.trans (congrArg globalIsometryClass
      ((isSameGenus_iff_eq_rank_one L M).mp hM).symm)
  rw [Fintype.card_eq_one_iff]
  exact ⟨⟨L.globalIsometryClass, L.mem_genus_self⟩,
    fun C => Subtype.ext (same C)⟩

private def rankOneIsometryGroupEquivBool (L : PositiveDefiniteIntegralLattice 1) :
    L.IsometryGroup ≃ Bool where
  toFun U := decide (U.1 0 0 = (-1 : ℤ))
  invFun b := if b then
      ⟨(-1 : Matrix (Fin 1) (Fin 1) ℤ), by
        constructor
        · rw [Matrix.isUnit_iff_isUnit_det]
          simp
        · simp
      ⟩
    else
      ⟨1, by
        constructor
        · exact isUnit_one
        · simp
      ⟩
  left_inv U := by
    apply Subtype.ext
    ext i j
    fin_cases i
    fin_cases j
    have hu : IsUnit (U.1 0 0) := by
      have hdet := U.2.1
      rw [Matrix.isUnit_iff_isUnit_det] at hdet
      simpa [Matrix.det_fin_one] using hdet
    rcases Int.isUnit_iff.mp hu with hpos | hneg
    · simp [hpos]
    · simp [hneg]
  right_inv b := by
    cases b <;> simp

/-- The full integral orthogonal group of every rank-one lattice has order two. -/
theorem isometryGroup_card_rank_one (L : PositiveDefiniteIntegralLattice 1) :
    Fintype.card L.IsometryGroup = 2 := by
  classical
  rw [← Fintype.card_bool]
  exact Fintype.card_congr (rankOneIsometryGroupEquivBool L)

/-- The ordinary full-O genus mass in rank one is always one half. -/
theorem ordinaryGenusMass_eq_one_half_rank_one (L : PositiveDefiniteIntegralLattice 1) :
    L.ordinaryGenusMass = (1 / 2 : ℚ) := by
  classical
  unfold ordinaryGenusMass
  simp_rw [isometryGroup_card_rank_one]
  rw [Finset.sum_const, Finset.card_univ, genus_card_rank_one]
  norm_num

end PositiveDefiniteIntegralLattice

#assert_standard_axioms PositiveDefiniteIntegralLattice.isSameGenus_iff_eq_rank_one
#assert_standard_axioms PositiveDefiniteIntegralLattice.genus_card_rank_one
#assert_standard_axioms PositiveDefiniteIntegralLattice.isometryGroup_card_rank_one
#assert_standard_axioms PositiveDefiniteIntegralLattice.ordinaryGenusMass_eq_one_half_rank_one
