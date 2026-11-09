import SMSFormula.RationalCliffordGeneralSpinSpinorNorm

/-!
# The fieldwise intrinsic general-Spin similitude image

For a characteristic-zero field, an invertible scalar occurs as the reverse
norm of an intrinsic general-Spin point exactly when its square class occurs
as the spinor norm of a special-orthogonal point.  One direction is the
already proved commutative right square of the crossed diagram.  Conversely,
surjectivity onto `SO` gives a general-Spin lift; the square-class discrepancy
is removed by multiplying that lift by a central scalar point.

This is the common algebraic reduction used by the rational and local
similitude-image calculations in the crossed cutoff argument.
-/

noncomputable section

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)
variable (K : Type*) [Field K] [CharZero K] [Algebra ℚ K]

namespace CliffordGeneralSpinIntrinsicPoint

/-- The exact fieldwise similitude image: it is the inverse image, under
passage to square classes, of the special-orthogonal spinor-norm image. -/
theorem range_similitudeGroupHom_eq_squareClass_comap_spinorNorm_range :
    (similitudeGroupHom V K).range =
      (V.specialOrthogonalSpinorNormHom K).range.comap
        (QuotientGroup.mk' (Subgroup.square Kˣ)) := by
  ext a
  constructor
  · rintro ⟨x, rfl⟩
    change similitudeSquareClassGroupHom V K x ∈
      (V.specialOrthogonalSpinorNormHom K).range
    refine ⟨toSpecialOrthogonalGroupHom V K x, ?_⟩
    exact
      (specialOrthogonalSpinorNorm_matrixGroup_eq_similitudeSquareClass
        V K x)
  · intro ha
    change ((a : Kˣ) : Rat.SquareClass K) ∈
      (V.specialOrthogonalSpinorNormHom K).range at ha
    obtain ⟨g, hg⟩ := ha
    obtain ⟨x, hx⟩ := toSpecialOrthogonalGroupHom_surjective V K g
    have hclass :
        (((a : Kˣ)) : Rat.SquareClass K) =
          (((x.similitude : Kˣ)) : Rat.SquareClass K) := by
      calc
        (((a : Kˣ)) : Rat.SquareClass K) =
            V.specialOrthogonalSpinorNormHom K g := hg.symm
        _ = V.specialOrthogonalSpinorNormHom K x.matrixGroup := by
          rw [← hx]
          rfl
        _ = (((x.similitude : Kˣ)) : Rat.SquareClass K) :=
          specialOrthogonalSpinorNorm_matrixGroup_eq_similitudeSquareClass
            V K x
    have hsq : a / x.similitude ∈ Subgroup.square Kˣ :=
      QuotientGroup.eq_iff_div_mem.mp hclass
    rw [Subgroup.mem_square] at hsq
    obtain ⟨z, hz⟩ := hsq
    refine ⟨ofScalar V K z * x, ?_⟩
    change z ^ 2 * x.similitude = a
    rw [pow_two, ← hz]
    simp

end CliffordGeneralSpinIntrinsicPoint

end RationalQuadraticSpaceMatrix
