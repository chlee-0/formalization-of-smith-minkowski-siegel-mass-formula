import SMSFormula.RationalOrthogonalSubmersiveCharts
import SMSFormula.RationalSpinReducedTargetInjectivity
import SMSFormula.SmoothAlgebraReduced

/-!
# Reducedness of the rational special-orthogonal carrier

The completed independent-Jacobian charts prove that the existing rational
special-orthogonal coordinate algebra is smooth over `ℚ`.  The generic
smooth-over-a-field theorem makes that coordinate algebra reduced.

Combining reducedness with the already proved surjectivity on prime spectra
removes the nilpotent obstruction and proves that the affine coordinate map

```text
O(SO_V) → O(SpinCandidate_V)
```

is injective without an additional hypothesis.  Faithful flatness still
requires the independent Takeuchi--Waterhouse theorem for injective maps of
commutative Hopf algebras over a field; it is not inferred here.
-/

noncomputable section

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

/-- The existing special-orthogonal coordinate ring is reduced. -/
theorem specialOrthogonalCoordinateRing_isReduced :
    IsReduced V.specialOrthogonalCoordinateRing :=
  RingHom.Smooth.isReduced_of_field
    (algebraMap ℚ V.specialOrthogonalCoordinateRing)
      (RingHom.smooth_algebraMap.mpr V.specialOrthogonalCoordinateRing_smooth)

/-- The coordinate homomorphism of the affine Spin-candidate cover is
injective, unconditionally. -/
theorem specialOrthogonalToCliffordSpinCandidateCoordinateRingHom_injective :
    Function.Injective
      V.specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom.toRingHom := by
  letI : IsReduced V.specialOrthogonalCoordinateRing :=
    V.specialOrthogonalCoordinateRing_isReduced
  exact V.specialOrthogonalToCliffordSpinCandidateCoordinateRingHom_injective_of_isReduced

end RationalQuadraticSpaceMatrix
