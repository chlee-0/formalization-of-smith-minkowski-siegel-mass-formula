import SMSFormula.RationalCliffordGeneralSpinAdelicSpecialOrthogonalQuotient
import SMSFormula.RationalCliffordGeneralSpinIdeleClassScalarMap

/-!
# The central idele-class action on the adelic general-Spin quotient

Central adelic scalars act on `GSpin(Q)\GSpin(A)`.  Rational scalar ideles
act trivially, so the action descends to rational idele classes.  Its orbits
are exactly the fibers of the horizontal projection to `SO(Q)\SO(A)`.

This is a carrier statement only.  It supplies the action consumed by the
horizontal crossed measure construction without choosing a section of the
`SO` quotient.
-/

noncomputable section

open PositiveDefiniteIntegralLattice

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

set_option synthInstance.maxHeartbeats 200000

/-- Central scalar points commute with every intrinsic general-Spin point. -/
theorem cliffordGeneralSpin_scalar_commutes
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (a : Aˣ) (x : V.CliffordGeneralSpinIntrinsicPoint A) :
    CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V A a * x =
      x * CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V A a := by
  apply CliffordGeneralSpinIntrinsicPoint.ext_cliffordUnit V A
  apply Units.ext
  change algebraMap A (V.cliffordCoordinateBaseChangeAlgebra A) (a : A) *
      (x.cliffordUnit : V.cliffordCoordinateBaseChangeAlgebra A) =
    (x.cliffordUnit : V.cliffordCoordinateBaseChangeAlgebra A) *
      algebraMap A (V.cliffordCoordinateBaseChangeAlgebra A) (a : A)
  exact Algebra.commutes (a : A)
    (x.cliffordUnit : V.cliffordCoordinateBaseChangeAlgebra A)

/-- Action of an adelic scalar representative on the rational general-Spin
left quotient. -/
def fullAdelicCliffordGeneralSpinLeftQuotientScalarActionOfIdele
    (a : RationalAdeleˣ) :
    V.FullAdelicCliffordGeneralSpinLeftQuotient →
      V.FullAdelicCliffordGeneralSpinLeftQuotient :=
  Quot.lift
    (fun x => V.fullAdelicCliffordGeneralSpinLeftQuotientMap
      (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
        V RationalAdele a * x)) (by
        intro x y hxy
        rcases hxy with ⟨gamma, rfl⟩
        change V.fullAdelicCliffordGeneralSpinLeftQuotientMap
            (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
              V RationalAdele a * x) =
          V.fullAdelicCliffordGeneralSpinLeftQuotientMap
            (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
              V RationalAdele a *
                ((gamma : V.FullAdelicCliffordGeneralSpinGroup) * x))
        rw [← mul_assoc,
          V.cliffordGeneralSpin_scalar_commutes RationalAdele a gamma]
        rw [mul_assoc]
        exact (leftCosetMap_gamma_mul
          V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup gamma
          (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
            V RationalAdele a * x)).symm)

@[simp]
theorem fullAdelicCliffordGeneralSpinLeftQuotientScalarActionOfIdele_mk
    (a : RationalAdeleˣ)
    (x : V.FullAdelicCliffordGeneralSpinGroup) :
    V.fullAdelicCliffordGeneralSpinLeftQuotientScalarActionOfIdele a
        (V.fullAdelicCliffordGeneralSpinLeftQuotientMap x) =
      V.fullAdelicCliffordGeneralSpinLeftQuotientMap
        (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
          V RationalAdele a * x) :=
  rfl

/-- The adelic scalar action depends only on the rational idele class. -/
def rationalIdeleClassActionOnFullAdelicCliffordGeneralSpinLeftQuotient :
    RationalIdeleClassGroup →
      V.FullAdelicCliffordGeneralSpinLeftQuotient →
        V.FullAdelicCliffordGeneralSpinLeftQuotient :=
  Quot.lift
    (fun a => V.fullAdelicCliffordGeneralSpinLeftQuotientScalarActionOfIdele a)
    (by
      intro a b hab
      have hclass : QuotientGroup.mk' rationalIdeleDiagonalSubgroup a =
          QuotientGroup.mk' rationalIdeleDiagonalSubgroup b :=
        Quotient.sound hab
      have hdiv : a / b ∈ rationalIdeleDiagonalSubgroup :=
        (QuotientGroup.eq_iff_div_mem).mp hclass
      rcases hdiv with ⟨q, hq⟩
      have hab' : a = rationalUnitFullAdelicDiagonalHom q * b := by
        calc
          a = (a / b) * b := by simp
          _ = rationalUnitFullAdelicDiagonalHom q * b := by rw [hq]
      funext z
      induction z using Quot.inductionOn with
      | _ x =>
        change V.fullAdelicCliffordGeneralSpinLeftQuotientMap
            (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
              V RationalAdele a * x) =
          V.fullAdelicCliffordGeneralSpinLeftQuotientMap
            (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
              V RationalAdele b * x)
        rw [hab', map_mul,
          V.rational_fullAdelic_diagonal_generalSpinScalar]
        rw [mul_assoc]
        exact leftCosetMap_gamma_mul
          V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup
          ⟨V.rationalCliffordGeneralSpinFullAdelicDiagonalHom
              (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V ℚ q),
            ⟨CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V ℚ q,
              rfl⟩⟩
          (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
            V RationalAdele b * x))

@[simp]
theorem rationalIdeleClassActionOnFullAdelicCliffordGeneralSpinLeftQuotient_mk
    (a : RationalAdeleˣ)
    (x : V.FullAdelicCliffordGeneralSpinGroup) :
    V.rationalIdeleClassActionOnFullAdelicCliffordGeneralSpinLeftQuotient
        (QuotientGroup.mk' rationalIdeleDiagonalSubgroup a)
        (V.fullAdelicCliffordGeneralSpinLeftQuotientMap x) =
      V.fullAdelicCliffordGeneralSpinLeftQuotientMap
        (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
          V RationalAdele a * x) :=
  rfl

/-- The central idele-class action does not change the horizontal `SO`
quotient point. -/
theorem fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal_scalarAction
    (c : RationalIdeleClassGroup)
    (z : V.FullAdelicCliffordGeneralSpinLeftQuotient) :
    V.fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal
        (V.rationalIdeleClassActionOnFullAdelicCliffordGeneralSpinLeftQuotient
          c z) =
      V.fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal z := by
  induction c using QuotientGroup.induction_on with
  | _ a =>
    induction z using Quot.inductionOn with
    | _ x =>
      change V.fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal
          (V.fullAdelicCliffordGeneralSpinLeftQuotientScalarActionOfIdele a
            (V.fullAdelicCliffordGeneralSpinLeftQuotientMap x)) =
        V.fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal
          (V.fullAdelicCliffordGeneralSpinLeftQuotientMap x)
      rw [V.fullAdelicCliffordGeneralSpinLeftQuotientScalarActionOfIdele_mk,
        V.fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal_mk,
        V.fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal_mk,
        map_mul]
      have haKer : CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
          V RationalAdele a ∈
            (CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom
              V RationalAdele).ker := by
        rw [← CliffordGeneralSpinIntrinsicPoint.range_scalarGroupHom_eq_ker_toSpecialOrthogonalGroupHom
          V RationalAdele]
        exact ⟨a, rfl⟩
      change V.fullAdelicCliffordGeneralSpinToSpecialOrthogonalHom
          (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
            V RationalAdele a) = 1 at haKer
      rw [haKer, one_mul]

/-- The orbits of the central rational idele-class action are exactly the
fibers of the horizontal map to the rational `SO` quotient. -/
theorem fullAdelicCliffordGeneralSpinLeftQuotient_sameSO_iff_ideleClassOrbit
    (z w : V.FullAdelicCliffordGeneralSpinLeftQuotient) :
    V.fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal z =
        V.fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal w ↔
      ∃ c : RationalIdeleClassGroup,
        w = V.rationalIdeleClassActionOnFullAdelicCliffordGeneralSpinLeftQuotient
          c z := by
  induction z using Quot.inductionOn with
  | _ x =>
    induction w using Quot.inductionOn with
    | _ y =>
      constructor
      · intro hxy
        obtain ⟨a, ha⟩ :=
          (V.fullAdelicCliffordGeneralSpinLeftQuotient_image_eq_iff_scalar
            x y).1 hxy
        exact ⟨QuotientGroup.mk' rationalIdeleDiagonalSubgroup a, ha⟩
      · rintro ⟨c, hc⟩
        rw [hc]
        exact
          V.fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal_scalarAction
            c (V.fullAdelicCliffordGeneralSpinLeftQuotientMap x) |>.symm

end RationalQuadraticSpaceMatrix
