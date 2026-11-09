import SMSFormula.RationalIdeleModuleContinuity

/-!
# The module on rational idele classes

The product formula places the rational diagonal in the kernel of the idele
module.  Consequently the positive module and logarithmic module descend to
the literal quotient of ideles by rational units.  This is the one-dimensional
base used by the compact crossed `GSpin` cutoff.
-/

noncomputable section

open PositiveDefiniteIntegralLattice

namespace RationalQuadraticSpaceMatrix

/-- The rational diagonal subgroup of the full idele group. -/
def rationalIdeleDiagonalSubgroup : Subgroup (Units RationalAdele) :=
  rationalUnitFullAdelicDiagonalHom.range

/-- Rational idele classes modulo the rational diagonal. -/
abbrev RationalIdeleClassGroup :=
  (Units RationalAdele) ⧸ rationalIdeleDiagonalSubgroup

theorem rationalIdeleDiagonalSubgroup_le_module_ker :
    rationalIdeleDiagonalSubgroup ≤ rationalIdeleModuleHom.ker := by
  rintro a ⟨q, rfl⟩
  change rationalIdeleModuleHom
      (rationalUnitFullAdelicDiagonalHom q) = 1
  apply Units.ext
  exact rationalIdeleModuleNNReal_rationalUnitDiagonal q

/-- The positive idele module descended to rational idele classes. -/
def rationalIdeleClassModuleHom : RationalIdeleClassGroup →* NNRealˣ :=
  QuotientGroup.lift rationalIdeleDiagonalSubgroup rationalIdeleModuleHom
    rationalIdeleDiagonalSubgroup_le_module_ker

@[simp]
theorem rationalIdeleClassModuleHom_mk (a : RationalAdeleˣ) :
    rationalIdeleClassModuleHom
        (QuotientGroup.mk' rationalIdeleDiagonalSubgroup a) =
      rationalIdeleModuleHom a :=
  QuotientGroup.lift_mk _ _ a

/-- The logarithmic module on rational idele classes. -/
def rationalIdeleClassLogModule (c : RationalIdeleClassGroup) : ℝ :=
  Real.log ((rationalIdeleClassModuleHom c : NNReal) : ℝ)

@[simp]
theorem rationalIdeleClassLogModule_mk (a : RationalAdeleˣ) :
    rationalIdeleClassLogModule
        (QuotientGroup.mk' rationalIdeleDiagonalSubgroup a) =
      rationalIdeleLogModule a :=
  rfl

theorem rationalIdeleClassLogModule_mul
    (a b : RationalIdeleClassGroup) :
    rationalIdeleClassLogModule (a * b) =
      rationalIdeleClassLogModule a + rationalIdeleClassLogModule b := by
  induction a using QuotientGroup.induction_on with
  | _ a =>
    induction b using QuotientGroup.induction_on with
    | _ b =>
      simpa only [← map_mul, rationalIdeleClassLogModule_mk] using
        rationalIdeleLogModule_mul a b

/-- Squaring doubles the descended logarithmic module. -/
theorem rationalIdeleClassLogModule_sq (a : RationalIdeleClassGroup) :
    rationalIdeleClassLogModule (a ^ 2) =
      2 * rationalIdeleClassLogModule a := by
  rw [pow_two, rationalIdeleClassLogModule_mul]
  ring

theorem continuous_rationalIdeleClassLogModule :
    Continuous rationalIdeleClassLogModule := by
  have hrel : ∀ (a b : RationalAdeleˣ),
      QuotientGroup.leftRel rationalIdeleDiagonalSubgroup a b →
      rationalIdeleLogModule a = rationalIdeleLogModule b := by
    intro a b hab
    have hq : (QuotientGroup.mk' rationalIdeleDiagonalSubgroup a) =
        QuotientGroup.mk' rationalIdeleDiagonalSubgroup b :=
      Quotient.sound hab
    exact congrArg rationalIdeleClassLogModule hq
  let f : RationalIdeleClassGroup → ℝ :=
    Quotient.lift rationalIdeleLogModule hrel
  have hf : f = rationalIdeleClassLogModule := by
    funext c
    induction c using Quotient.inductionOn with
    | _ a => rfl
  rw [← hf]
  exact Continuous.quotient_lift continuous_rationalIdeleLogModule hrel

end RationalQuadraticSpaceMatrix
