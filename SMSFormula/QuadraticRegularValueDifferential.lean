import SMSFormula.QuadraticCartanDieudonneOrthogonal
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Topology.Algebra.Module.FiniteDimension

noncomputable section

namespace QuadraticMap

variable {field space : Type*} [NontriviallyNormedField field] [CompleteSpace field]
  [NormedAddCommGroup space] [NormedSpace field space] [FiniteDimensional field space]

def valueDifferential (form : QuadraticForm field space) (point : space) :
    space →L[field] field :=
  LinearMap.toContinuousLinearMap (form.polarBilin point)

theorem valueDifferential_apply (form : QuadraticForm field space) (point tangent : space) :
    form.valueDifferential point tangent = polar form point tangent := rfl

theorem hasStrictFDerivAt_valueDifferential [Invertible (2 : field)]
    (form : QuadraticForm field space) (point : space) :
    HasStrictFDerivAt form (form.valueDifferential point) point := by
  let bilinear : space →L[field] space →L[field] field :=
    LinearMap.toContinuousLinearMap
      (LinearMap.toContinuousLinearMap.toLinearMap.comp form.associated)
  have hderivative := bilinear.hasStrictFDerivAt_of_bilinear
    (hasStrictFDerivAt_id point) (hasStrictFDerivAt_id point)
  have hfunction : (fun value => bilinear value value) = form := by
    funext value
    exact form.associated_eq_self_apply ℕ value
  simp only [id_eq] at hderivative
  rw [hfunction] at hderivative
  have hlinear : bilinear.precompR space point (ContinuousLinearMap.id field space) +
      bilinear.precompL space (ContinuousLinearMap.id field space) point =
      form.valueDifferential point := by
    ext tangent
    change form.associated point tangent + form.associated tangent point =
      form.polarBilin point tangent
    rw [← QuadraticMap.associated_isSymm field form point tangent]
    have hpolar := congrArg (fun pairing => pairing point tangent)
      (form.two_nsmul_associated field)
    simpa only [two_smul, LinearMap.add_apply] using hpolar
  rw [hlinear] at hderivative
  exact hderivative

def valueDifferentialRightInverse (form : QuadraticForm field space) (point : space) :
    field →L[field] space :=
  (ContinuousLinearMap.id field field).smulRight ((2 * form point)⁻¹ • point)

theorem valueDifferential_rightInverse [CharZero field]
    (form : QuadraticForm field space) (point : space) (hpoint : form point ≠ 0) :
    Function.RightInverse (form.valueDifferentialRightInverse point)
      (form.valueDifferential point) := by
  intro value
  change form.polarBilin point (value • ((2 * form point)⁻¹ • point)) = value
  rw [map_smul, map_smul]
  simp only [polarBilin_apply_apply, polar_self, smul_eq_mul, nsmul_eq_mul,
    Nat.cast_ofNat]
  rw [inv_mul_cancel₀ (mul_ne_zero two_ne_zero hpoint), mul_one]

theorem valueDifferential_surjective [CharZero field]
    (form : QuadraticForm field space) (point : space) (hpoint : form point ≠ 0) :
    Function.Surjective (form.valueDifferential point) :=
  (form.valueDifferential_rightInverse point hpoint).surjective

theorem valueDifferential_ker [CharZero field]
    (form : QuadraticForm field space) (point : space) :
    (form.valueDifferential point).ker = form.anisotropicOrthogonal point := by
  ext tangent
  rw [LinearMap.mem_ker, form.mem_anisotropicOrthogonal_iff]
  change form.polarBilin point tangent = 0 ↔ form.associated point tangent = 0
  rw [← form.two_nsmul_associated ℕ]
  simp [two_smul, ← two_mul, mul_eq_zero]

end QuadraticMap
