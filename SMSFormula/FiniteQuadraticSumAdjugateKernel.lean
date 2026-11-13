import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# The adjugate kernel bound

The admissibility proof for the fixed-width spatial test family rests on a finite affine
quadratic-sum bound `|G_q| <= |det H|^(n/2) q^(-n/2)`.  Squaring and applying finite character
orthogonality reduces that to `#ker(H mod q) <= C_H` with `C_H` independent of the conductor `q`,
and the answer identifies the cheapest proof of the latter: the adjugate.

This file holds that step, and it is the reusable part.  Over any commutative ring, `adj(M) M =
det(M) . 1` forces every vector killed by `M` to be killed by the scalar `det M`.  Reducing an
integral matrix modulo `q` and using that reduction commutes with the determinant, the kernel of
`H mod q` is therefore contained in the `det H`-torsion, coordinatewise -- a condition that involves
`q` only through reduction.  Bounding the kernel by a power of the scalar torsion count then makes
the conductor dependence explicit.

Why this is the right shape: the generic conductor contributes nothing.  Whenever `q` is coprime to
`det H` the reduced determinant is a unit and the kernel is trivial, so the bound bites only at the
conductors sharing a factor with the discriminant data.  That is recorded below.

Negative scope: this is the kernel step alone.  The squaring/orthogonality reduction and the
summation by conductor are not done here, no character sum is estimated, and the remaining generic
input -- the cardinality of the scalar `det H`-torsion in `ZMod q`, classically `gcd(det H, q)` --
is isolated below rather than proved, so no numerical bound is claimed.
-/

namespace SMSFormula.FiniteQuadraticSum

open Matrix

/-- The adjugate step, over any commutative ring: a vector in the kernel of `M` is killed by the
scalar `det M`.  This is `adj(M) M = det(M) . 1` applied to the vector. -/
theorem det_smul_eq_zero_of_mulVec_eq_zero {R : Type*} [CommRing R]
    {m : Type*} [Fintype m] [DecidableEq m]
    (M : Matrix m m R) {h : m → R} (hh : M *ᵥ h = 0) : M.det • h = 0 := by
  have h1 : M.adjugate *ᵥ (M *ᵥ h) = 0 := by rw [hh, Matrix.mulVec_zero]
  rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul] at h1
  rwa [show (M.det • (1 : Matrix m m R)) *ᵥ h = M.det • h by
    simp [Matrix.smul_mulVec, Matrix.one_mulVec]] at h1

/-- Reduced modulo a conductor: the kernel of an integral matrix mod `q` lies in the `det H`-torsion
coordinatewise, with the determinant computed over the integers and only then reduced. -/
theorem mul_eq_zero_of_mulVec_eq_zero_mod {m : Type*} [Fintype m] [DecidableEq m]
    (q : ℕ) (H : Matrix m m ℤ) {h : m → ZMod q}
    (hh : (H.map (Int.cast : ℤ → ZMod q)) *ᵥ h = 0) (i : m) :
    ((H.det : ℤ) : ZMod q) * h i = 0 := by
  have hdet : (H.map (Int.cast : ℤ → ZMod q)).det = ((H.det : ℤ) : ZMod q) :=
    (RingHom.map_det (Int.castRingHom (ZMod q)) H).symm
  have hkey := det_smul_eq_zero_of_mulVec_eq_zero (H.map (Int.cast : ℤ → ZMod q)) hh
  rw [hdet] at hkey
  have := congrFun hkey i
  simpa [Pi.smul_apply, smul_eq_mul] using this

/-- The generic conductor contributes nothing: if the reduced determinant is a unit -- in
particular whenever `q` is coprime to `det H` -- the kernel is trivial.  So the bound is only ever
about the conductors sharing a factor with the determinant. -/
theorem mulVec_eq_zero_iff_of_isUnit_det {m : Type*} [Fintype m] [DecidableEq m]
    (q : ℕ) (H : Matrix m m ℤ) (hunit : IsUnit ((H.det : ℤ) : ZMod q)) {h : m → ZMod q}
    (hh : (H.map (Int.cast : ℤ → ZMod q)) *ᵥ h = 0) : h = 0 := by
  funext i
  have hi := mul_eq_zero_of_mulVec_eq_zero_mod q H hh i
  obtain ⟨u, hu⟩ := hunit
  have : (u : ZMod q) * h i = 0 := by rw [hu]; exact hi
  simpa using congrArg (fun z ↦ (↑u⁻¹ : ZMod q) * z) this

/-- The kernel bound, with the conductor dependence isolated: the kernel injects coordinatewise
into the scalar `det H`-torsion, so its cardinality is at most the `n`-th power of that torsion's
cardinality.  Only the scalar count remains, and it is the classical `gcd(det H, q)`. -/
theorem card_kernel_le {m : Type*} [Fintype m] [DecidableEq m]
    (q : ℕ) [NeZero q] (H : Matrix m m ℤ) :
    Nat.card {h : m → ZMod q // (H.map (Int.cast : ℤ → ZMod q)) *ᵥ h = 0} ≤
      Nat.card (m → {x : ZMod q // ((H.det : ℤ) : ZMod q) * x = 0}) := by
  refine Nat.card_le_card_of_injective
    (fun h ↦ fun i ↦ ⟨h.1 i, mul_eq_zero_of_mulVec_eq_zero_mod q H h.2 i⟩) ?_
  intro h h' hEq
  refine Subtype.ext (funext fun i ↦ ?_)
  exact congrArg Subtype.val (congrFun hEq i)

end SMSFormula.FiniteQuadraticSum
