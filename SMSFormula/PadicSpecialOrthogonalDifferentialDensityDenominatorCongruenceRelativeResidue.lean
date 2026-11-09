import SMSFormula.PadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceRelativeCayleyAlgebra
import SMSFormula.PadicSpecialOrthogonalDifferentialDensityCongruenceDeterminantLossResidue
import SMSFormula.PadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidue

/-!
# Relative denominator-Cayley residues

This module converts the exact relative Cayley algebra into the finite
form-coordinate relation needed for the denominator-congruence quotient.
The key intermediate condition is entrywise membership in the selected
principal ideal.  Left and right multiplication by integral matrix units
preserves this condition exactly; no cancellation on the form-adapted lattice
is assumed.

No quotient equivalence, cardinality, or gauge value is asserted.
-/

noncomputable section

open scoped Matrix Matrix.Norms.Operator

namespace Matrix

set_option maxHeartbeats 3000000

variable {n : ℕ} {R : Type*} [CommRing R]

/-- Every entry of a matrix belongs to a fixed ideal. -/
def entriesMemIdeal (I : Ideal R) (X : Matrix (Fin n) (Fin n) R) : Prop :=
  ∀ i j, X i j ∈ I

/-- Right multiplication by an arbitrary matrix preserves entrywise ideal
membership. -/
theorem entriesMemIdeal_mul_right
    (I : Ideal R) (X A : Matrix (Fin n) (Fin n) R)
    (hX : entriesMemIdeal I X) :
    entriesMemIdeal I (X * A) := by
  intro i j
  rw [Matrix.mul_apply]
  exact I.sum_mem fun l _ ↦ I.mul_mem_right (A l j) (hX i l)

/-- Left multiplication by an arbitrary matrix preserves entrywise ideal
membership. -/
theorem entriesMemIdeal_mul_left
    (I : Ideal R) (A X : Matrix (Fin n) (Fin n) R)
    (hX : entriesMemIdeal I X) :
    entriesMemIdeal I (A * X) := by
  intro i j
  rw [Matrix.mul_apply]
  exact I.sum_mem fun l _ ↦ I.mul_mem_left (A i l) (hX l j)

/-- Left multiplication by a matrix unit preserves and reflects entrywise
ideal membership. -/
theorem entriesMemIdeal_unit_mul_iff
    (I : Ideal R) (U : GL (Fin n) R) (X : Matrix (Fin n) (Fin n) R) :
    entriesMemIdeal I (U.1 * X) ↔ entriesMemIdeal I X := by
  constructor
  · intro h
    have h' := entriesMemIdeal_mul_left I (U⁻¹).1 (U.1 * X) h
    have hinv_mul : (U⁻¹).1 * U.1 = 1 := U.inv_val
    have heq : (U⁻¹).1 * (U.1 * X) = X := by
      rw [← Matrix.mul_assoc, hinv_mul, Matrix.one_mul]
    rwa [heq] at h'
  · exact entriesMemIdeal_mul_left I U.1 X

/-- Right multiplication by a matrix unit preserves and reflects entrywise
ideal membership. -/
theorem entriesMemIdeal_mul_unit_iff
    (I : Ideal R) (X : Matrix (Fin n) (Fin n) R) (U : GL (Fin n) R) :
    entriesMemIdeal I (X * U.1) ↔ entriesMemIdeal I X := by
  constructor
  · intro h
    have h' := entriesMemIdeal_mul_right I (X * U.1) (U⁻¹).1 h
    have hmul_inv : U.1 * (U⁻¹).1 = 1 := U.val_inv
    have heq : (X * U.1) * (U⁻¹).1 = X := by
      rw [Matrix.mul_assoc, hmul_inv, Matrix.mul_one]
    rwa [heq] at h'
  · exact entriesMemIdeal_mul_right I X U.1

/-- Multiplication by a scalar unit preserves and reflects entrywise ideal
membership. -/
theorem entriesMemIdeal_unit_smul_iff
    (I : Ideal R) (u : Rˣ) (X : Matrix (Fin n) (Fin n) R) :
    entriesMemIdeal I ((u : R) • X) ↔ entriesMemIdeal I X := by
  constructor
  · intro h i j
    have hij := I.mul_mem_left ((↑(u⁻¹) : R)) (h i j)
    change (↑(u⁻¹) : R) * ((u : R) * X i j) ∈ I at hij
    simpa only [← mul_assoc, Units.inv_mul, one_mul] using hij
  · intro h i j
    exact I.mul_mem_left (u : R) (h i j)

/-- The exact forward-Cayley difference identity preserves entrywise ideal
membership when two is a unit. -/
theorem entriesMemIdeal_cayleyRingForwardMatrix_sub_iff
    (I : Ideal R) (X Y : Matrix (Fin n) (Fin n) R)
    (hX : X ∈ cayleyRingSource) (hY : Y ∈ cayleyRingSource)
    (h2 : IsUnit (2 : R)) :
    entriesMemIdeal I (cayleyRingForwardMatrix X - cayleyRingForwardMatrix Y) ↔
      entriesMemIdeal I (X - Y) := by
  let UX : GL (Fin n) R := hX.unit
  let UY : GL (Fin n) R := hY.unit
  let u2 : Rˣ := h2.unit
  have hUX : UX.1 = 1 - X := hX.unit_spec
  have hUY : UY.1 = 1 - Y := hY.unit_spec
  have hu2 : (u2 : R) = 2 := h2.unit_spec
  have hcross := cayleyRingForwardMatrix_sub_cross X Y hX hY
  calc
    entriesMemIdeal I (cayleyRingForwardMatrix X - cayleyRingForwardMatrix Y) ↔
        entriesMemIdeal I
          ((1 - X) *
            (cayleyRingForwardMatrix X - cayleyRingForwardMatrix Y) *
              (1 - Y)) := by
          rw [← hUX, ← hUY,
            entriesMemIdeal_mul_unit_iff,
            entriesMemIdeal_unit_mul_iff]
    _ ↔ entriesMemIdeal I (cayleyRingTwoMatrix * (X - Y)) := by
      rw [hcross]
    _ ↔ entriesMemIdeal I ((2 : R) • (X - Y)) := by
      rw [smul_eq_diagonal_mul]
      rfl
    _ ↔ entriesMemIdeal I (X - Y) := by
      rw [← hu2]
      exact entriesMemIdeal_unit_smul_iff I u2 (X - Y)

end Matrix

namespace PositiveDefiniteIntegralLattice

open Matrix

variable {n : ℕ}

/-- Principal congruence is exactly entrywise membership of the integral
matrix difference from one in the selected prime-power ideal. -/
theorem mem_localPadicPrincipalCongruenceSubgroup_iff_entriesMemIdeal_sub_one
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (g : L.localPadicLatticeStabilizerSubgroup p) :
    g ∈ L.localPadicPrincipalCongruenceSubgroup p k ↔
      Matrix.entriesMemIdeal
        (Ideal.span {(p : ℤ_[p]) ^ k})
        ((L.localPadicLatticeStabilizerIntegralGL p g).1 - 1) := by
  rw [L.mem_localPadicPrincipalCongruenceSubgroup_iff]
  constructor
  · intro hg i j
    rw [← PadicInt.ker_toZModPow k, RingHom.mem_ker]
    change PadicInt.toZModPow k
      ((L.localPadicLatticeStabilizerIntegralGL p g).1 i j -
        (1 : Matrix (Fin n) (Fin n) ℤ_[p]) i j) = 0
    rw [map_sub]
    have hone : PadicInt.toZModPow k
        ((1 : Matrix (Fin n) (Fin n) ℤ_[p]) i j) =
          (1 : Matrix (Fin n) (Fin n) (ZMod (p ^ k))) i j := by
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    rw [hone]
    exact sub_eq_zero.mpr (hg i j)
  · intro hg i j
    have hij := hg i j
    rw [← PadicInt.ker_toZModPow k, RingHom.mem_ker] at hij
    change PadicInt.toZModPow k
      ((L.localPadicLatticeStabilizerIntegralGL p g).1 i j -
        (1 : Matrix (Fin n) (Fin n) ℤ_[p]) i j) = 0 at hij
    rw [map_sub] at hij
    have hone : PadicInt.toZModPow k
        ((1 : Matrix (Fin n) (Fin n) ℤ_[p]) i j) =
          (1 : Matrix (Fin n) (Fin n) (ZMod (p ^ k))) i j := by
      by_cases hij' : i = j <;> simp [Matrix.one_apply, hij']
    rw [hone] at hij
    exact sub_eq_zero.mp hij

/-- For two odd-prime denominator-congruence elements, relative principal
congruence is exactly entrywise selected-depth divisibility of the difference
of their literal integral inverse-Cayley coordinates. -/
theorem
    mul_inv_mem_densityPrincipalKernel_iff_inverseCayleyIntegral_sub_entriesMemIdeal
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2)
    (g h :
      L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceSubgroup p) :
    g * h⁻¹ ∈
        L.localPadicSpecialOrthogonalDifferentialDensityPrincipalKernelInDenominatorCongruence p ↔
      Matrix.entriesMemIdeal
        (Ideal.span
          {(p : ℤ_[p]) ^
            L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p})
        ((L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceInverseCayleyIntegral
            p hp2 g : Matrix (Fin n) (Fin n) ℤ_[p]) -
          (L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceInverseCayleyIntegral
            p hp2 h : Matrix (Fin n) (Fin n) ℤ_[p])) := by
  let k := L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p
  let I : Ideal ℤ_[p] := Ideal.span {(p : ℤ_[p]) ^ k}
  let G := L.localPadicLatticeStabilizerIntegralGL p g.1
  let H := L.localPadicLatticeStabilizerIntegralGL p h.1
  let R := L.localPadicLatticeStabilizerIntegralGL p (g * h⁻¹).1
  let X : Matrix (Fin n) (Fin n) ℤ_[p] :=
    L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceInverseCayleyIntegral
      p hp2 g
  let Y : Matrix (Fin n) (Fin n) ℤ_[p] :=
    L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceInverseCayleyIntegral
      p hp2 h
  have h2 : IsUnit (2 : ℤ_[p]) := two_isUnit_padicInt_of_ne_two p hp2
  have hGdomain : G.1 ∈ Matrix.cayleyRingInverseDomain :=
    L.isUnit_localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceIntegralGL_add_one
      p hp2 g
  have hHdomain : H.1 ∈ Matrix.cayleyRingInverseDomain :=
    L.isUnit_localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceIntegralGL_add_one
      p hp2 h
  have hXeq : X = Matrix.cayleyRingInverseMatrix G.1 := by
    exact
      L.coe_localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceInverseCayleyIntegral
        p hp2 g
  have hYeq : Y = Matrix.cayleyRingInverseMatrix H.1 := by
    exact
      L.coe_localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceInverseCayleyIntegral
        p hp2 h
  have hXsource : X ∈ Matrix.cayleyRingSource := by
    rw [hXeq]
    exact Matrix.cayleyRingInverseMatrix_mem_source h2 G.1 hGdomain
  have hYsource : Y ∈ Matrix.cayleyRingSource := by
    rw [hYeq]
    exact Matrix.cayleyRingInverseMatrix_mem_source h2 H.1 hHdomain
  have hGforward : Matrix.cayleyRingForwardMatrix X = G.1 := by
    rw [hXeq]
    exact Matrix.cayleyRingForwardMatrix_inverse h2 G.1 hGdomain
  have hHforward : Matrix.cayleyRingForwardMatrix Y = H.1 := by
    rw [hYeq]
    exact Matrix.cayleyRingForwardMatrix_inverse h2 H.1 hHdomain
  have hHinv :
      L.localPadicLatticeStabilizerIntegralGL p h.1⁻¹ = H⁻¹ := by
    simpa only [H] using
      (L.localPadicLatticeStabilizerIntegralGLHom p).map_inv h.1
  have hRmatrix : R.1 = G.1 * (H⁻¹).1 := by
    calc
      R.1 = (G * (L.localPadicLatticeStabilizerIntegralGL p h.1⁻¹)).1 := by
        exact congrArg Units.val
          ((L.localPadicLatticeStabilizerIntegralGLHom p).map_mul g.1 h.1⁻¹)
      _ = (G * H⁻¹).1 := by rw [hHinv]
      _ = G.1 * (H⁻¹).1 := rfl
  have hrelative : R.1 - 1 = (G.1 - H.1) * (H⁻¹).1 := by
    rw [hRmatrix]
    have hHmul : H.1 * (H⁻¹).1 = 1 := H.val_inv
    calc
      G.1 * (H⁻¹).1 - 1 =
          G.1 * (H⁻¹).1 - H.1 * (H⁻¹).1 := by rw [hHmul]
      _ = (G.1 - H.1) * (H⁻¹).1 := by noncomm_ring
  rw [L.mem_localPadicSpecialOrthogonalDifferentialDensityPrincipalKernelInDenominatorCongruence_iff]
  change (g * h⁻¹).1 ∈ L.localPadicPrincipalCongruenceSubgroup p k ↔ _
  rw [L.mem_localPadicPrincipalCongruenceSubgroup_iff_entriesMemIdeal_sub_one]
  change Matrix.entriesMemIdeal I (R.1 - 1) ↔
    Matrix.entriesMemIdeal I (X - Y)
  rw [hrelative, Matrix.entriesMemIdeal_mul_unit_iff]
  rw [← hGforward, ← hHforward]
  exact
    Matrix.entriesMemIdeal_cayleyRingForwardMatrix_sub_iff
      I X Y hXsource hYsource h2

/-- The difference of two absolute denominator-Cayley coordinates belongs to
the original density source exactly when their literal integral coordinate
difference is entrywise divisible by the selected principal power. -/
theorem
    inverseCayley_sub_mem_densitySourceAmbientSet_iff_integral_sub_entriesMemIdeal
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2)
    (g h :
      L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceSubgroup p) :
    (L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceInverseCayley
          p hp2 g -
        L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceInverseCayley
          p hp2 h) ∈
        L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet p ↔
      Matrix.entriesMemIdeal
        (Ideal.span
          {(p : ℤ_[p]) ^
            L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p})
        ((L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceInverseCayleyIntegral
            p hp2 g : Matrix (Fin n) (Fin n) ℤ_[p]) -
          (L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceInverseCayleyIntegral
            p hp2 h : Matrix (Fin n) (Fin n) ℤ_[p])) := by
  let X :=
    L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceInverseCayley
      p hp2 g
  let Y :=
    L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceInverseCayley
      p hp2 h
  let Xz :=
    L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceInverseCayleyIntegral
      p hp2 g
  let Yz :=
    L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceInverseCayleyIntegral
      p hp2 h
  let D := X - Y
  let Dz := Xz - Yz
  have hDzmap :
      (Dz : Matrix (Fin n) (Fin n) ℤ_[p]).map PadicInt.Coe.ringHom =
        (D : Matrix (Fin n) (Fin n) ℚ_[p]) := by
    change
      ((Xz : Matrix (Fin n) (Fin n) ℤ_[p]) -
          (Yz : Matrix (Fin n) (Fin n) ℤ_[p])).map PadicInt.Coe.ringHom =
        (X : Matrix (Fin n) (Fin n) ℚ_[p]) -
          (Y : Matrix (Fin n) (Fin n) ℚ_[p])
    rw [Matrix.map_sub _ (fun a b ↦ map_sub PadicInt.Coe.ringHom a b)]
    rw [← L.coe_localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceInverseCayley
        p hp2 g,
      ← L.coe_localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceInverseCayley
        p hp2 h]
  constructor
  · intro hD
    obtain ⟨U, hUmap, hUmem⟩ :=
      L.exists_integral_skewAdjoint_lift_mem_span_pow_of_mem_densityCongruenceSourceAmbientSet
        p hp2 D hD
    have hUDz :
        (U : Matrix (Fin n) (Fin n) ℤ_[p]) =
          (Dz : Matrix (Fin n) (Fin n) ℤ_[p]) := by
      apply Matrix.ext
      intro i j
      apply PadicInt.ext
      exact congr_fun (congr_fun (hUmap.trans hDzmap.symm) i) j
    intro i j
    change (Dz : Matrix (Fin n) (Fin n) ℤ_[p]) i j ∈ _
    rw [← hUDz]
    exact hUmem i j
  · intro hDz
    exact
      L.mem_localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet_of_integral_skewAdjoint_lift_mem_span_pow
        p D Dz hDzmap hDz

/-- Regard the inverse-Cayley coordinate of an `H_k` element as a point of
the form-adapted integral coordinate lattice. -/
def
    localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceInverseCayleyFormCoordinatePoint
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2)
    (g :
      L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceSubgroup p) :
    Matrix.skewAdjointFormElementaryPadicCoordinateLatticeAddSubgroup
      p L.rationalFormMatrix (L.form_symm.map _)
        L.rationalFormMatrix_det_ne_zero :=
  ⟨L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceInverseCayley
      p hp2 g,
    Matrix.skewAdjointFormElementaryPadicUniformCoordinateBall_subset_lattice
      p
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)
      L.rationalFormMatrix (L.form_symm.map _)
      L.rationalFormMatrix_det_ne_zero
      (L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceInverseCayley_mem_formElementaryUniformCoordinateBall
        p hp2 g)⟩

/-- The literal difference of the two absolute inverse-Cayley coordinates as
an integral form-coordinate point. -/
def
    localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceRelativeFormCoordinatePoint
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2)
    (g h :
      L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceSubgroup p) :
    Matrix.skewAdjointFormElementaryPadicCoordinateLatticeAddSubgroup
      p L.rationalFormMatrix (L.form_symm.map _)
        L.rationalFormMatrix_det_ne_zero :=
  L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceInverseCayleyFormCoordinatePoint
      p hp2 g -
    L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceInverseCayleyFormCoordinatePoint
      p hp2 h

/-- The relative element is in the principal kernel exactly when the literal
difference of its two absolute form coordinates belongs to the density
source. -/
theorem
    mul_inv_mem_densityPrincipalKernel_iff_relativeFormCoordinatePoint_mem_source
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2)
    (g h :
      L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceSubgroup p) :
    g * h⁻¹ ∈
        L.localPadicSpecialOrthogonalDifferentialDensityPrincipalKernelInDenominatorCongruence p ↔
      (L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceRelativeFormCoordinatePoint
        p hp2 g h).1 ∈
        L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet p := by
  rw [L.mul_inv_mem_densityPrincipalKernel_iff_inverseCayleyIntegral_sub_entriesMemIdeal
    p hp2 g h]
  rw [← L.inverseCayley_sub_mem_densitySourceAmbientSet_iff_integral_sub_entriesMemIdeal
    p hp2 g h]
  rfl

/-- The prescribed level-`k+v` residue of the difference of two absolute
denominator-Cayley coordinates. -/
def
    localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceRelativeFormCoordinateResidue
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2)
    (g h :
      L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceSubgroup p) :
    Matrix.skewAdjointFormElementaryPadicCoordinateResidue
      p
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel p)
      L.rationalFormMatrix :=
  Matrix.skewAdjointFormElementaryPadicCoordinateReduction
    p
    (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel p)
    L.rationalFormMatrix (L.form_symm.map _)
      L.rationalFormMatrix_det_ne_zero
    (L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceRelativeFormCoordinatePoint
      p hp2 g h)

/-- The relative principal-kernel relation is literally membership of the
absolute-coordinate difference residue in the attained density-residue
image. -/
theorem
    mul_inv_mem_densityPrincipalKernel_iff_relativeFormCoordinateResidue_mem_image
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2)
    (g h :
      L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceSubgroup p) :
    g * h⁻¹ ∈
        L.localPadicSpecialOrthogonalDifferentialDensityPrincipalKernelInDenominatorCongruence p ↔
      L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceRelativeFormCoordinateResidue
          p hp2 g h ∈
        L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueImage p := by
  rw [L.mul_inv_mem_densityPrincipalKernel_iff_relativeFormCoordinatePoint_mem_source
    p hp2 g h]
  have hpre := Set.ext_iff.mp
    (L.preimage_localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueImage_eq_source
      p hp2)
    (L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceRelativeFormCoordinatePoint
      p hp2 g h)
  simpa only [Set.mem_preimage,
    localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateSource,
    localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceRelativeFormCoordinateResidue]
    using hpre.symm

/-- The absolute-coordinate difference residue lies in the determinant-loss
zero fiber. -/
theorem
    relativeFormCoordinateResidue_restrictsToZero
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2)
    (g h :
      L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceSubgroup p) :
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDeterminantLossRestriction p
        (L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceRelativeFormCoordinateResidue
          p hp2 g h) = 0 := by
  let x :=
    L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceInverseCayleyFormCoordinatePoint
      p hp2 g
  let y :=
    L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceInverseCayleyFormCoordinatePoint
      p hp2 h
  have hxball : x.1 ∈
      Matrix.skewAdjointFormElementaryPadicUniformCoordinateBall
        p
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)
        L.rationalFormMatrix (L.form_symm.map _)
          L.rationalFormMatrix_det_ne_zero :=
    L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceInverseCayley_mem_formElementaryUniformCoordinateBall
      p hp2 g
  have hyball : y.1 ∈
      Matrix.skewAdjointFormElementaryPadicUniformCoordinateBall
        p
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)
        L.rationalFormMatrix (L.form_symm.map _)
          L.rationalFormMatrix_det_ne_zero :=
    L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceInverseCayley_mem_formElementaryUniformCoordinateBall
      p hp2 h
  have hxzero :=
    (Matrix.mem_skewAdjointFormElementaryPadicUniformCoordinateBall_iff_coordinateReduction_eq_zero
      p
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)
      L.rationalFormMatrix (L.form_symm.map _)
      L.rationalFormMatrix_det_ne_zero x).1 hxball
  have hyzero :=
    (Matrix.mem_skewAdjointFormElementaryPadicUniformCoordinateBall_iff_coordinateReduction_eq_zero
      p
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)
      L.rationalFormMatrix (L.form_symm.map _)
      L.rationalFormMatrix_det_ne_zero y).1 hyball
  change
    Matrix.skewAdjointFormElementaryPadicCoordinateResidueRestriction
        p
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)
        (padicValInt p L.pairingDeterminant)
        L.rationalFormMatrix
        (Matrix.skewAdjointFormElementaryPadicCoordinateReduction
          p
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p +
            padicValInt p L.pairingDeterminant)
          L.rationalFormMatrix (L.form_symm.map _)
          L.rationalFormMatrix_det_ne_zero (x - y)) = 0
  rw [Matrix.skewAdjointFormElementaryPadicCoordinateResidueRestriction_reduction,
    map_sub, hxzero, hyzero, sub_zero]

/-- The difference residue packaged in the selected determinant-loss
carrier. -/
def
    localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceRelativeDeterminantLossResidue
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2)
    (g h :
      L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceSubgroup p) :
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDeterminantLossResidue p :=
  ⟨L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceRelativeFormCoordinateResidue
      p hp2 g h,
    L.relativeFormCoordinateResidue_restrictsToZero p hp2 g h⟩

end PositiveDefiniteIntegralLattice
