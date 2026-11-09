import SMSFormula.RationalFiniteAdeleIntegralCoordinateResidueQuotient
import SMSFormula.RationalFiniteAdeleQuadraticGaussDualQuotient

/-!
# Residue presentations of the finite quadratic Gauss quotients

The standard integral quotient has the canonical residue-cube presentation
`(ZMod m)^n`.  The adjugate inclusion
`m * |polarDeterminant L| * Zhat^n <= m * C * Zhat^n` gives a canonical quotient map
from a rectangular residue cube onto the intrinsic polar-matrix quotient.
The latter is an overcounted finite presentation, not a choice of residue
representatives or a change of Haar normalization.  Thus both sides of the
remaining matrix reciprocity theorem are sums over explicit canonical finite
residue cubes.
-/

noncomputable section

open PositiveDefiniteIntegralLattice

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

private noncomputable instance rectangularModulusNeZero
    (L : PositiveDefiniteIntegralLattice n) (m : ℕ) [NeZero m] :
    NeZero (m * L.polarDeterminant.natAbs) :=
  ⟨mul_ne_zero (NeZero.ne m)
    (Int.natAbs_ne_zero.mpr (ne_of_gt L.polarDeterminant_pos))⟩

/-- The quotient projection induced by
`m * |polarDeterminant L| * Zhat^n <= m * C * Zhat^n`. -/
noncomputable def integralFiniteAdeleRectangularToPolarMatrixQuotient
    (L : PositiveDefiniteIntegralLattice n) (m : ℕ) :
    ((Fin n → IntegralFiniteAdele) ⧸
        (integralFiniteAdeleCoordinateNatDilation n
          (m * L.polarDeterminant.natAbs)).range) →+
      ((Fin n → IntegralFiniteAdele) ⧸
        integralFiniteAdelePolarDenDilationAddSubgroup L m) :=
  QuotientAddGroup.map
    (integralFiniteAdeleCoordinateNatDilation n
      (m * L.polarDeterminant.natAbs)).range
    (integralFiniteAdelePolarDenDilationAddSubgroup L m)
    (AddMonoidHom.id (Fin n → IntegralFiniteAdele))
    (integralFiniteAdeleCoordinateNatDiscDilation_range_le_polarDenDilation
      L m)

@[simp]
theorem integralFiniteAdeleRectangularToPolarMatrixQuotient_mk
    (L : PositiveDefiniteIntegralLattice n) (m : ℕ)
    (x : Fin n → IntegralFiniteAdele) :
    integralFiniteAdeleRectangularToPolarMatrixQuotient L m
        (x : (Fin n → IntegralFiniteAdele) ⧸
          (integralFiniteAdeleCoordinateNatDilation n
            (m * L.polarDeterminant.natAbs)).range) =
      (x : (Fin n → IntegralFiniteAdele) ⧸
        integralFiniteAdelePolarDenDilationAddSubgroup L m) :=
  rfl

theorem integralFiniteAdeleRectangularToPolarMatrixQuotient_surjective
    (L : PositiveDefiniteIntegralLattice n) (m : ℕ) :
    Function.Surjective
      (integralFiniteAdeleRectangularToPolarMatrixQuotient L m) := by
  intro q
  induction q using Quotient.inductionOn' with
  | _ x => exact ⟨(x : (Fin n → IntegralFiniteAdele) ⧸
      (integralFiniteAdeleCoordinateNatDilation n
        (m * L.polarDeterminant.natAbs)).range), rfl⟩

/-- The canonical rectangular residue map
`(ZMod (m * |polarDeterminant L|))^n -> Zhat^n / (m * C * Zhat^n)`. -/
noncomputable def rectangularResidueToPolarMatrixQuotient
    (L : PositiveDefiniteIntegralLattice n) (m : ℕ) [NeZero m] :
    (Fin n → ZMod (m * L.polarDeterminant.natAbs)) →+
      ((Fin n → IntegralFiniteAdele) ⧸
        integralFiniteAdelePolarDenDilationAddSubgroup L m) :=
  (integralFiniteAdeleRectangularToPolarMatrixQuotient L m).comp
    (coordinateResidueEquivIntegralFiniteAdeleModDilation n
      (m * L.polarDeterminant.natAbs) (NeZero.ne _)).toAddMonoidHom

theorem rectangularResidueToPolarMatrixQuotient_surjective
    (L : PositiveDefiniteIntegralLattice n) (m : ℕ) [NeZero m] :
    Function.Surjective (rectangularResidueToPolarMatrixQuotient L m) :=
  (integralFiniteAdeleRectangularToPolarMatrixQuotient_surjective L m).comp
    (coordinateResidueEquivIntegralFiniteAdeleModDilation n
      (m * L.polarDeterminant.natAbs) (NeZero.ne _)).surjective

@[simp]
theorem rectangularResidueToPolarMatrixQuotient_apply_intCast
    (L : PositiveDefiniteIntegralLattice n) (m : ℕ) [NeZero m]
    (z : Fin n → ℤ) :
    rectangularResidueToPolarMatrixQuotient L m
        (fun i ↦ (z i : ZMod (m * L.polarDeterminant.natAbs))) =
      (fun i ↦ integerToIntegralFiniteAdele (z i) :
        (Fin n → IntegralFiniteAdele) ⧸
          integralFiniteAdelePolarDenDilationAddSubgroup L m) := by
  rw [rectangularResidueToPolarMatrixQuotient]
  change integralFiniteAdeleRectangularToPolarMatrixQuotient L m
      (coordinateResidueEquivIntegralFiniteAdeleModDilation n
        (m * L.polarDeterminant.natAbs) (NeZero.ne _)
          (fun i ↦ (z i : ZMod (m * L.polarDeterminant.natAbs)))) = _
  rw [coordinateResidueEquivIntegralFiniteAdeleModDilation_apply_intCast]
  rfl

/-- Cardinality of the rectangular source residue cube. -/
theorem rectangularResidue_card
    (L : PositiveDefiniteIntegralLattice n) (m : ℕ) [NeZero m] :
    Fintype.card (Fin n → ZMod (m * L.polarDeterminant.natAbs)) =
      (m * L.polarDeterminant.natAbs) ^ n := by
  simp

/-- Every fiber of the rectangular presentation has the expected fixed
overcount `|polarDeterminant L|^(n-1)`.  This is a cardinal statement about the canonical
quotient map; no representatives of either quotient are selected. -/
theorem rectangularResidueToPolarMatrixQuotient_ker_card
    (L : PositiveDefiniteIntegralLattice n) (m : ℕ) [NeZero m]
    (hn : n ≠ 0) :
    Nat.card (rectangularResidueToPolarMatrixQuotient L m).ker =
      L.polarDeterminant.natAbs ^ (n - 1) := by
  let f := rectangularResidueToPolarMatrixQuotient L m
  have hsurj : Function.Surjective f :=
    rectangularResidueToPolarMatrixQuotient_surjective L m
  have hcard := f.ker.card_mul_index
  have hrange : f.range = ⊤ := by
    apply top_unique
    intro y _hy
    rcases hsurj y with ⟨x, rfl⟩
    exact ⟨x, rfl⟩
  rw [AddSubgroup.index_ker, hrange] at hcard
  simp [integralFiniteAdelePolarDenQuotient_card] at hcard
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  apply Nat.mul_right_cancel (mul_pos
    (Int.natAbs_pos.mpr (ne_of_gt L.polarDeterminant_pos))
    (pow_pos (Nat.pos_of_ne_zero (NeZero.ne m)) _))
  calc
    Nat.card f.ker * (L.polarDeterminant.natAbs * m ^ (k + 1)) =
        (m * L.polarDeterminant.natAbs) ^ (k + 1) := hcard
    _ = L.polarDeterminant.natAbs ^ k *
        (L.polarDeterminant.natAbs * m ^ (k + 1)) := by
      rw [mul_pow, pow_succ]
      ring

private noncomputable def addMonoidHomKerEquivFiber
    {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (f : G →+ H) (hf : Function.Surjective f) (y : H) :
    f.ker ≃ {x : G // f x = y} := by
  let x₀ : G := Classical.choose (hf y)
  have hx₀ : f x₀ = y := Classical.choose_spec (hf y)
  exact
    { toFun := fun k ↦ ⟨k.1 + x₀, by
        have hk : f k.1 = 0 := k.2
        rw [map_add, hk, zero_add, hx₀]⟩
      invFun := fun x ↦ ⟨x.1 - x₀, by simp [x.2, hx₀]⟩
      left_inv := by intro k; apply Subtype.ext; simp
      right_inv := by intro x; apply Subtype.ext; simp }

private noncomputable instance rectangularResidueFiberFintype
    (L : PositiveDefiniteIntegralLattice n) (m : ℕ) [NeZero m]
    (q : (Fin n → IntegralFiniteAdele) ⧸
      integralFiniteAdelePolarDenDilationAddSubgroup L m) :
    Fintype {x // rectangularResidueToPolarMatrixQuotient L m x = q} :=
  Fintype.ofFinite _

/-- Every target class has exactly the fixed rectangular overcount. -/
theorem rectangularResidueToPolarMatrixQuotient_fiber_card
    (L : PositiveDefiniteIntegralLattice n) (m : ℕ) [NeZero m]
    (hn : n ≠ 0)
    (q : (Fin n → IntegralFiniteAdele) ⧸
      integralFiniteAdelePolarDenDilationAddSubgroup L m) :
    Fintype.card {x // rectangularResidueToPolarMatrixQuotient L m x = q} =
      L.polarDeterminant.natAbs ^ (n - 1) := by
  rw [← Nat.card_eq_fintype_card]
  rw [← Nat.card_congr
    (addMonoidHomKerEquivFiber
      (rectangularResidueToPolarMatrixQuotient L m)
      (rectangularResidueToPolarMatrixQuotient_surjective L m) q)]
  exact rectangularResidueToPolarMatrixQuotient_ker_card L m hn

/-- Pulling a function on the polar-matrix quotient back to the rectangular
residue cube multiplies its finite sum by the exact constant fiber size. -/
theorem sum_comp_rectangularResidueToPolarMatrixQuotient
    (L : PositiveDefiniteIntegralLattice n) (m : ℕ) [NeZero m]
    (hn : n ≠ 0)
    (f : ((Fin n → IntegralFiniteAdele) ⧸
      integralFiniteAdelePolarDenDilationAddSubgroup L m) → ℂ) :
    ∑ x, f (rectangularResidueToPolarMatrixQuotient L m x) =
      ((L.polarDeterminant.natAbs ^ (n - 1) : ℕ) : ℂ) * ∑ q, f q := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ
    (rectangularResidueToPolarMatrixQuotient L m)
    (fun x ↦ f (rectangularResidueToPolarMatrixQuotient L m x))]
  have hfiber : ∀ q,
      ((Finset.univ.filter fun x ↦
        rectangularResidueToPolarMatrixQuotient L m x = q).card : ℂ) =
          ((L.polarDeterminant.natAbs ^ (n - 1) : ℕ) : ℂ) := by
    intro q
    rw [show (Finset.univ.filter fun x ↦
        rectangularResidueToPolarMatrixQuotient L m x = q).card =
        Fintype.card {x //
          rectangularResidueToPolarMatrixQuotient L m x = q} by
      exact (Fintype.card_subtype fun x ↦
        rectangularResidueToPolarMatrixQuotient L m x = q).symm]
    rw [rectangularResidueToPolarMatrixQuotient_fiber_card L m hn q]
  calc
    ∑ q, ∑ x ∈ Finset.univ with
        rectangularResidueToPolarMatrixQuotient L m x = q,
          f (rectangularResidueToPolarMatrixQuotient L m x) =
        ∑ q, ((L.polarDeterminant.natAbs ^ (n - 1) : ℕ) : ℂ) * f q := by
          apply Finset.sum_congr rfl
          intro q _hq
          calc
            ∑ x ∈ Finset.univ with
                rectangularResidueToPolarMatrixQuotient L m x = q,
                  f (rectangularResidueToPolarMatrixQuotient L m x) =
                ((Finset.univ.filter fun x ↦
                  rectangularResidueToPolarMatrixQuotient L m x = q).card : ℂ) *
                    f q := by
                      have hsum := Finset.sum_eq_card_nsmul
                        (s := Finset.univ.filter fun x ↦
                          rectangularResidueToPolarMatrixQuotient L m x = q)
                        (f := fun x ↦
                          f (rectangularResidueToPolarMatrixQuotient L m x))
                        (b := f q) (by
                          intro x hx
                          change f (rectangularResidueToPolarMatrixQuotient L m x) = f q
                          rw [(Finset.mem_filter.mp hx).2])
                      simpa [nsmul_eq_mul] using hsum
            _ = ((L.polarDeterminant.natAbs ^ (n - 1) : ℕ) : ℂ) * f q := by rw [hfiber q]
    _ = ((L.polarDeterminant.natAbs ^ (n - 1) : ℕ) : ℂ) * ∑ q, f q := by
      rw [Finset.mul_sum]

private noncomputable instance rationalDenNeZero (t : ℚ) : NeZero t.den :=
  ⟨t.den_nz⟩

/-- The standard integral-lattice phase pulled back to the canonical residue
cube `(ZMod t.den)^n`. -/
noncomputable def rationalFiniteAdeleIntegralQuadraticPhaseOnResidues
    (L : PositiveDefiniteIntegralLattice n) (t : ℚ) :
    (Fin n → ZMod t.den) → ℂ :=
  fun z ↦ addQuotientPeriodicLift
    (integralFiniteAdeleCoordinateNatDilation n t.den).range
    (rationalFiniteAdeleIntegralQuadraticPhase L t)
    (rationalFiniteAdeleIntegralQuadraticPhase_add_denDilation L t)
    (coordinateResidueEquivIntegralFiniteAdeleModDilation
      n t.den t.den_nz z)

@[simp]
theorem rationalFiniteAdeleIntegralQuadraticPhaseOnResidues_intCast
    (L : PositiveDefiniteIntegralLattice n) (t : ℚ) (z : Fin n → ℤ) :
    rationalFiniteAdeleIntegralQuadraticPhaseOnResidues L t
        (fun i ↦ (z i : ZMod t.den)) =
      rationalFiniteAdeleIntegralQuadraticPhase L t
        (fun i ↦ integerToIntegralFiniteAdele (z i)) := by
  rw [rationalFiniteAdeleIntegralQuadraticPhaseOnResidues]
  rw [coordinateResidueEquivIntegralFiniteAdeleModDilation_apply_intCast]
  rfl

/-- Exact residue-cube formula for the old standard finite Gauss integral. -/
theorem rationalFiniteAdeleQuadraticGaussIntegral_eq_residueSum
    (L : PositiveDefiniteIntegralLattice n) (t : ℚ) :
    L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegral t =
      (((t.den : ℝ) ^ n : ℂ)⁻¹) *
        ∑ z, rationalFiniteAdeleIntegralQuadraticPhaseOnResidues L t z := by
  rw [rationalFiniteAdeleQuadraticGaussIntegral_eq_denQuotientSum]
  congr 1
  exact (Equiv.sum_comp
    (coordinateResidueEquivIntegralFiniteAdeleModDilation
      n t.den t.den_nz).toEquiv
    (addQuotientPeriodicLift
      (integralFiniteAdeleCoordinateNatDilation n t.den).range
      (rationalFiniteAdeleIntegralQuadraticPhase L t)
      (rationalFiniteAdeleIntegralQuadraticPhase_add_denDilation L t))).symm

/-- The polar-dual phase pulled back to the canonical rectangular residue
cube. -/
noncomputable def rationalFiniteAdelePolarDualQuadraticPhaseOnRectangularResidues
    (L : PositiveDefiniteIntegralLattice n) (t : ℚ) :
    (Fin n → ZMod (t.den * L.polarDeterminant.natAbs)) → ℂ :=
  fun z ↦ rationalFiniteAdelePolarDualQuadraticPhaseOnPolarMatrixQuotient L t
    (rectangularResidueToPolarMatrixQuotient L t.den z)

@[simp]
theorem rationalFiniteAdelePolarDualQuadraticPhaseOnRectangularResidues_intCast
    (L : PositiveDefiniteIntegralLattice n) (t : ℚ) (z : Fin n → ℤ) :
    rationalFiniteAdelePolarDualQuadraticPhaseOnRectangularResidues L t
        (fun i ↦ (z i : ZMod (t.den * L.polarDeterminant.natAbs))) =
      rationalFiniteAdelePolarDualQuadraticPhase L t
        ((finitePolarDualEquivIntegralCoordinates L).symm
          (fun i ↦ integerToIntegralFiniteAdele (z i))) := by
  rw [rationalFiniteAdelePolarDualQuadraticPhaseOnRectangularResidues]
  rw [rectangularResidueToPolarMatrixQuotient_apply_intCast]
  let x : FinitePolarDualAdeleVector L :=
    (finitePolarDualEquivIntegralCoordinates L).symm
      (fun i ↦ integerToIntegralFiniteAdele (z i))
  have hx : finitePolarDualEquivIntegralCoordinates L x =
      fun i ↦ integerToIntegralFiniteAdele (z i) := by
    exact (finitePolarDualEquivIntegralCoordinates L).apply_symm_apply _
  rw [← hx]
  simpa [x] using
    (rationalFiniteAdelePolarDualQuadraticPhaseOnPolarMatrixQuotient_mk
      L t x)

/-- Exact rectangular residue formula for the old polar-dual finite Gauss
integral.  The factor `|polarDeterminant L|^(1-n)` is the literal constant-fiber
overcount; it is not a probability renormalization. -/
theorem rationalFiniteAdeleDualQuadraticGaussIntegral_eq_rectangularResidueSum
    (L : PositiveDefiniteIntegralLattice n) (t : ℚ) (hn : n ≠ 0) :
    L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleDualQuadraticGaussIntegral t =
      (((t.den : ℝ) ^ n : ℂ)⁻¹) *
        (((L.polarDeterminant.natAbs ^ (n - 1) : ℕ) : ℂ)⁻¹) *
          ∑ z, rationalFiniteAdelePolarDualQuadraticPhaseOnRectangularResidues
            L t z := by
  rw [rationalFiniteAdeleDualQuadraticGaussIntegral_eq_polarMatrixQuotientSum]
  have hsum := sum_comp_rectangularResidueToPolarMatrixQuotient
    L t.den hn
      (rationalFiniteAdelePolarDualQuadraticPhaseOnPolarMatrixQuotient L t)
  change (((t.den : ℝ) ^ n : ℂ)⁻¹) *
      ∑ q, rationalFiniteAdelePolarDualQuadraticPhaseOnPolarMatrixQuotient L t q = _
  change _ = (((t.den : ℝ) ^ n : ℂ)⁻¹) *
    (((L.polarDeterminant.natAbs ^ (n - 1) : ℕ) : ℂ)⁻¹) *
      ∑ z, rationalFiniteAdelePolarDualQuadraticPhaseOnPolarMatrixQuotient L t
        (rectangularResidueToPolarMatrixQuotient L t.den z)
  rw [hsum]
  have hdisc : ((L.polarDeterminant.natAbs ^ (n - 1) : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast pow_ne_zero (n - 1)
      (Int.natAbs_ne_zero.mpr (ne_of_gt L.polarDeterminant_pos))
  field_simp

end RationalQuadraticSpaceMatrix
