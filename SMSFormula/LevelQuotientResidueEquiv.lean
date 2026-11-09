import SMSFormula.IntegralFiniteAdeleConductor

/-!
# The level quotient is the residue vectors

The conductor layer leaves the local integral equal to `m ^ (-n)` times a sum over the level
quotient of the integral finite-adelic vectors.  `FiniteQuadraticSumModulusBound` bounds a sum over
`(ZMod q) ^ n`.  This file identifies the two index sets, which is the group-theoretic half of the
last structural gap.

The one-coordinate case is already repository state: `residueEquivIntegralFiniteAdeleModDilation`
identifies `ZMod m` with the quotient of the integral finite adeles by the `m`-dilation range.  What
is missing is only the product step, and it is a kernel computation: the coordinatewise projection
to the one-coordinate quotients has kernel exactly the level subgroup and is surjective, so the
level quotient is the product of the coordinate quotients.

Negative scope.  This is an isomorphism of groups and says nothing about the phase.  Reindexing a
sum along it transports the summand unchanged, so the descended phase at a residue vector is not directly
the affine quadratic in that vector -- that identification needs the form's matrix reduced mod `m`
and the character identified, and is not supplied here.
-/

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

open MeasureTheory SMSFormula.QuadraticPhaseDescent

variable {n : ℕ}

/-! ## The coordinatewise projection -/

/-- The coordinatewise projection to the one-coordinate quotients. -/
noncomputable def coordProj (n m : ℕ) : (Fin n → IntegralFiniteAdele) →+
    (Fin n → IntegralFiniteAdele ⧸ (integralFiniteAdeleNatDilation m).range) where
  toFun x i := QuotientAddGroup.mk (x i)
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Membership in the level subgroup is coordinatewise, which is the whole content of the product
step. -/
theorem mem_levelSubgroup_iff (n m : ℕ) (x : Fin n → IntegralFiniteAdele) :
    x ∈ levelSubgroup n m ↔ ∀ i, x i ∈ (integralFiniteAdeleNatDilation m).range := by
  constructor
  · rintro ⟨u, rfl⟩ i
    exact ⟨u i, rfl⟩
  · intro hx
    choose u hu using hx
    exact ⟨u, funext hu⟩

/-- Its kernel is exactly the level subgroup. -/
theorem ker_coordProj (n m : ℕ) :
    (coordProj n m).ker = levelSubgroup n m := by
  ext x
  rw [AddMonoidHom.mem_ker, mem_levelSubgroup_iff]
  constructor
  · intro hx i
    exact (QuotientAddGroup.eq_zero_iff _).1 (congrFun hx i)
  · intro hx
    funext i
    exact (QuotientAddGroup.eq_zero_iff _).2 (hx i)

/-- And it is surjective, each coordinate class having a representative. -/
theorem coordProj_surjective (n m : ℕ) : Function.Surjective (coordProj n m) := by
  intro y
  choose u hu using fun i ↦ QuotientAddGroup.mk_surjective (y i)
  exact ⟨u, funext hu⟩

/-! ## The identification -/

/-- The level quotient is the product of the coordinate quotients. -/
noncomputable def levelQuotientEquivPi (n m : ℕ) :
    ((Fin n → IntegralFiniteAdele) ⧸ levelSubgroup n m) ≃+
      (Fin n → IntegralFiniteAdele ⧸ (integralFiniteAdeleNatDilation m).range) :=
  (QuotientAddGroup.quotientAddEquivOfEq (ker_coordProj n m).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective (coordProj n m) (coordProj_surjective n m))

/-- Hence the level quotient is the residue vectors, the one-coordinate identification being the
repository's own. -/
noncomputable def residueVectorEquivLevelQuotient (n m : ℕ) (hm : m ≠ 0) :
    (Fin n → ZMod m) ≃+ ((Fin n → IntegralFiniteAdele) ⧸ levelSubgroup n m) :=
  (AddEquiv.piCongrRight fun _ : Fin n ↦
    residueEquivIntegralFiniteAdeleModDilation m hm).trans (levelQuotientEquivPi n m).symm

/-! ## Reindexing the sum -/

/-- The finite sum is a sum over residue vectors -- the index set the conductor bounds use. -/
theorem sum_levelQuotient_eq_sum_residueVector (m : ℕ) [NeZero m]
    (F : ((Fin n → IntegralFiniteAdele) ⧸ levelSubgroup n m) → ℂ) :
    ∑ q : (Fin n → IntegralFiniteAdele) ⧸ levelSubgroup n m, F q =
      ∑ w : Fin n → ZMod m, F (residueVectorEquivLevelQuotient n m (NeZero.ne m) w) :=
  (Fintype.sum_equiv (residueVectorEquivLevelQuotient n m (NeZero.ne m)).toEquiv _ _
    fun _ ↦ rfl).symm

/-- The payoff: the local integral of the frequency phase is `m ^ (-n)` times a sum over residue
vectors, with the conductor condition as the only input. -/
theorem integral_scaledPhase_eq_residueVector_sum (m : ℕ) [NeZero m]
    {C : Matrix (Fin n) (Fin n) RationalFiniteAdele}
    (hC : ∀ i j, C i j ∈ integralFiniteAdeleSubring) {t : RationalFiniteAdele}
    (htm : t * (m : RationalFiniteAdele) ∈ integralFiniteAdeleSubring) :
    ∫ x, complexFiniteChar (scaledQuadratic t C x)
        ∂(integralFiniteAdeleCoordinateAddHaarMeasure n) =
      ((m ^ n : ℝ))⁻¹ • ∑ w : Fin n → ZMod m,
        phaseQuotient (scaledQuadratic_polarization t C) complexFiniteChar
          (level_of_conductor m hC htm)
          (residueVectorEquivLevelQuotient n m (NeZero.ne m) w) := by
  rw [integral_scaledPhase_eq_normalized_sum m hC htm,
    sum_levelQuotient_eq_sum_residueVector m]

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
