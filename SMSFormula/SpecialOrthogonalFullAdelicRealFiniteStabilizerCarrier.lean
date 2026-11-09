import SMSFormula.SpecialOrthogonalRealFiniteDifferentialStabilizerProductMeasure
import SMSFormula.AdelicProperFullPresentation

/-!
# Real/finite stabilizer carrier inside the full adelic special orthogonal group

The full adelic special orthogonal group splits continuously into its real
and finite-adelic factors.  This module pulls back the literal integral
finite-adelic stabilizer along that splitting and identifies the resulting
subgroup with the direct product of the real group and the finite stabilizer.

This is a carrier theorem.  No measure is transported, and no
subgroup-supported measure is asserted to be Haar on the full adelic group.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The subgroup of the full adelic special orthogonal group whose finite
component stabilizes the integral lattice.  The real component is
unrestricted. -/
def fullAdelicRealFiniteLatticeStabilizerSubgroup
    (L : PositiveDefiniteIntegralLattice n) :
    Subgroup L.ConcreteFullAdelicSpecialOrthogonalGroup :=
  ((⊤ : Subgroup L.ConcreteRealSpecialOrthogonalGroup).prod
      L.finiteSpecialOrthogonalLatticeStabilizerSubgroup).comap
    L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv.toMonoidHom

/-- Membership in the full-adelic real/finite stabilizer is exactly the
integrality of its finite component. -/
@[simp]
theorem mem_fullAdelicRealFiniteLatticeStabilizerSubgroup_iff
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFullAdelicSpecialOrthogonalGroup) :
    g ∈ L.fullAdelicRealFiniteLatticeStabilizerSubgroup ↔
      (L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv g).2 ∈
        L.finiteSpecialOrthogonalLatticeStabilizerSubgroup := by
  change
    ((L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv g).1 ∈
        (⊤ : Subgroup L.ConcreteRealSpecialOrthogonalGroup) ∧
      (L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv g).2 ∈
        L.finiteSpecialOrthogonalLatticeStabilizerSubgroup) ↔ _
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨Subgroup.mem_top _, h⟩

/-- The algebraic identification of the real group times the integral finite
stabilizer with its natural subgroup in the full adelic group. -/
noncomputable def fullAdelicRealFiniteLatticeStabilizerMulEquiv
    (L : PositiveDefiniteIntegralLattice n) :
    L.ConcreteRealSpecialOrthogonalGroup ×
        L.finiteSpecialOrthogonalLatticeStabilizerSubgroup ≃*
      L.fullAdelicRealFiniteLatticeStabilizerSubgroup where
  toFun x := by
    let g :=
      L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv.symm
        (x.1, x.2.1)
    exact ⟨g, by
      rw [L.mem_fullAdelicRealFiniteLatticeStabilizerSubgroup_iff]
      rw [show
        (L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv g).2 =
            x.2.1 from
          congrArg Prod.snd
            (L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv.apply_symm_apply
              (x.1, x.2.1))]
      exact x.2.2⟩
  invFun g := by
    let x :=
      L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv g.1
    exact (x.1, ⟨x.2,
      (L.mem_fullAdelicRealFiniteLatticeStabilizerSubgroup_iff g.1).mp g.2⟩)
  left_inv x := by
    dsimp only
    have h :=
      L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv.apply_symm_apply
        (x.1, x.2.1)
    have hinjective : Function.Injective
        (fun z :
          L.ConcreteRealSpecialOrthogonalGroup ×
            L.finiteSpecialOrthogonalLatticeStabilizerSubgroup =>
          (z.1, z.2.1)) := by
      rintro ⟨a, b⟩ ⟨c, d⟩ hcd
      have h₁ : a = c := congrArg Prod.fst hcd
      have h₂ : b.1 = d.1 := congrArg Prod.snd hcd
      subst c
      exact congrArg (fun z => (a, z)) (Subtype.ext h₂)
    apply hinjective
    exact h
  right_inv g := by
    apply Subtype.ext
    exact
      L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv.symm_apply_apply
        g.1
  map_mul' x y := by
    apply Subtype.ext
    exact
      L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv.symm.map_mul
        (x.1, x.2.1) (y.1, y.2.1)

/-- The algebraic carrier identification is a homeomorphism. -/
noncomputable def fullAdelicRealFiniteLatticeStabilizerHomeomorph
    (L : PositiveDefiniteIntegralLattice n) :
    L.ConcreteRealSpecialOrthogonalGroup ×
        L.finiteSpecialOrthogonalLatticeStabilizerSubgroup ≃ₜ
      L.fullAdelicRealFiniteLatticeStabilizerSubgroup where
  toEquiv := L.fullAdelicRealFiniteLatticeStabilizerMulEquiv.toEquiv
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact
      L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv.symm.continuous.comp
        (continuous_fst.prodMk
          (continuous_subtype_val.comp continuous_snd))
  continuous_invFun := by
    apply Continuous.prodMk
    · exact
        (L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv.continuous.comp
          continuous_subtype_val).fst
    · apply Continuous.subtype_mk
      exact
        (L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv.continuous.comp
          continuous_subtype_val).snd

/-- The natural full-adelic stabilizer carrier identification is continuously
multiplicative. -/
noncomputable def fullAdelicRealFiniteLatticeStabilizerContinuousMulEquiv
    (L : PositiveDefiniteIntegralLattice n) :
    L.ConcreteRealSpecialOrthogonalGroup ×
        L.finiteSpecialOrthogonalLatticeStabilizerSubgroup ≃ₜ*
      L.fullAdelicRealFiniteLatticeStabilizerSubgroup :=
  ContinuousMulEquiv.mk'
    L.fullAdelicRealFiniteLatticeStabilizerHomeomorph
    L.fullAdelicRealFiniteLatticeStabilizerMulEquiv.map_mul

/-- Splitting the assembled full-adelic stabilizer recovers its real
component. -/
@[simp]
theorem fullAdelicRealFiniteLatticeStabilizerContinuousMulEquiv_real
    (L : PositiveDefiniteIntegralLattice n)
    (x : L.ConcreteRealSpecialOrthogonalGroup ×
      L.finiteSpecialOrthogonalLatticeStabilizerSubgroup) :
    (L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv
      (L.fullAdelicRealFiniteLatticeStabilizerContinuousMulEquiv x).1).1 =
        x.1 := by
  exact congrArg Prod.fst
    (L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv.apply_symm_apply
      (x.1, x.2.1))

/-- Splitting the assembled full-adelic stabilizer recovers its finite
component. -/
@[simp]
theorem fullAdelicRealFiniteLatticeStabilizerContinuousMulEquiv_finite
    (L : PositiveDefiniteIntegralLattice n)
    (x : L.ConcreteRealSpecialOrthogonalGroup ×
      L.finiteSpecialOrthogonalLatticeStabilizerSubgroup) :
    (L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv
      (L.fullAdelicRealFiniteLatticeStabilizerContinuousMulEquiv x).1).2 =
        x.2.1 := by
  exact congrArg Prod.snd
    (L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv.apply_symm_apply
      (x.1, x.2.1))

/-- Assembly followed by projection back to the real/finite carrier is the
identity. -/
theorem fullAdelicRealFiniteLatticeStabilizerContinuousMulEquiv_symm_apply_apply
    (L : PositiveDefiniteIntegralLattice n)
    (x : L.ConcreteRealSpecialOrthogonalGroup ×
      L.finiteSpecialOrthogonalLatticeStabilizerSubgroup) :
    L.fullAdelicRealFiniteLatticeStabilizerContinuousMulEquiv.symm
        (L.fullAdelicRealFiniteLatticeStabilizerContinuousMulEquiv x) = x :=
  L.fullAdelicRealFiniteLatticeStabilizerContinuousMulEquiv.symm_apply_apply x

/-- Projection followed by assembly is the identity on the full-adelic
stabilizer subgroup. -/
theorem fullAdelicRealFiniteLatticeStabilizerContinuousMulEquiv_apply_symm_apply
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.fullAdelicRealFiniteLatticeStabilizerSubgroup) :
    L.fullAdelicRealFiniteLatticeStabilizerContinuousMulEquiv
        (L.fullAdelicRealFiniteLatticeStabilizerContinuousMulEquiv.symm g) = g :=
  L.fullAdelicRealFiniteLatticeStabilizerContinuousMulEquiv.apply_symm_apply g

end PositiveDefiniteIntegralLattice
