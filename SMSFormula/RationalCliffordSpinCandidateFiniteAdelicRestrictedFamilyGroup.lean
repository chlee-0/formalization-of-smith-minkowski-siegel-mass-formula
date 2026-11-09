import SMSFormula.RationalCliffordSpinCandidateFiniteAdelicRestrictedFamily

/-!
# Group structure on restricted finite-adelic Clifford--Spin families

The literal cofinite integral-coordinate condition is stable under pointwise
group operations.  Rather than repeat rational-denominator calculations for
the Clifford multiplication formulas, this module uses the completed
restricted-family assembly: every restricted family is the local evaluation
of a finite-adelic candidate point, and simultaneous evaluation is a group
homomorphism.

The resulting subgroup is multiplicatively equivalent to the finite-adelic
candidate group.  No reverse-continuity or local-compactness statement is made.
-/

noncomputable section

open PositiveDefiniteIntegralLattice

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

/-! ## The pointwise restricted-family subgroup -/

/-- Restricted p-adic Clifford--Spin candidate families form a subgroup of
the unrestricted dependent product under pointwise operations. -/
def finiteAdelicCliffordSpinCandidateRestrictedFamilySubgroup :
    Subgroup V.HeightOnePadicCliffordSpinCandidateGroupProduct where
  carrier := {g | V.IsFiniteAdelicCliffordSpinCandidateRestrictedFamily g}
  one_mem' := by
    have h :=
      V.finiteAdelicCliffordSpinCandidateHeightOneComponents_isRestrictedFamily
        (1 : V.FiniteAdelicCliffordSpinCandidateGroup)
    simpa only [map_one] using h
  mul_mem' := by
    intro g h hg hh
    let g' : V.FiniteAdelicCliffordSpinCandidateRestrictedFamily := ⟨g, hg⟩
    let h' : V.FiniteAdelicCliffordSpinCandidateRestrictedFamily := ⟨h, hh⟩
    have hres :=
      V.finiteAdelicCliffordSpinCandidateHeightOneComponents_isRestrictedFamily
        (V.finiteAdelicCliffordSpinCandidateRestrictedFamilyAssembly g' *
          V.finiteAdelicCliffordSpinCandidateRestrictedFamilyAssembly h')
    rw [map_mul,
      V.finiteAdelicCliffordSpinCandidateHeightOneComponents_assembly,
      V.finiteAdelicCliffordSpinCandidateHeightOneComponents_assembly] at hres
    exact hres
  inv_mem' := by
    intro g hg
    let g' : V.FiniteAdelicCliffordSpinCandidateRestrictedFamily := ⟨g, hg⟩
    have hres :=
      V.finiteAdelicCliffordSpinCandidateHeightOneComponents_isRestrictedFamily
        (V.finiteAdelicCliffordSpinCandidateRestrictedFamilyAssembly g')⁻¹
    rw [map_inv,
      V.finiteAdelicCliffordSpinCandidateHeightOneComponents_assembly] at hres
    exact hres

@[simp]
theorem mem_finiteAdelicCliffordSpinCandidateRestrictedFamilySubgroup_iff
    (g : V.HeightOnePadicCliffordSpinCandidateGroupProduct) :
    g ∈ V.finiteAdelicCliffordSpinCandidateRestrictedFamilySubgroup ↔
      V.IsFiniteAdelicCliffordSpinCandidateRestrictedFamily g :=
  Iff.rfl

/-- The canonical pointwise group carrier of restricted local candidate
families. -/
abbrev FiniteAdelicCliffordSpinCandidateRestrictedFamilyGroup :=
  V.finiteAdelicCliffordSpinCandidateRestrictedFamilySubgroup

/-! ## Identification with the earlier carrier and multiplicative equivalence -/

/-- The earlier restricted-family subtype and the canonical subgroup have the
same elements. -/
def finiteAdelicCliffordSpinCandidateRestrictedFamilyCarrierEquivGroup :
    V.FiniteAdelicCliffordSpinCandidateRestrictedFamily ≃
      V.FiniteAdelicCliffordSpinCandidateRestrictedFamilyGroup where
  toFun g := ⟨g.1, g.2⟩
  invFun g := ⟨g.1, g.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Evaluation identifies the finite-adelic Clifford--Spin candidate group
with the pointwise subgroup of restricted p-adic candidate families. -/
def finiteAdelicCliffordSpinCandidateRestrictedFamilyMulEquiv :
    V.FiniteAdelicCliffordSpinCandidateGroup ≃*
      V.FiniteAdelicCliffordSpinCandidateRestrictedFamilyGroup where
  toFun x :=
    ⟨V.finiteAdelicCliffordSpinCandidateHeightOneComponentsHom x,
      V.finiteAdelicCliffordSpinCandidateHeightOneComponents_isRestrictedFamily x⟩
  invFun g :=
    V.finiteAdelicCliffordSpinCandidateRestrictedFamilyAssembly
      ⟨g.1, g.2⟩
  left_inv :=
    V.finiteAdelicCliffordSpinCandidateRestrictedFamilyAssembly_components
  right_inv := by
    intro g
    apply Subtype.ext
    exact V.finiteAdelicCliffordSpinCandidateHeightOneComponents_assembly
      ⟨g.1, g.2⟩
  map_mul' := by
    intro x y
    apply Subtype.ext
    exact
      V.finiteAdelicCliffordSpinCandidateHeightOneComponentsHom.map_mul x y

@[simp]
theorem finiteAdelicCliffordSpinCandidateRestrictedFamilyMulEquiv_apply
    (x : V.FiniteAdelicCliffordSpinCandidateGroup) :
    (V.finiteAdelicCliffordSpinCandidateRestrictedFamilyMulEquiv x).1 =
      V.finiteAdelicCliffordSpinCandidateHeightOneComponentsHom x :=
  rfl

@[simp]
theorem finiteAdelicCliffordSpinCandidateRestrictedFamilyMulEquiv_symm_apply
    (g : V.FiniteAdelicCliffordSpinCandidateRestrictedFamilyGroup) :
    V.finiteAdelicCliffordSpinCandidateRestrictedFamilyMulEquiv.symm g =
      V.finiteAdelicCliffordSpinCandidateRestrictedFamilyAssembly
        ⟨g.1, g.2⟩ :=
  rfl

end RationalQuadraticSpaceMatrix
