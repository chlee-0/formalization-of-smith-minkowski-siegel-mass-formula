import SMSFormula.RationalQuadraticIsometryGeneralSpinEquivalence
import SMSFormula.RationalCliffordGeneralSpinAdelicCarrier

/-!
# Intrinsic general-Spin presentation transport on the adelic left quotient

The multiplicative equivalence induced by a supplied anisotropic-complement
presentation commutes with coefficient extension.  In particular, it carries
the rational diagonal subgroup in the block presentation exactly onto the
rational diagonal subgroup in the ambient presentation, and therefore
descends to the existing full-adelic left-coset carriers.

This file is purely algebraic.  It installs no topology or measurable
structure and makes no Haar, quotient-measure, shell-measure, orbit-kernel, or
cutoff comparison.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open scoped TensorProduct

namespace RationalQuadraticSpaceMatrix

variable {r s : ℕ}
variable (U : RationalQuadraticSpaceMatrix r)
variable (V : RationalQuadraticSpaceMatrix s)
variable (e : U.quadraticForm.IsometryEquiv V.quadraticForm)
variable {A B : Type*}
variable [CommRing A] [Algebra ℚ A]
variable [CommRing B] [Algebra ℚ B]

/-- Rational-isometry Clifford transport commutes literally with extension of
the coefficient algebra. -/
theorem rationalIsometryCliffordBaseChangeAlgEquiv_naturality
    (f : A →ₐ[ℚ] B) (z : U.cliffordCoordinateBaseChangeAlgebra A) :
    rationalIsometryCliffordBaseChangeAlgEquiv U V e B
        (U.cliffordCoordinateBaseChangeMap f z) =
      V.cliffordCoordinateBaseChangeMap f
        (rationalIsometryCliffordBaseChangeAlgEquiv U V e A z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a z =>
      rw [U.cliffordCoordinateBaseChangeMap_tmul,
        rationalIsometryCliffordBaseChangeAlgEquiv_tmul,
        rationalIsometryCliffordBaseChangeAlgEquiv_tmul,
        V.cliffordCoordinateBaseChangeMap_tmul]

namespace AnisotropicComplementPresentation

variable {n m : ℕ}
variable {V : RationalQuadraticSpaceMatrix n} {x : Fin n → ℚ}
variable (P : V.AnisotropicComplementPresentation x m)

/-- Presentation transport of intrinsic general-Spin points commutes with
coefficient extension. -/
theorem blockToAmbientGeneralSpinIntrinsicPoint_naturality
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (f : A →ₐ[ℚ] B)
    (z : (P.blockSpace hx).CliffordGeneralSpinIntrinsicPoint A) :
    P.blockToAmbientGeneralSpinIntrinsicPoint B hx
        (CliffordGeneralSpinIntrinsicPoint.map (P.blockSpace hx) f z) =
      CliffordGeneralSpinIntrinsicPoint.map V f
        (P.blockToAmbientGeneralSpinIntrinsicPoint A hx z) := by
  apply CliffordGeneralSpinIntrinsicPoint.ext_cliffordUnit V B
  apply Units.ext
  exact rationalIsometryCliffordBaseChangeAlgEquiv_naturality
    (P.blockSpace hx) V (P.blockToAmbientIsometryEquiv hx) f
      (z.cliffordUnit :
        (P.blockSpace hx).cliffordCoordinateBaseChangeAlgebra A)

/-- The presentation equivalence commutes with the rational diagonal into the
full adeles. -/
theorem blockToAmbientGeneralSpinFullAdelic_diagonal_commutes
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (z : (P.blockSpace hx).RationalCliffordGeneralSpinGroup) :
    P.blockToAmbientGeneralSpinMulEquiv RationalAdele hx
        ((P.blockSpace hx).rationalCliffordGeneralSpinFullAdelicDiagonalHom z) =
      V.rationalCliffordGeneralSpinFullAdelicDiagonalHom
        (P.blockToAmbientGeneralSpinMulEquiv ℚ hx z) := by
  exact P.blockToAmbientGeneralSpinIntrinsicPoint_naturality hx
    (Algebra.ofId ℚ RationalAdele) z

/-- The full-adelic presentation equivalence maps the rational diagonal
subgroup exactly onto the ambient rational diagonal subgroup. -/
theorem blockToAmbientGeneralSpinFullAdelic_diagonalSubgroup_map
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    ((P.blockSpace hx).rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup).map
        (P.blockToAmbientGeneralSpinMulEquiv RationalAdele hx).toMonoidHom =
      V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup := by
  ext z
  simp only [rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup,
    Subgroup.mem_map, MonoidHom.mem_range]
  constructor
  · rintro ⟨w, ⟨q, rfl⟩, rfl⟩
    exact ⟨P.blockToAmbientGeneralSpinMulEquiv ℚ hx q,
      (P.blockToAmbientGeneralSpinFullAdelic_diagonal_commutes hx q).symm⟩
  · rintro ⟨q, rfl⟩
    let q' := (P.blockToAmbientGeneralSpinMulEquiv ℚ hx).symm q
    refine ⟨(P.blockSpace hx).rationalCliffordGeneralSpinFullAdelicDiagonalHom q',
      ⟨q', rfl⟩, ?_⟩
    change P.blockToAmbientGeneralSpinMulEquiv RationalAdele hx
        ((P.blockSpace hx).rationalCliffordGeneralSpinFullAdelicDiagonalHom q') = _
    exact (P.blockToAmbientGeneralSpinFullAdelic_diagonal_commutes hx q').trans
      (congrArg V.rationalCliffordGeneralSpinFullAdelicDiagonalHom
        ((P.blockToAmbientGeneralSpinMulEquiv ℚ hx).apply_symm_apply q))

private def leftCosetSetEquivOfMulEquiv
    {G H : Type*} [Group G] [Group H]
    (E : G ≃* H) (Γ : Subgroup G) (Δ : Subgroup H)
    (hmap : Γ.map E.toMonoidHom = Δ) :
    leftCosetSet Γ ≃ leftCosetSet Δ where
  toFun :=
    Quot.map E (by
      intro g h hgh
      rcases hgh with ⟨γ, rfl⟩
      have hγ : E (γ : G) ∈ Δ := by
        rw [← hmap]
        exact ⟨γ, γ.property, rfl⟩
      exact ⟨⟨E (γ : G), hγ⟩, by simp⟩)
  invFun :=
    Quot.map E.symm (by
      intro g h hgh
      rcases hgh with ⟨δ, rfl⟩
      have hδ : (δ : H) ∈ Γ.map E.toMonoidHom := by
        rw [hmap]
        exact δ.property
      rcases hδ with ⟨γ, hγ, heq⟩
      exact ⟨⟨γ, hγ⟩, by simp [← heq]⟩)
  left_inv := by
    intro C
    refine Quot.inductionOn C ?_
    intro g
    change Quot.mk (leftCosetSetoid Γ) (E.symm (E g)) =
      Quot.mk (leftCosetSetoid Γ) g
    rw [E.symm_apply_apply]
  right_inv := by
    intro C
    refine Quot.inductionOn C ?_
    intro g
    change Quot.mk (leftCosetSetoid Δ) (E (E.symm g)) =
      Quot.mk (leftCosetSetoid Δ) g
    rw [E.apply_symm_apply]

/-- The presentation equivalence descends canonically to the existing
rational full-adelic left-coset carriers. -/
def blockToAmbientGeneralSpinFullAdelicLeftQuotientEquiv
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    (P.blockSpace hx).FullAdelicCliffordGeneralSpinLeftQuotient ≃
      V.FullAdelicCliffordGeneralSpinLeftQuotient :=
  leftCosetSetEquivOfMulEquiv
    (P.blockToAmbientGeneralSpinMulEquiv RationalAdele hx)
    (P.blockSpace hx).rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup
    V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup
    (P.blockToAmbientGeneralSpinFullAdelic_diagonalSubgroup_map hx)

@[simp]
theorem blockToAmbientGeneralSpinFullAdelicLeftQuotientEquiv_mk
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (g : (P.blockSpace hx).FullAdelicCliffordGeneralSpinGroup) :
    P.blockToAmbientGeneralSpinFullAdelicLeftQuotientEquiv hx
        ((P.blockSpace hx).fullAdelicCliffordGeneralSpinLeftQuotientMap g) =
      V.fullAdelicCliffordGeneralSpinLeftQuotientMap
        (P.blockToAmbientGeneralSpinMulEquiv RationalAdele hx g) := by
  rfl

@[simp]
theorem blockToAmbientGeneralSpinFullAdelicLeftQuotientEquiv_symm_mk
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (g : V.FullAdelicCliffordGeneralSpinGroup) :
    (P.blockToAmbientGeneralSpinFullAdelicLeftQuotientEquiv hx).symm
        (V.fullAdelicCliffordGeneralSpinLeftQuotientMap g) =
      (P.blockSpace hx).fullAdelicCliffordGeneralSpinLeftQuotientMap
        ((P.blockToAmbientGeneralSpinMulEquiv RationalAdele hx).symm g) := by
  rfl

end AnisotropicComplementPresentation
end RationalQuadraticSpaceMatrix
