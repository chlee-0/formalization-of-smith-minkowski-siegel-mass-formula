import SMSFormula.SpecialOrthogonalFullAdelicDifferentialHaar
import SMSFormula.RationalSpecialOrthogonalTamagawa

/-!
# Concrete lattice carrier for the rational special-orthogonal adelic quotient

The general Tamagawa interface is phrased for a
`RationalQuadraticSpaceMatrix`, while the internally constructed
differential Haar measure lives on the concrete full-adelic group attached
to an integral lattice.  This module identifies those duplicate carriers for
the rational form matrix of the lattice.  It also identifies their diagonal
rational subgroups and abstract left-coset quotients.

This is a carrier bridge.  It defines no quotient measure, proves
no Weil formula, and introduces no Tamagawa value or measure comparison.
-/

noncomputable section

open MeasureTheory
open RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The rational quadratic-space presentation underlying an integral
lattice. -/
def rationalQuadraticSpaceMatrix
    (L : PositiveDefiniteIntegralLattice n) :
    RationalQuadraticSpaceMatrix n where
  pairingMatrix := L.rationalFormMatrix
  form_symm := L.form_symm.map (algebraMap ℤ ℚ)
  form_det_ne_zero := L.rationalFormMatrix_det_ne_zero

@[simp]
theorem rationalQuadraticSpaceMatrix_pairingMatrix
    (L : PositiveDefiniteIntegralLattice n) :
    L.rationalQuadraticSpaceMatrix.pairingMatrix =
      L.rationalFormMatrix :=
  rfl

/-- The general rational special-orthogonal carrier is the lattice rational
special-orthogonal carrier. -/
def rationalQuadraticSpaceMatrixRationalSpecialOrthogonalEquiv
    (L : PositiveDefiniteIntegralLattice n) :
    L.rationalQuadraticSpaceMatrix.RationalSpecialOrthogonalGroup ≃*
      L.rationalSpecialOrthogonalMatrixSubgroup :=
  MulEquiv.refl _

@[simp]
theorem rationalQuadraticSpaceMatrixRationalSpecialOrthogonalEquiv_apply
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.rationalQuadraticSpaceMatrix.RationalSpecialOrthogonalGroup) :
    L.rationalQuadraticSpaceMatrixRationalSpecialOrthogonalEquiv g = g :=
  rfl

/-- The full-adelic form matrix in the general presentation is the
lattice full-adelic form matrix. -/
theorem rationalQuadraticSpaceMatrix_fullAdelicFormMatrix
    (L : PositiveDefiniteIntegralLattice n) :
    L.rationalQuadraticSpaceMatrix.fullAdelicFormMatrix =
      L.fullAdelicFormMatrix := by
  rw [L.fullAdelicFormMatrix_eq_map_rationalFormMatrix]
  rfl

private theorem specialFormPreservingMatrixSubgroup_cast_apply_matrix
    {F F' : Matrix (Fin n) (Fin n) RationalAdele}
    (h : F = F')
    (g : ↥(specialFormPreservingMatrixSubgroup F)) :
    ((MulEquiv.cast
      (M := fun A : Matrix (Fin n) (Fin n) RationalAdele =>
        ↥(specialFormPreservingMatrixSubgroup A)) h g).1.1.1 :
          Matrix _ _ _) =
      g.1.1.1 := by
  cases h
  rfl

private theorem specialFormPreservingMatrixSubgroup_cast_symm_apply_matrix
    {F F' : Matrix (Fin n) (Fin n) RationalAdele}
    (h : F = F')
    (g : ↥(specialFormPreservingMatrixSubgroup F')) :
    (((MulEquiv.cast
      (M := fun A : Matrix (Fin n) (Fin n) RationalAdele =>
        ↥(specialFormPreservingMatrixSubgroup A)) h).symm g).1.1.1 :
          Matrix _ _ _) =
      g.1.1.1 := by
  cases h
  rfl

private theorem specialFormPreservingMatrixSubgroup_cast_continuous
    {F F' : Matrix (Fin n) (Fin n) RationalAdele}
    (h : F = F') :
    Continuous
      (MulEquiv.cast
        (M := fun A : Matrix (Fin n) (Fin n) RationalAdele =>
          ↥(specialFormPreservingMatrixSubgroup A)) h) := by
  cases h
  exact continuous_id

private theorem specialFormPreservingMatrixSubgroup_cast_symm_continuous
    {F F' : Matrix (Fin n) (Fin n) RationalAdele}
    (h : F = F') :
    Continuous
      (MulEquiv.cast
        (M := fun A : Matrix (Fin n) (Fin n) RationalAdele =>
          ↥(specialFormPreservingMatrixSubgroup A)) h).symm := by
  cases h
  exact continuous_id

/-- The general and lattice full-adelic special-orthogonal carriers for the
lattice rational form matrix are canonically multiplicatively equivalent. -/
def rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalEquiv
    (L : PositiveDefiniteIntegralLattice n) :
    L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup ≃*
      L.ConcreteFullAdelicSpecialOrthogonalGroup :=
  MulEquiv.cast
    (M := fun F : Matrix (Fin n) (Fin n) RationalAdele =>
      ↥(specialFormPreservingMatrixSubgroup F))
    L.rationalQuadraticSpaceMatrix_fullAdelicFormMatrix

/-- The full-adelic carrier identification is a topological group
equivalence. -/
def rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalContinuousEquiv
    (L : PositiveDefiniteIntegralLattice n) :
    L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup ≃ₜ*
      L.ConcreteFullAdelicSpecialOrthogonalGroup where
  toMulEquiv :=
    L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalEquiv
  continuous_toFun :=
    specialFormPreservingMatrixSubgroup_cast_continuous
      L.rationalQuadraticSpaceMatrix_fullAdelicFormMatrix
  continuous_invFun :=
    specialFormPreservingMatrixSubgroup_cast_symm_continuous
      L.rationalQuadraticSpaceMatrix_fullAdelicFormMatrix

@[simp]
theorem
    rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalEquiv_apply_matrix
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup) :
    (L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalEquiv g).1.1.1 =
      g.1.1.1 :=
  by
    exact specialFormPreservingMatrixSubgroup_cast_apply_matrix
      L.rationalQuadraticSpaceMatrix_fullAdelicFormMatrix g

@[simp]
theorem
    rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalEquiv_symm_apply_matrix
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFullAdelicSpecialOrthogonalGroup) :
    (L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalEquiv.symm
        g).1.1.1 =
      g.1.1.1 :=
  by
    exact specialFormPreservingMatrixSubgroup_cast_symm_apply_matrix
      L.rationalQuadraticSpaceMatrix_fullAdelicFormMatrix g

/-- The rational diagonal embeddings commute with the concrete full-adelic
carrier identification. -/
theorem rationalQuadraticSpaceMatrix_diagonal_commutes
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.rationalQuadraticSpaceMatrix.RationalSpecialOrthogonalGroup) :
    L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalEquiv
        (L.rationalQuadraticSpaceMatrix
          |>.rationalSpecialOrthogonalFullAdelicDiagonalHom g) =
      L.rationalSpecialOrthogonalFullAdelicDiagonalHom g := by
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  simpa using
    L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalEquiv_apply_matrix
      (L.rationalQuadraticSpaceMatrix
        |>.rationalSpecialOrthogonalFullAdelicDiagonalHom g)

/-- Mapping the general rational diagonal subgroup across the carrier
identification gives exactly the lattice diagonal subgroup. -/
theorem rationalQuadraticSpaceMatrix_diagonalSubgroup_map
    (L : PositiveDefiniteIntegralLattice n) :
    (L.rationalQuadraticSpaceMatrix
      |>.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup).map
        L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalEquiv.toMonoidHom =
      L.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup := by
  ext x
  simp only [
    RationalQuadraticSpaceMatrix.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup,
    rationalSpecialOrthogonalFullAdelicDiagonalSubgroup, Subgroup.mem_map,
    MonoidHom.mem_range]
  constructor
  · rintro ⟨y, ⟨g, rfl⟩, hy⟩
    exact
      ⟨g, (L.rationalQuadraticSpaceMatrix_diagonal_commutes g).symm.trans
        hy⟩
  · rintro ⟨g, hg⟩
    exact
      ⟨L.rationalQuadraticSpaceMatrix
          |>.rationalSpecialOrthogonalFullAdelicDiagonalHom g,
        ⟨g, rfl⟩,
        (L.rationalQuadraticSpaceMatrix_diagonal_commutes g).trans hg⟩

private def leftCosetSetEquivOfMulEquiv
    {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (Gamma : Subgroup G) (Delta : Subgroup H)
    (hmap : Gamma.map e.toMonoidHom = Delta) :
    leftCosetSet Gamma ≃ leftCosetSet Delta where
  toFun :=
    Quot.map e (by
      intro x y hxy
      rcases hxy with ⟨gamma, rfl⟩
      have hgamma : e (gamma : G) ∈ Delta := by
        rw [← hmap]
        exact ⟨gamma, gamma.property, rfl⟩
      exact
        ⟨⟨e (gamma : G), hgamma⟩, by
          simp⟩)
  invFun :=
    Quot.map e.symm (by
      intro x y hxy
      rcases hxy with ⟨delta, rfl⟩
      have hdelta : (delta : H) ∈ Gamma.map e.toMonoidHom := by
        rw [hmap]
        exact delta.property
      rcases hdelta with ⟨gamma, hgamma, heq⟩
      exact
        ⟨⟨gamma, hgamma⟩, by
          simp [← heq]⟩)
  left_inv := by
    intro C
    refine Quot.inductionOn C ?_
    intro x
    change
      Quot.mk (leftCosetSetoid Gamma) (e.symm (e x)) =
        Quot.mk (leftCosetSetoid Gamma) x
    rw [e.symm_apply_apply]
  right_inv := by
    intro C
    refine Quot.inductionOn C ?_
    intro x
    change
      Quot.mk (leftCosetSetoid Delta) (e (e.symm x)) =
        Quot.mk (leftCosetSetoid Delta) x
    rw [e.apply_symm_apply]

/-- The lattice form of the rational full-adelic left quotient. -/
abbrev ConcreteFullAdelicSpecialOrthogonalLeftQuotient
    (L : PositiveDefiniteIntegralLattice n) :=
  leftCosetSet L.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup

/-- The canonical map to the lattice rational full-adelic left
quotient. -/
def concreteFullAdelicSpecialOrthogonalLeftQuotientMap
    (L : PositiveDefiniteIntegralLattice n) :
    L.ConcreteFullAdelicSpecialOrthogonalGroup →
      L.ConcreteFullAdelicSpecialOrthogonalLeftQuotient :=
  leftCosetMap L.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup

/-- The quotient measurable structure generated by the lattice
left-quotient map. -/
instance concreteFullAdelicSpecialOrthogonalLeftQuotientMeasurableSpace
    (L : PositiveDefiniteIntegralLattice n) :
    MeasurableSpace L.ConcreteFullAdelicSpecialOrthogonalLeftQuotient :=
  MeasurableSpace.map
    L.concreteFullAdelicSpecialOrthogonalLeftQuotientMap
    (borel L.ConcreteFullAdelicSpecialOrthogonalGroup)

theorem concreteFullAdelicSpecialOrthogonalLeftQuotientMap_measurable
    (L : PositiveDefiniteIntegralLattice n) :
    Measurable L.concreteFullAdelicSpecialOrthogonalLeftQuotientMap :=
  leftCosetMap_measurable_map
    L.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup

/-- The general rational quadratic-space left quotient is canonically the
lattice left quotient. -/
def rationalQuadraticSpaceMatrixFullAdelicLeftQuotientEquiv
    (L : PositiveDefiniteIntegralLattice n) :
    L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalLeftQuotient ≃
      L.ConcreteFullAdelicSpecialOrthogonalLeftQuotient :=
  leftCosetSetEquivOfMulEquiv
    L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalEquiv
    (L.rationalQuadraticSpaceMatrix
      |>.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup)
    L.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup
    L.rationalQuadraticSpaceMatrix_diagonalSubgroup_map

@[simp]
theorem rationalQuadraticSpaceMatrixFullAdelicLeftQuotientEquiv_mk
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup) :
    L.rationalQuadraticSpaceMatrixFullAdelicLeftQuotientEquiv
        (L.rationalQuadraticSpaceMatrix
          |>.fullAdelicSpecialOrthogonalLeftQuotientMap g) =
      L.concreteFullAdelicSpecialOrthogonalLeftQuotientMap
        (L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalEquiv g) :=
  by
    rfl

@[simp]
theorem rationalQuadraticSpaceMatrixFullAdelicLeftQuotientEquiv_symm_mk
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFullAdelicSpecialOrthogonalGroup) :
    L.rationalQuadraticSpaceMatrixFullAdelicLeftQuotientEquiv.symm
        (L.concreteFullAdelicSpecialOrthogonalLeftQuotientMap g) =
      L.rationalQuadraticSpaceMatrix.fullAdelicSpecialOrthogonalLeftQuotientMap
        (L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalEquiv.symm
          g) :=
  by
    rfl

/-- The quotient carrier equivalence is measurable for the quotient
measurable structures generated by the two canonical quotient maps. -/
theorem rationalQuadraticSpaceMatrixFullAdelicLeftQuotientEquiv_measurable
    (L : PositiveDefiniteIntegralLattice n) :
    Measurable
      L.rationalQuadraticSpaceMatrixFullAdelicLeftQuotientEquiv := by
  rw [measurable_iff_le_map]
  change
    MeasurableSpace.map
        L.concreteFullAdelicSpecialOrthogonalLeftQuotientMap
        (borel L.ConcreteFullAdelicSpecialOrthogonalGroup) ≤
      MeasurableSpace.map
        L.rationalQuadraticSpaceMatrixFullAdelicLeftQuotientEquiv
        (MeasurableSpace.map
          L.rationalQuadraticSpaceMatrix.fullAdelicSpecialOrthogonalLeftQuotientMap
          (borel
            L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup))
  rw [MeasurableSpace.map_comp]
  have hcomp :
      L.rationalQuadraticSpaceMatrixFullAdelicLeftQuotientEquiv ∘
          L.rationalQuadraticSpaceMatrix.fullAdelicSpecialOrthogonalLeftQuotientMap =
        L.concreteFullAdelicSpecialOrthogonalLeftQuotientMap ∘
          L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalEquiv := by
    funext g
    exact
      L.rationalQuadraticSpaceMatrixFullAdelicLeftQuotientEquiv_mk g
  rw [hcomp, ← MeasurableSpace.map_comp]
  have he :
      Measurable
        L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalContinuousEquiv :=
    (L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalContinuousEquiv).continuous_toFun.measurable
  exact
    MeasurableSpace.map_mono
      (measurable_iff_le_map.mp he)

/-- The inverse quotient carrier identification is measurable. -/
theorem rationalQuadraticSpaceMatrixFullAdelicLeftQuotientEquiv_symm_measurable
    (L : PositiveDefiniteIntegralLattice n) :
    Measurable
      L.rationalQuadraticSpaceMatrixFullAdelicLeftQuotientEquiv.symm := by
  rw [measurable_iff_le_map]
  change
    MeasurableSpace.map
        L.rationalQuadraticSpaceMatrix.fullAdelicSpecialOrthogonalLeftQuotientMap
        (borel
          L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup) ≤
      MeasurableSpace.map
        L.rationalQuadraticSpaceMatrixFullAdelicLeftQuotientEquiv.symm
        (MeasurableSpace.map
          L.concreteFullAdelicSpecialOrthogonalLeftQuotientMap
          (borel L.ConcreteFullAdelicSpecialOrthogonalGroup))
  rw [MeasurableSpace.map_comp]
  have hcomp :
      L.rationalQuadraticSpaceMatrixFullAdelicLeftQuotientEquiv.symm ∘
          L.concreteFullAdelicSpecialOrthogonalLeftQuotientMap =
        L.rationalQuadraticSpaceMatrix.fullAdelicSpecialOrthogonalLeftQuotientMap ∘
          L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalEquiv.symm := by
    funext g
    exact
      L.rationalQuadraticSpaceMatrixFullAdelicLeftQuotientEquiv_symm_mk g
  rw [hcomp, ← MeasurableSpace.map_comp]
  have he :
      Measurable
        L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalContinuousEquiv.symm :=
    (L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalContinuousEquiv).continuous_invFun.measurable
  exact
    MeasurableSpace.map_mono
      (measurable_iff_le_map.mp he)

/-- The general and concrete left quotients are measurably equivalent. -/
def rationalQuadraticSpaceMatrixFullAdelicLeftQuotientMeasurableEquiv
    (L : PositiveDefiniteIntegralLattice n) :
    L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalLeftQuotient ≃ᵐ
      L.ConcreteFullAdelicSpecialOrthogonalLeftQuotient where
  toEquiv := L.rationalQuadraticSpaceMatrixFullAdelicLeftQuotientEquiv
  measurable_toFun :=
    L.rationalQuadraticSpaceMatrixFullAdelicLeftQuotientEquiv_measurable
  measurable_invFun :=
    L.rationalQuadraticSpaceMatrixFullAdelicLeftQuotientEquiv_symm_measurable

end PositiveDefiniteIntegralLattice
