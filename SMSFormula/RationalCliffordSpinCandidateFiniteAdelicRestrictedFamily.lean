import SMSFormula.RationalCliffordSpinCandidateFiniteAdelicLocalEvaluation

/-!
# Restricted-family presentation of finite-adelic Clifford--Spin points

This module reverses the simultaneous height-one evaluation of finite-adelic
Clifford--Spin candidate points.  The finitely many Clifford-basis and matrix
coordinates of a restricted local family are assembled as rational finite
adeles.  They define an evaluation of the polynomial presentation of the
candidate coordinate ring.  Every defining relation vanishes after evaluation
at every height-one place, hence already vanishes over the finite adeles.

The resulting assembly is inverse to local evaluation as a plain equivalence
of carriers.  Pointwise subgroup closure and the topological restricted-product
comparison are deliberately left to subsequent layers.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open scoped Matrix RestrictedProduct

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

local instance finiteAdelicSpinRestrictedFamilyPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

/-! ## Assembly of the finite coordinates -/

/-- Assemble one Clifford-basis coordinate of a restricted local family as a
rational finite adele. -/
def finiteAdelicCliffordSpinCandidateRestrictedFamilyCliffordCoordinate
    (g : V.FiniteAdelicCliffordSpinCandidateRestrictedFamily)
    (s : Finset (Fin n)) : RationalFiniteAdele :=
  ⟨fun v =>
      (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm
        ((g.1 v) (V.cliffordSpinCandidateCliffordCoordinate s)),
    (show V.IsFiniteAdelicCliffordSpinCandidateRestrictedFamily g.1 from g.2).mono
      fun _v hv => hv.1 s⟩

@[simp]
theorem finiteAdelicCliffordSpinCandidateRestrictedFamilyCliffordCoordinate_apply
    (g : V.FiniteAdelicCliffordSpinCandidateRestrictedFamily)
    (s : Finset (Fin n))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    V.finiteAdelicCliffordSpinCandidateRestrictedFamilyCliffordCoordinate g s v =
      (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm
        ((g.1 v) (V.cliffordSpinCandidateCliffordCoordinate s)) :=
  rfl

/-- Assemble one matrix coordinate of a restricted local family as a rational
finite adele. -/
def finiteAdelicCliffordSpinCandidateRestrictedFamilyMatrixCoordinate
    (g : V.FiniteAdelicCliffordSpinCandidateRestrictedFamily)
    (i j : Fin n) : RationalFiniteAdele :=
  ⟨fun v =>
      (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm
        ((g.1 v) (V.cliffordSpinCandidateMatrixCoordinate i j)),
    (show V.IsFiniteAdelicCliffordSpinCandidateRestrictedFamily g.1 from g.2).mono
      fun _v hv => hv.2.1 i j⟩

@[simp]
theorem finiteAdelicCliffordSpinCandidateRestrictedFamilyMatrixCoordinate_apply
    (g : V.FiniteAdelicCliffordSpinCandidateRestrictedFamily)
    (i j : Fin n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    V.finiteAdelicCliffordSpinCandidateRestrictedFamilyMatrixCoordinate g i j v =
      (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm
        ((g.1 v) (V.cliffordSpinCandidateMatrixCoordinate i j)) :=
  rfl

/-- The finite-adelic Clifford element assembled from the local basis
coordinates. -/
def finiteAdelicCliffordSpinCandidateRestrictedFamilyElement
    (g : V.FiniteAdelicCliffordSpinCandidateRestrictedFamily) :
    V.cliffordCoordinateBaseChangeAlgebra RationalFiniteAdele :=
  ∑ s,
    V.finiteAdelicCliffordSpinCandidateRestrictedFamilyCliffordCoordinate g s •
      V.cliffordCoordinateBaseChangeBasis RationalFiniteAdele s

@[simp]
theorem finiteAdelicCliffordSpinCandidateRestrictedFamilyElement_repr
    (g : V.FiniteAdelicCliffordSpinCandidateRestrictedFamily)
    (u : Finset (Fin n)) :
    (V.cliffordCoordinateBaseChangeBasis RationalFiniteAdele).repr
        (V.finiteAdelicCliffordSpinCandidateRestrictedFamilyElement g) u =
      V.finiteAdelicCliffordSpinCandidateRestrictedFamilyCliffordCoordinate g u := by
  rw [finiteAdelicCliffordSpinCandidateRestrictedFamilyElement, map_sum,
    Finsupp.coe_finset_sum, Finset.sum_apply]
  rw [Finset.sum_eq_single u]
  · rw [map_smul, Module.Basis.repr_self]
    simp
  · intro s _ hsu
    rw [map_smul, Module.Basis.repr_self]
    simp [hsu]
  · simp

/-- The finite-adelic matrix assembled from the local matrix coordinates. -/
def finiteAdelicCliffordSpinCandidateRestrictedFamilyMatrix
    (g : V.FiniteAdelicCliffordSpinCandidateRestrictedFamily) :
    Matrix (Fin n) (Fin n) RationalFiniteAdele :=
  fun i j =>
    V.finiteAdelicCliffordSpinCandidateRestrictedFamilyMatrixCoordinate g i j

/-- Polynomial evaluation at the assembled finite coordinates. -/
def finiteAdelicCliffordSpinCandidateRestrictedFamilyEvaluation
    (g : V.FiniteAdelicCliffordSpinCandidateRestrictedFamily) :
    cliffordSpinCandidatePolynomialRing n →ₐ[ℚ] RationalFiniteAdele :=
  V.cliffordSpinCandidateBaseChangeEvaluation RationalFiniteAdele
    (V.finiteAdelicCliffordSpinCandidateRestrictedFamilyElement g)
    (V.finiteAdelicCliffordSpinCandidateRestrictedFamilyMatrix g)

/-! ## Local comparison and quotient lift -/

/-- Evaluating the assembled polynomial coordinates at one height-one place
is the same as evaluating the polynomial through the given local point. -/
theorem finiteAdelicCliffordSpinCandidateRestrictedFamilyEvaluation_local
    (g : V.FiniteAdelicCliffordSpinCandidateRestrictedFamily)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    (finiteAdelicCliffordSpinCandidateHeightOneAlgHom v).comp
        (V.finiteAdelicCliffordSpinCandidateRestrictedFamilyEvaluation g) =
      (g.1 v).comp
        (Ideal.Quotient.mkₐ ℚ V.cliffordSpinCandidateRelationIdeal) := by
  apply MvPolynomial.algHom_ext
  intro z
  rcases z with s | ij
  · simp only [AlgHom.comp_apply,
      finiteAdelicCliffordSpinCandidateRestrictedFamilyEvaluation]
    rw [show MvPolynomial.X (Sum.inl s) =
      cliffordSpinVariable (n := n) s by rfl,
      V.cliffordSpinCandidateBaseChangeEvaluation_cliffordVariable]
    change
      (finiteAdelicCliffordSpinCandidateHeightOneAlgHom v)
          ((V.cliffordCoordinateBaseChangeBasis RationalFiniteAdele).repr
            (V.finiteAdelicCliffordSpinCandidateRestrictedFamilyElement g) s) =
        (g.1 v) (V.cliffordSpinCandidateCliffordCoordinate s)
    rw [V.finiteAdelicCliffordSpinCandidateRestrictedFamilyElement_repr]
    change
      (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v)
          ((Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm
            ((g.1 v) (V.cliffordSpinCandidateCliffordCoordinate s))) = _
    exact
      (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).apply_symm_apply _
  · rcases ij with ⟨i, j⟩
    simp only [AlgHom.comp_apply,
      finiteAdelicCliffordSpinCandidateRestrictedFamilyEvaluation]
    rw [show MvPolynomial.X (Sum.inr (i, j)) =
      cliffordSpinMatrixVariable (n := n) i j by rfl,
      V.cliffordSpinCandidateBaseChangeEvaluation_matrixVariable]
    change
      (finiteAdelicCliffordSpinCandidateHeightOneAlgHom v)
          (V.finiteAdelicCliffordSpinCandidateRestrictedFamilyMatrix g i j) =
        (g.1 v) (V.cliffordSpinCandidateMatrixCoordinate i j)
    change
      (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v)
          ((Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm
            ((g.1 v) (V.cliffordSpinCandidateMatrixCoordinate i j))) = _
    exact
      (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).apply_symm_apply _

/-- Every defining relation vanishes at the assembled finite-adelic
coordinates. -/
theorem cliffordSpinCandidateRelationIdeal_le_restrictedFamilyEvaluation_ker
    (g : V.FiniteAdelicCliffordSpinCandidateRestrictedFamily) :
    V.cliffordSpinCandidateRelationIdeal ≤ RingHom.ker
      (V.finiteAdelicCliffordSpinCandidateRestrictedFamilyEvaluation g).toRingHom := by
  intro p hp
  change V.finiteAdelicCliffordSpinCandidateRestrictedFamilyEvaluation g p = 0
  ext v
  let e := Rat.HeightOneSpectrum.adicCompletion.padicEquiv v
  apply e.injective
  change e
      (V.finiteAdelicCliffordSpinCandidateRestrictedFamilyEvaluation g p v) =
    e 0
  rw [map_zero]
  change
    (finiteAdelicCliffordSpinCandidateHeightOneAlgHom v)
        (V.finiteAdelicCliffordSpinCandidateRestrictedFamilyEvaluation g p) = 0
  have h := DFunLike.congr_fun
    (V.finiteAdelicCliffordSpinCandidateRestrictedFamilyEvaluation_local g v) p
  have h' :
      (finiteAdelicCliffordSpinCandidateHeightOneAlgHom v)
          (V.finiteAdelicCliffordSpinCandidateRestrictedFamilyEvaluation g p) =
        (g.1 v) (Ideal.Quotient.mk V.cliffordSpinCandidateRelationIdeal p) := by
    simpa only [AlgHom.comp_apply] using h
  rw [h']
  change (g.1 v) (Ideal.Quotient.mk V.cliffordSpinCandidateRelationIdeal p) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.2 hp, map_zero]

/-- Assemble a restricted family into a finite-adelic Clifford--Spin
candidate point. -/
def finiteAdelicCliffordSpinCandidateRestrictedFamilyAssembly
    (g : V.FiniteAdelicCliffordSpinCandidateRestrictedFamily) :
    V.FiniteAdelicCliffordSpinCandidateGroup :=
  Ideal.Quotient.liftₐ V.cliffordSpinCandidateRelationIdeal
    (V.finiteAdelicCliffordSpinCandidateRestrictedFamilyEvaluation g)
    (V.cliffordSpinCandidateRelationIdeal_le_restrictedFamilyEvaluation_ker g)

@[simp]
theorem finiteAdelicCliffordSpinCandidateRestrictedFamilyAssembly_cliffordCoordinate
    (g : V.FiniteAdelicCliffordSpinCandidateRestrictedFamily)
    (s : Finset (Fin n)) :
    V.finiteAdelicCliffordSpinCandidateRestrictedFamilyAssembly g
        (V.cliffordSpinCandidateCliffordCoordinate s) =
      V.finiteAdelicCliffordSpinCandidateRestrictedFamilyCliffordCoordinate g s := by
  simp [finiteAdelicCliffordSpinCandidateRestrictedFamilyAssembly,
    finiteAdelicCliffordSpinCandidateRestrictedFamilyEvaluation,
    cliffordSpinCandidateCliffordCoordinate]

@[simp]
theorem finiteAdelicCliffordSpinCandidateRestrictedFamilyAssembly_matrixCoordinate
    (g : V.FiniteAdelicCliffordSpinCandidateRestrictedFamily)
    (i j : Fin n) :
    V.finiteAdelicCliffordSpinCandidateRestrictedFamilyAssembly g
        (V.cliffordSpinCandidateMatrixCoordinate i j) =
      V.finiteAdelicCliffordSpinCandidateRestrictedFamilyMatrixCoordinate g i j := by
  simp [finiteAdelicCliffordSpinCandidateRestrictedFamilyAssembly,
    finiteAdelicCliffordSpinCandidateRestrictedFamilyEvaluation,
    finiteAdelicCliffordSpinCandidateRestrictedFamilyMatrix,
    cliffordSpinCandidateMatrixCoordinate]

/-! ## Both recovery laws -/

/-- Simultaneous height-one evaluation of the assembled point recovers the
original restricted family. -/
theorem finiteAdelicCliffordSpinCandidateHeightOneComponents_assembly
    (g : V.FiniteAdelicCliffordSpinCandidateRestrictedFamily) :
    V.finiteAdelicCliffordSpinCandidateHeightOneComponentsHom
        (V.finiteAdelicCliffordSpinCandidateRestrictedFamilyAssembly g) =
      g.1 := by
  funext v
  apply V.cliffordSpinCandidatePointCoordinateMap_injective
    ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]
  apply Prod.ext
  · funext s
    change
      (finiteAdelicCliffordSpinCandidateHeightOneAlgHom v)
          (V.finiteAdelicCliffordSpinCandidateRestrictedFamilyAssembly g
            (V.cliffordSpinCandidateCliffordCoordinate s)) =
        (g.1 v) (V.cliffordSpinCandidateCliffordCoordinate s)
    rw [V.finiteAdelicCliffordSpinCandidateRestrictedFamilyAssembly_cliffordCoordinate]
    change
      (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v)
          ((Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm
            ((g.1 v) (V.cliffordSpinCandidateCliffordCoordinate s))) = _
    exact
      (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).apply_symm_apply _
  · ext i j
    change
      (finiteAdelicCliffordSpinCandidateHeightOneAlgHom v)
          (V.finiteAdelicCliffordSpinCandidateRestrictedFamilyAssembly g
            (V.cliffordSpinCandidateMatrixCoordinate i j)) =
        (g.1 v) (V.cliffordSpinCandidateMatrixCoordinate i j)
    rw [V.finiteAdelicCliffordSpinCandidateRestrictedFamilyAssembly_matrixCoordinate]
    change
      (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v)
          ((Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm
            ((g.1 v) (V.cliffordSpinCandidateMatrixCoordinate i j))) = _
    exact
      (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).apply_symm_apply _

/-- Assembly of the evaluated restricted family recovers the original
finite-adelic candidate point. -/
theorem finiteAdelicCliffordSpinCandidateRestrictedFamilyAssembly_components
    (x : V.FiniteAdelicCliffordSpinCandidateGroup) :
    V.finiteAdelicCliffordSpinCandidateRestrictedFamilyAssembly
        (V.finiteAdelicCliffordSpinCandidateRestrictedFamilyMap x) = x := by
  apply V.finiteAdelicCliffordSpinCandidateHeightOneComponentsHom_injective
  exact
    V.finiteAdelicCliffordSpinCandidateHeightOneComponents_assembly
      (V.finiteAdelicCliffordSpinCandidateRestrictedFamilyMap x)

/-- The finite-adelic candidate carrier is equivalent to the carrier of
restricted local p-adic candidate families. -/
def finiteAdelicCliffordSpinCandidateRestrictedFamilyEquiv :
    V.FiniteAdelicCliffordSpinCandidateGroup ≃
      V.FiniteAdelicCliffordSpinCandidateRestrictedFamily where
  toFun := V.finiteAdelicCliffordSpinCandidateRestrictedFamilyMap
  invFun := V.finiteAdelicCliffordSpinCandidateRestrictedFamilyAssembly
  left_inv := V.finiteAdelicCliffordSpinCandidateRestrictedFamilyAssembly_components
  right_inv := by
    intro g
    apply Subtype.ext
    exact V.finiteAdelicCliffordSpinCandidateHeightOneComponents_assembly g

end RationalQuadraticSpaceMatrix
