import SMSFormula.RationalCliffordSpinCandidateIntegralSpinorNormUnitAlternative

/-!
# Splitting off an integral unit-norm line

A vector of unit norm in a p-adic integral lattice defines a normalized Gram
functional taking value one on that vector.  Its kernel is the integral
orthogonal complement, so the ambient coordinate lattice is the direct sum of
the unit-norm line and that complement.

This is the integral direct-sum carrier needed after the unit-reflection
alignment step.  The complement is finite free of rank one less than the
ambient lattice, and an integral orthogonal matrix fixing the line restricts
to a quadratic-value-preserving automorphism.  Unimodularity of the restricted
form and the dimension induction remain separate subsequent steps.
-/

noncomputable section

open Matrix
open scoped Matrix

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- Right Gram pairing with a fixed integral vector. -/
def localPadicIntegralPairingRight
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact p.Prime]
    (x : Fin n → ℤ_[p]) : (Fin n → ℤ_[p]) →ₗ[ℤ_[p]] ℤ_[p] where
  toFun y := y ⬝ᵥ Matrix.mulVec (L.pairingMatrix_padic p) x
  map_add' y z := by
    simp [dotProduct, Finset.sum_add_distrib, add_mul]
  map_smul' a y := by
    simp only [dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    simp only [RingHom.id_apply]
    ring

@[simp]
theorem localPadicIntegralPairingRight_apply
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact p.Prime]
    (x y : Fin n → ℤ_[p]) :
    L.localPadicIntegralPairingRight p x y =
      y ⬝ᵥ Matrix.mulVec (L.pairingMatrix_padic p) x :=
  rfl

/-- The integral Gram-orthogonal complement of a fixed vector. -/
def localPadicIntegralOrthogonal
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact p.Prime]
    (x : Fin n → ℤ_[p]) : Submodule ℤ_[p] (Fin n → ℤ_[p]) :=
  LinearMap.ker (L.localPadicIntegralPairingRight p x)

theorem mem_localPadicIntegralOrthogonal_iff
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact p.Prime]
    (x y : Fin n → ℤ_[p]) :
    y ∈ L.localPadicIntegralOrthogonal p x ↔
      y ⬝ᵥ Matrix.mulVec (L.pairingMatrix_padic p) x = 0 := by
  rfl

/-- Normalize the right Gram pairing by the inverse of the unit norm. -/
def localPadicIntegralUnitNormFunctional
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact p.Prime]
    (x : Fin n → ℤ_[p])
    (hx : IsUnit (L.localPadicIntegralFormValue p x)) :
    (Fin n → ℤ_[p]) →ₗ[ℤ_[p]] ℤ_[p] :=
  ((hx.unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) •
    L.localPadicIntegralPairingRight p x

theorem localPadicIntegralUnitNormFunctional_apply_self
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact p.Prime]
    (x : Fin n → ℤ_[p])
    (hx : IsUnit (L.localPadicIntegralFormValue p x)) :
    L.localPadicIntegralUnitNormFunctional p x hx x = 1 := by
  have hu : (hx.unit : ℤ_[p]) =
      L.localPadicIntegralFormValue p x := IsUnit.unit_spec hx
  change ((hx.unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) *
      L.localPadicIntegralFormValue p x = 1
  calc
    ((hx.unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) *
        L.localPadicIntegralFormValue p x =
      ((hx.unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * (hx.unit : ℤ_[p]) := by rw [hu]
    _ = 1 := by simp

theorem ker_localPadicIntegralUnitNormFunctional
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact p.Prime]
    (x : Fin n → ℤ_[p])
    (hx : IsUnit (L.localPadicIntegralFormValue p x)) :
    LinearMap.ker (L.localPadicIntegralUnitNormFunctional p x hx) =
      L.localPadicIntegralOrthogonal p x := by
  ext y
  change
    ((hx.unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) *
        L.localPadicIntegralPairingRight p x y = 0 ↔
      L.localPadicIntegralPairingRight p x y = 0
  simp

/-- A linear functional taking value one on `x` splits the line through `x`
from its kernel. -/
theorem isCompl_span_singleton_ker_of_apply_eq_one
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (x : M) (f : M →ₗ[R] R) (hf : f x = 1) :
    IsCompl (Submodule.span R ({x} : Set M)) (LinearMap.ker f) := by
  refine ⟨?_, ?_⟩
  · rw [Submodule.disjoint_def]
    intro y hyspan hyker
    rw [Submodule.mem_span_singleton] at hyspan
    rcases hyspan with ⟨r, rfl⟩
    rw [LinearMap.mem_ker] at hyker
    have hr : r = 0 := by
      simpa [hf] using hyker
    simp [hr]
  · rw [codisjoint_iff, eq_top_iff]
    intro y _hy
    refine Submodule.mem_sup.2
      ⟨(f y) • x, ?_, y - (f y) • x, ?_, ?_⟩
    · rw [Submodule.mem_span_singleton]
      exact ⟨f y, rfl⟩
    · rw [LinearMap.mem_ker]
      simp [hf]
    · simp

/-- A unit-norm integral line is complementary to its integral Gram-
orthogonal kernel. -/
theorem isCompl_span_localPadicIntegralOrthogonal_of_isUnit
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact p.Prime]
    (x : Fin n → ℤ_[p])
    (hx : IsUnit (L.localPadicIntegralFormValue p x)) :
    IsCompl
      (Submodule.span ℤ_[p] ({x} : Set (Fin n → ℤ_[p])))
      (L.localPadicIntegralOrthogonal p x) := by
  rw [← L.ker_localPadicIntegralUnitNormFunctional p x hx]
  exact isCompl_span_singleton_ker_of_apply_eq_one x
    (L.localPadicIntegralUnitNormFunctional p x hx)
    (L.localPadicIntegralUnitNormFunctional_apply_self p x hx)

/-- Product coordinates supplied by the integral unit-line splitting. -/
def localPadicIntegralUnitNormDecompositionEquiv
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact p.Prime]
    (x : Fin n → ℤ_[p])
    (hx : IsUnit (L.localPadicIntegralFormValue p x)) :
    (Submodule.span ℤ_[p] ({x} : Set (Fin n → ℤ_[p])) ×
        L.localPadicIntegralOrthogonal p x) ≃ₗ[ℤ_[p]]
      (Fin n → ℤ_[p]) :=
  Submodule.prodEquivOfIsCompl _ _
    (L.isCompl_span_localPadicIntegralOrthogonal_of_isUnit p x hx)

@[simp]
theorem localPadicIntegralUnitNormDecompositionEquiv_apply
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact p.Prime]
    (x : Fin n → ℤ_[p])
    (hx : IsUnit (L.localPadicIntegralFormValue p x))
    (y : Submodule.span ℤ_[p] ({x} : Set (Fin n → ℤ_[p])))
    (z : L.localPadicIntegralOrthogonal p x) :
    L.localPadicIntegralUnitNormDecompositionEquiv p x hx (y, z) = y + z :=
  rfl

/-- An integral orthogonal matrix fixing `x` preserves right Gram pairing
with `x`. -/
theorem localPadicIntegralPairingRight_apply_orthogonalMatrix_fixing
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact p.Prime]
    (x y : Fin n → ℤ_[p])
    (g : GL (Fin n) ℤ_[p])
    (hform : g.1ᵀ * L.pairingMatrix_padic p * g.1 =
      L.pairingMatrix_padic p)
    (hfix : (GeneralLinearGroup.toLin g).toLinearEquiv x = x) :
    L.localPadicIntegralPairingRight p x
        ((GeneralLinearGroup.toLin g).toLinearEquiv y) =
      L.localPadicIntegralPairingRight p x y := by
  have hpair := dotProduct_mulVec_eq_of_matrix_conj hform y x
  change g.1.mulVec x = x at hfix
  rw [hfix] at hpair
  change
    dotProduct (g.1.mulVec y)
        ((L.pairingMatrix_padic p).mulVec x) =
      dotProduct y ((L.pairingMatrix_padic p).mulVec x)
  exact hpair

/-- An integral orthogonal matrix fixing a unit-norm line restricts to a
linear automorphism of its integral orthogonal complement. -/
def localPadicIntegralOrthogonalRestriction
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact p.Prime]
    (x : Fin n → ℤ_[p])
    (g : GL (Fin n) ℤ_[p])
    (hform : g.1ᵀ * L.pairingMatrix_padic p * g.1 =
      L.pairingMatrix_padic p)
    (hfix : (GeneralLinearGroup.toLin g).toLinearEquiv x = x) :
    L.localPadicIntegralOrthogonal p x ≃ₗ[ℤ_[p]]
      L.localPadicIntegralOrthogonal p x where
  toFun y := ⟨(GeneralLinearGroup.toLin g).toLinearEquiv y,
    by
      rw [L.mem_localPadicIntegralOrthogonal_iff p x]
      change L.localPadicIntegralPairingRight p x
        ((GeneralLinearGroup.toLin g).toLinearEquiv y) = 0
      rw [L.localPadicIntegralPairingRight_apply_orthogonalMatrix_fixing
        p x y g hform hfix]
      exact y.property⟩
  invFun y := ⟨(GeneralLinearGroup.toLin g).toLinearEquiv.symm y,
    by
      rw [L.mem_localPadicIntegralOrthogonal_iff p x]
      change L.localPadicIntegralPairingRight p x
        ((GeneralLinearGroup.toLin g).toLinearEquiv.symm y) = 0
      have hpair :=
        L.localPadicIntegralPairingRight_apply_orthogonalMatrix_fixing
          p x ((GeneralLinearGroup.toLin g).toLinearEquiv.symm y)
          g hform hfix
      rw [(GeneralLinearGroup.toLin g).toLinearEquiv.apply_symm_apply] at hpair
      rw [← hpair]
      exact y.property⟩
  left_inv y := Subtype.ext
    ((GeneralLinearGroup.toLin g).toLinearEquiv.symm_apply_apply y)
  right_inv y := Subtype.ext
    ((GeneralLinearGroup.toLin g).toLinearEquiv.apply_symm_apply y)
  map_add' y z := Subtype.ext
    ((GeneralLinearGroup.toLin g).toLinearEquiv.map_add y z)
  map_smul' a y := Subtype.ext
    ((GeneralLinearGroup.toLin g).toLinearEquiv.map_smul a y)

@[simp]
theorem coe_localPadicIntegralOrthogonalRestriction
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact p.Prime]
    (x : Fin n → ℤ_[p])
    (g : GL (Fin n) ℤ_[p])
    (hform : g.1ᵀ * L.pairingMatrix_padic p * g.1 =
      L.pairingMatrix_padic p)
    (hfix : (GeneralLinearGroup.toLin g).toLinearEquiv x = x)
    (y : L.localPadicIntegralOrthogonal p x) :
    (L.localPadicIntegralOrthogonalRestriction p x g hform hfix y :
        Fin n → ℤ_[p]) =
      (GeneralLinearGroup.toLin g).toLinearEquiv y :=
  rfl

/-- The restricted complement automorphism preserves the restricted
quadratic value. -/
theorem localPadicIntegralFormValue_orthogonalRestriction
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact p.Prime]
    (x : Fin n → ℤ_[p])
    (g : GL (Fin n) ℤ_[p])
    (hform : g.1ᵀ * L.pairingMatrix_padic p * g.1 =
      L.pairingMatrix_padic p)
    (hfix : (GeneralLinearGroup.toLin g).toLinearEquiv x = x)
    (y : L.localPadicIntegralOrthogonal p x) :
    L.localPadicIntegralFormValue p
        (L.localPadicIntegralOrthogonalRestriction p x g hform hfix y) =
      L.localPadicIntegralFormValue p y := by
  change
    dotProduct (g.1.mulVec y)
        ((L.pairingMatrix_padic p).mulVec (g.1.mulVec y)) =
      dotProduct y ((L.pairingMatrix_padic p).mulVec y)
  exact dotProduct_mulVec_eq_of_matrix_conj hform y y

/-- The integral orthogonal complement is finitely generated over `Z_p`. -/
theorem localPadicIntegralOrthogonal_moduleFinite
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact p.Prime]
    (x : Fin n → ℤ_[p]) :
    Module.Finite ℤ_[p] (L.localPadicIntegralOrthogonal p x) := by
  infer_instance

/-- The integral orthogonal complement is free over the principal ideal
domain `Z_p`. -/
theorem localPadicIntegralOrthogonal_moduleFree
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact p.Prime]
    (x : Fin n → ℤ_[p]) :
    Module.Free ℤ_[p] (L.localPadicIntegralOrthogonal p x) := by
  infer_instance

/-- The free integral orthogonal complement has rank one less than the
ambient coordinate lattice. -/
theorem finrank_localPadicIntegralOrthogonal_add_one
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact p.Prime]
    (x : Fin n → ℤ_[p])
    (hx : IsUnit (L.localPadicIntegralFormValue p x)) :
    Module.finrank ℤ_[p] (L.localPadicIntegralOrthogonal p x) + 1 = n := by
  have hx0 : x ≠ 0 := by
    intro hzero
    apply hx.ne_zero
    simp [hzero, localPadicIntegralFormValue]
  let line := Submodule.span ℤ_[p] ({x} : Set (Fin n → ℤ_[p]))
  have hline : Module.finrank ℤ_[p] line = 1 := by
    have h := (LinearEquiv.coord ℤ_[p] (Fin n → ℤ_[p]) x hx0).finrank_eq
    simpa [line] using h
  have hdecomp :=
    (L.localPadicIntegralUnitNormDecompositionEquiv p x hx).finrank_eq
  rw [Module.finrank_prod] at hdecomp
  simpa [line, hline, add_comm] using hdecomp

end PositiveDefiniteIntegralLattice
