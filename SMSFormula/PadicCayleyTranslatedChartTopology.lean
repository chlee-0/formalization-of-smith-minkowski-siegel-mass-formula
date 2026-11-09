import SMSFormula.AdelicProperFinitePresentation
import SMSFormula.PadicCayleyTargetChartCoordinateTopology

/-!
# Translated p-adic Cayley chart topology

The matrix-valued special-orthogonal carrier is identified with the
units-valued special-orthogonal subgroup.  The exact Cayley inverse domain is
transported across this homeomorphism and then translated on the left by an
arbitrary group point.  Composing with the Cayley homeomorphism gives
an exact translated chart from the transported skew-adjoint source.

Only the chart sets, their topology, and their exact pointwise formulas are
developed here.  No measure transport, invariance, overlap comparison, or
chart gluing is introduced.
-/

noncomputable section

open scoped Matrix

namespace PositiveDefiniteIntegralLattice

open Matrix

variable {n : ℕ}

/-- The exact p-adic Cayley target, transported from the matrix-valued
special-orthogonal carrier to the existing units-valued special subgroup. -/
def padicCayleySpecialOrthogonalSubgroupInverseDomain
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    Set (specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :=
  specialOrthogonalMatrixSetHomeomorphSpecialSubgroup
      (F.map (algebraMap ℚ ℚ_[p])) ''
    Matrix.padicCayleySpecialOrthogonalInverseDomain F p

/-- The exact matrix-valued and units-valued p-adic Cayley targets are
homeomorphic. -/
def padicCayleySpecialOrthogonalSubgroupInverseDomainHomeomorph
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    Matrix.padicCayleySpecialOrthogonalInverseDomain F p ≃ₜ
      padicCayleySpecialOrthogonalSubgroupInverseDomain F p :=
  (specialOrthogonalMatrixSetHomeomorphSpecialSubgroup
    (F.map (algebraMap ℚ ℚ_[p]))).image
      (Matrix.padicCayleySpecialOrthogonalInverseDomain F p)

@[simp]
theorem coe_padicCayleySpecialOrthogonalSubgroupInverseDomainHomeomorph_apply
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (g : Matrix.padicCayleySpecialOrthogonalInverseDomain F p) :
    (padicCayleySpecialOrthogonalSubgroupInverseDomainHomeomorph
        F p g).1.1.1.1 =
      (g.1 : Matrix (Fin n) (Fin n) ℚ_[p]) :=
  rfl

@[simp]
theorem coe_padicCayleySpecialOrthogonalSubgroupInverseDomainHomeomorph_symm_apply
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (g : padicCayleySpecialOrthogonalSubgroupInverseDomain F p) :
    (((padicCayleySpecialOrthogonalSubgroupInverseDomainHomeomorph
        F p).symm g).1 : Matrix (Fin n) (Fin n) ℚ_[p]) =
      g.1.1.1.1 :=
  rfl

/-- Membership in the transported identity target is exactly the original
ambient matrix inverse-domain condition. -/
theorem mem_padicCayleySpecialOrthogonalSubgroupInverseDomain_iff
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (g : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    g ∈ padicCayleySpecialOrthogonalSubgroupInverseDomain F p ↔
      (g.1.1.1 : Matrix (Fin n) (Fin n) ℚ_[p]) ∈
        Matrix.padicCayleyInverseDomain p := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hg
    let e :=
      specialOrthogonalMatrixSetHomeomorphSpecialSubgroup
        (F.map (algebraMap ℚ ℚ_[p]))
    let x : Matrix.padicCayleySpecialOrthogonalInverseDomain F p :=
      ⟨e.symm g, by
        change ((e.symm g : Matrix.specialOrthogonalMatrixSet
          (F.map (algebraMap ℚ ℚ_[p]))) :
            Matrix (Fin n) (Fin n) ℚ_[p]) ∈
          Matrix.padicCayleyInverseDomain p
        simpa [e] using hg⟩
    exact ⟨x, x.2, e.apply_symm_apply g⟩

/-- The transported exact identity target is open in the units-valued
special-orthogonal subgroup. -/
theorem isOpen_padicCayleySpecialOrthogonalSubgroupInverseDomain
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    IsOpen (padicCayleySpecialOrthogonalSubgroupInverseDomain F p) := by
  exact
    (specialOrthogonalMatrixSetHomeomorphSpecialSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))).isOpen_image.mpr
        (Matrix.isOpen_padicCayleySpecialOrthogonalInverseDomain F p)

/-- The identity belongs to the transported exact p-adic Cayley target. -/
@[simp]
theorem one_mem_padicCayleySpecialOrthogonalSubgroupInverseDomain
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    (1 : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) ∈
        padicCayleySpecialOrthogonalSubgroupInverseDomain F p := by
  refine ⟨Matrix.specialOrthogonalMatrixIdentity
      (F.map (algebraMap ℚ ℚ_[p])),
    Matrix.specialOrthogonalMatrixIdentity_mem_padicCayleyInverseDomain
      F p, ?_⟩
  exact specialOrthogonalMatrixSetToSpecialSubgroup_identity
    (F.map (algebraMap ℚ ℚ_[p]))

/-- The exact p-adic Cayley target translated on the left by a specified
special-orthogonal center. -/
def padicCayleySpecialOrthogonalTranslatedTarget
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (c : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    Set (specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :=
  Homeomorph.mulLeft c ''
    padicCayleySpecialOrthogonalSubgroupInverseDomain F p

/-- A group point belongs to the translated target exactly when translating
it back by the inverse center lands in the identity target. -/
theorem mem_padicCayleySpecialOrthogonalTranslatedTarget_iff
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (c g : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    g ∈ padicCayleySpecialOrthogonalTranslatedTarget F p c ↔
      c⁻¹ * g ∈
        padicCayleySpecialOrthogonalSubgroupInverseDomain F p := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro hg
    exact ⟨c⁻¹ * g, hg, by simp⟩

/-- Ambient matrix membership in a translated target is the inverse-domain
condition after multiplying by the inverse center. -/
theorem mem_padicCayleySpecialOrthogonalTranslatedTarget_iff_inverseDomain
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (c g : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    g ∈ padicCayleySpecialOrthogonalTranslatedTarget F p c ↔
      (((c⁻¹ * g).1.1.1 : Matrix (Fin n) (Fin n) ℚ_[p])) ∈
        Matrix.padicCayleyInverseDomain p := by
  rw [mem_padicCayleySpecialOrthogonalTranslatedTarget_iff,
    mem_padicCayleySpecialOrthogonalSubgroupInverseDomain_iff]

/-- Every translated p-adic Cayley target is open in the units-valued
special-orthogonal subgroup. -/
theorem isOpen_padicCayleySpecialOrthogonalTranslatedTarget
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (c : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    IsOpen (padicCayleySpecialOrthogonalTranslatedTarget F p c) := by
  exact (Homeomorph.mulLeft c).isOpen_image.mpr
    (isOpen_padicCayleySpecialOrthogonalSubgroupInverseDomain F p)

/-- The center belongs to its translated exact p-adic Cayley target. -/
@[simp]
theorem self_mem_padicCayleySpecialOrthogonalTranslatedTarget
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (c : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    c ∈ padicCayleySpecialOrthogonalTranslatedTarget F p c := by
  rw [mem_padicCayleySpecialOrthogonalTranslatedTarget_iff]
  convert one_mem_padicCayleySpecialOrthogonalSubgroupInverseDomain F p using 1
  simp

/-- Left multiplication identifies the exact identity Cayley target with its
translate around an arbitrary special-orthogonal center. -/
def padicCayleySpecialOrthogonalLeftTranslateHomeomorph
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (c : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    padicCayleySpecialOrthogonalSubgroupInverseDomain F p ≃ₜ
      padicCayleySpecialOrthogonalTranslatedTarget F p c :=
  (Homeomorph.mulLeft c).image
    (padicCayleySpecialOrthogonalSubgroupInverseDomain F p)

@[simp]
theorem coe_padicCayleySpecialOrthogonalLeftTranslateHomeomorph_apply
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (c : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (g : padicCayleySpecialOrthogonalSubgroupInverseDomain F p) :
    (padicCayleySpecialOrthogonalLeftTranslateHomeomorph F p c g).1 =
      c * g.1 :=
  rfl

@[simp]
theorem coe_padicCayleySpecialOrthogonalLeftTranslateHomeomorph_symm_apply
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (c : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (g : padicCayleySpecialOrthogonalTranslatedTarget F p c) :
    ((padicCayleySpecialOrthogonalLeftTranslateHomeomorph
      F p c).symm g).1 = c⁻¹ * g.1 :=
  rfl

/-- The translated p-adic Cayley chart from the exact skew-adjoint source to
the exact target around a specified special-orthogonal center. -/
def skewAdjointPadicCayleyTranslatedHomeomorph
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (c : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    Matrix.skewAdjointPadicCayleySource F p ≃ₜ
      padicCayleySpecialOrthogonalTranslatedTarget F p c :=
  (Matrix.skewAdjointPadicCayleyHomeomorphSpecialOrthogonal
      F p hF).trans
    ((padicCayleySpecialOrthogonalSubgroupInverseDomainHomeomorph
      F p).trans
        (padicCayleySpecialOrthogonalLeftTranslateHomeomorph F p c))

/-- The translated Cayley chart has the expected exact forward matrix
formula: left multiplication of the identity-centered Cayley transform. -/
@[simp]
theorem coe_skewAdjointPadicCayleyTranslatedHomeomorph_apply
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (c : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : Matrix.skewAdjointPadicCayleySource F p) :
    (skewAdjointPadicCayleyTranslatedHomeomorph
        F p hF c X).1.1.1.1 =
      c.1.1.1 *
        ((1 + (X.1 : Matrix (Fin n) (Fin n) ℚ_[p])) *
          (1 - (X.1 : Matrix (Fin n) (Fin n) ℚ_[p]))⁻¹) :=
  rfl

/-- The inverse translated chart first multiplies by the inverse center and
then applies the exact inverse Cayley formula. -/
@[simp]
theorem coe_skewAdjointPadicCayleyTranslatedHomeomorph_symm_apply
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (c : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (g : padicCayleySpecialOrthogonalTranslatedTarget F p c) :
    (((skewAdjointPadicCayleyTranslatedHomeomorph
        F p hF c).symm g).1 :
          Matrix (Fin n) (Fin n) ℚ_[p]) =
      ((((c⁻¹ * g.1).1.1.1 :
          Matrix (Fin n) (Fin n) ℚ_[p]) + 1)⁻¹ *
        (((c⁻¹ * g.1).1.1.1 :
          Matrix (Fin n) (Fin n) ℚ_[p]) - 1)) :=
  rfl

end PositiveDefiniteIntegralLattice
