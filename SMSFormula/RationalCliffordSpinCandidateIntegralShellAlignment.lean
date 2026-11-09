import SMSFormula.RationalCliffordSpinCandidateIntegralReflectionFieldBridge
import SMSFormula.RationalCliffordSpinCandidateIntegralReflectionWordLift
import SMSFormula.QuadraticCartanDieudonneParity

/-!
# Determinant-one integral alignment of a unit shell vector

At an odd p-adic integral place, two vectors with the same unit quadratic
value are aligned by one or two unit reflections.  When the alignment uses
one reflection, a unit reflection in the orthogonal complement of the source
is prepended.  It fixes the source and makes the word even.  Thus the source
is carried to the target by a literal two-reflection integral word.

This is the local restricted-product input for the finite-adelic block-shell
orbit.  No adelic choice, measure, cutoff, or Fourier statement occurs here.
-/

noncomputable section

open QuadraticMap.ReflectionWord

namespace PositiveDefiniteIntegralLattice

/-- Add a fixed source-complement reflection precisely in the one-reflection
case. -/
def LocalPadicIntegralUnimodularForm.ReflectionAlignment.evenWord
    {p : ℕ} [Fact p.Prime]
    {U : LocalPadicIntegralUnimodularForm p}
    {x y : Fin U.rank → ℤ_[p]}
    (hx : IsUnit (U.quadraticForm x))
    (a : U.ReflectionAlignment x y)
    (c : (U.orthogonalUnimodularForm x hx).UnitVector) :
    U.UnitReflectionWord := by
  cases a with
  | one hsub =>
      exact U.liftOrthogonalUnitVector x hx c :: [⟨y - x, hsub⟩]
  | two hadd hx' =>
      exact [⟨x, hx'⟩, ⟨y + x, hadd⟩]

/-- The determinant-corrected integral word carrying `x` to `y`.  The
orthogonal-complement rank hypothesis is exactly what supplies the extra
reflection when the direct alignment has odd length. -/
def LocalPadicIntegralUnimodularForm.evenAlignmentWord
    {p : ℕ} [Fact p.Prime]
    (U : LocalPadicIntegralUnimodularForm p) (hpodd : p ≠ 2)
    (x y : Fin U.rank → ℤ_[p])
    (hxy : U.quadraticForm y = U.quadraticForm x)
    (hx : IsUnit (U.quadraticForm x))
    [NeZero (U.orthogonalUnimodularForm x hx).rank] :
    U.UnitReflectionWord := by
  exact (U.reflectionAlignment hpodd x y hxy hx).evenWord hx
    (Classical.choice
      ((U.orthogonalUnimodularForm x hx).unitVector_nonempty hpodd))

@[simp]
theorem LocalPadicIntegralUnimodularForm.length_evenAlignmentWord
    {p : ℕ} [Fact p.Prime]
    (U : LocalPadicIntegralUnimodularForm p) (hpodd : p ≠ 2)
    (x y : Fin U.rank → ℤ_[p])
    (hxy : U.quadraticForm y = U.quadraticForm x)
    (hx : IsUnit (U.quadraticForm x))
  [NeZero (U.orthogonalUnimodularForm x hx).rank] :
    (U.evenAlignmentWord hpodd x y hxy hx).length = 2 := by
  simp only [LocalPadicIntegralUnimodularForm.evenAlignmentWord]
  generalize U.reflectionAlignment hpodd x y hxy hx = a
  cases a <;> rfl

theorem LocalPadicIntegralUnimodularForm.even_length_evenAlignmentWord
    {p : ℕ} [Fact p.Prime]
    (U : LocalPadicIntegralUnimodularForm p) (hpodd : p ≠ 2)
    (x y : Fin U.rank → ℤ_[p])
    (hxy : U.quadraticForm y = U.quadraticForm x)
    (hx : IsUnit (U.quadraticForm x))
    [NeZero (U.orthogonalUnimodularForm x hx).rank] :
    Even (U.evenAlignmentWord hpodd x y hxy hx).length := by
  rw [U.length_evenAlignmentWord hpodd x y hxy hx]
  exact even_two

@[simp]
theorem LocalPadicIntegralUnimodularForm.eval_evenAlignmentWord_apply_source
    {p : ℕ} [Fact p.Prime]
    (U : LocalPadicIntegralUnimodularForm p) (hpodd : p ≠ 2)
    (x y : Fin U.rank → ℤ_[p])
    (hxy : U.quadraticForm y = U.quadraticForm x)
    (hx : IsUnit (U.quadraticForm x))
    [NeZero (U.orthogonalUnimodularForm x hx).rank] :
    LocalPadicIntegralUnimodularForm.UnitReflectionWord.eval U
        (U.evenAlignmentWord hpodd x y hxy hx) x = y := by
  simp only [LocalPadicIntegralUnimodularForm.evenAlignmentWord]
  generalize U.reflectionAlignment hpodd x y hxy hx = a
  cases a with
  | one hsub =>
      simp only [LocalPadicIntegralUnimodularForm.ReflectionAlignment.evenWord,
        LocalPadicIntegralUnimodularForm.UnitReflectionWord.eval_cons_apply,
        LocalPadicIntegralUnimodularForm.UnitReflectionWord.eval_nil]
      rw [U.unitReflection_liftOrthogonal_apply_distinguished]
      have halign :
          U.unitReflection ⟨y - x, hsub⟩ y = x :=
        U.unitReflection_sub_map_right x y hxy hsub
      exact (U.unitReflection ⟨y - x, hsub⟩).symm_apply_eq.mpr halign.symm
  | two hadd hx' =>
      simp only [LocalPadicIntegralUnimodularForm.ReflectionAlignment.evenWord,
        LocalPadicIntegralUnimodularForm.UnitReflectionWord.eval_cons_apply,
        LocalPadicIntegralUnimodularForm.UnitReflectionWord.eval_nil]
      have hself : U.unitReflection ⟨x, hx'⟩ x = -x :=
        (U.unitReflection ⟨x, hx'⟩).symm_apply_eq.mpr
          (U.unitReflection_self_map_neg x hx').symm
      rw [hself]
      have halign : U.unitReflection ⟨y + x, hadd⟩ y = -x :=
        U.unitReflection_add_map_right x y hxy hadd
      exact (U.unitReflection ⟨y + x, hadd⟩).symm_apply_eq.mpr halign.symm

end PositiveDefiniteIntegralLattice

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

local instance integralShellAlignmentPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

/-- The determinant-corrected integral alignment remains an exact shell
alignment after passage from `Z_p` to `Q_p`. -/
theorem CliffordSpinCandidateIntegralSpinorRangeGoodPlace.eval_evenAlignmentWordToPadic_apply_source
    {V : RationalQuadraticSpaceMatrix n}
    {v : IsDedekindDomain.HeightOneSpectrum ℤ}
    (P : V.CliffordSpinCandidateIntegralSpinorRangeGoodPlace v)
    (x y : Fin n → ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).1])
    (hxy : P.unimodularForm.quadraticForm y =
      P.unimodularForm.quadraticForm x)
    (hx : IsUnit (P.unimodularForm.quadraticForm x))
    [NeZero (P.unimodularForm.orthogonalUnimodularForm x hx).rank] :
    eval (V.commutativeScalarExtensionQuadraticForm
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])
        (P.unitReflectionWordToPadic
          (P.unimodularForm.evenAlignmentWord P.prime_ne_two x y hxy hx))
        (fun i ↦ (x i : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])) =
      fun i ↦ (y i : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) := by
  rw [P.eval_unitReflectionWordToPadic_apply]
  rw [P.unimodularForm.eval_evenAlignmentWord_apply_source]
  rfl

/-- The cast determinant-corrected shell word is literally a list of
reflection pairs. -/
theorem CliffordSpinCandidateIntegralSpinorRangeGoodPlace.exists_reflectionPairs_flatten_eq_evenAlignmentWordToPadic
    {V : RationalQuadraticSpaceMatrix n}
    {v : IsDedekindDomain.HeightOneSpectrum ℤ}
    (P : V.CliffordSpinCandidateIntegralSpinorRangeGoodPlace v)
    (x y : Fin n → ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).1])
    (hxy : P.unimodularForm.quadraticForm y =
      P.unimodularForm.quadraticForm x)
    (hx : IsUnit (P.unimodularForm.quadraticForm x))
    [NeZero (P.unimodularForm.orthogonalUnimodularForm x hx).rank] :
    ∃ ps : List (QuadraticMap.ReflectionWord.ReflectionPair
        (V.commutativeScalarExtensionQuadraticForm
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])),
      flattenPairs
          (V.commutativeScalarExtensionQuadraticForm
            ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) ps =
        P.unitReflectionWordToPadic
          (P.unimodularForm.evenAlignmentWord P.prime_ne_two x y hxy hx) := by
  apply exists_pairs_flatten_eq
  rw [P.length_unitReflectionWordToPadic]
  exact P.unimodularForm.even_length_evenAlignmentWord
    P.prime_ne_two x y hxy hx

end RationalQuadraticSpaceMatrix
