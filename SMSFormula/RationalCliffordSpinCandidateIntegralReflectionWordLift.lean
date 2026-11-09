import SMSFormula.RationalCliffordSpinCandidateIntegralReflectionComplement

/-!
# Lifting recursive integral reflection words

Unit vectors and unit reflections in the recursive orthogonal-complement
carrier lift through its canonical basis to unit vectors and reflections in
the ambient integral form.  This is the conjugacy interface needed to lift a
recursively generated word in the rank induction.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

/-- A unit vector in the recursive complement, regarded as an ambient unit
vector through the canonical complement basis. -/
def LocalPadicIntegralUnimodularForm.liftOrthogonalUnitVector
    {p : ℕ} [Fact p.Prime]
    (U : LocalPadicIntegralUnimodularForm p)
    (x : Fin U.rank → ℤ_[p]) (hx : IsUnit (U.quadraticForm x))
    (y : (U.orthogonalUnimodularForm x hx).UnitVector) : U.UnitVector :=
  ⟨((U.orthogonalBasis x).equivFun.symm y.val : U.orthogonal x), by
    rw [← U.orthogonalUnimodularForm_quadraticForm_apply x hx]
    exact y.property⟩

@[simp]
theorem LocalPadicIntegralUnimodularForm.liftOrthogonalUnitVector_mem
    {p : ℕ} [Fact p.Prime]
    (U : LocalPadicIntegralUnimodularForm p)
    (x : Fin U.rank → ℤ_[p]) (hx : IsUnit (U.quadraticForm x))
    (y : (U.orthogonalUnimodularForm x hx).UnitVector) :
    (U.liftOrthogonalUnitVector x hx y : Fin U.rank → ℤ_[p]) ∈
      U.orthogonal x :=
  ((U.orthogonalBasis x).equivFun.symm y.val).property

@[simp]
theorem LocalPadicIntegralUnimodularForm.quadraticForm_liftOrthogonalUnitVector
    {p : ℕ} [Fact p.Prime]
    (U : LocalPadicIntegralUnimodularForm p)
    (x : Fin U.rank → ℤ_[p]) (hx : IsUnit (U.quadraticForm x))
    (y : (U.orthogonalUnimodularForm x hx).UnitVector) :
    U.quadraticForm (U.liftOrthogonalUnitVector x hx y) =
      (U.orthogonalUnimodularForm x hx).quadraticForm y := by
  simpa [LocalPadicIntegralUnimodularForm.liftOrthogonalUnitVector] using
    (U.orthogonalUnimodularForm_quadraticForm_apply x hx y.val).symm

/-- Polarization in complement coordinates is ambient polarization after
the canonical basis embedding. -/
theorem LocalPadicIntegralUnimodularForm.orthogonalUnimodularForm_polar
    {p : ℕ} [Fact p.Prime]
    (U : LocalPadicIntegralUnimodularForm p)
    (x : Fin U.rank → ℤ_[p]) (hx : IsUnit (U.quadraticForm x))
    (y z : Fin (U.orthogonalUnimodularForm x hx).rank → ℤ_[p]) :
    QuadraticMap.polar (U.orthogonalUnimodularForm x hx).quadraticForm y z =
      QuadraticMap.polar U.quadraticForm
        ((U.orthogonalBasis x).equivFun.symm y : U.orthogonal x)
        ((U.orthogonalBasis x).equivFun.symm z : U.orthogonal x) := by
  rw [QuadraticMap.polar, QuadraticMap.polar]
  rw [U.orthogonalUnimodularForm_quadraticForm_apply,
    U.orthogonalUnimodularForm_quadraticForm_apply,
    U.orthogonalUnimodularForm_quadraticForm_apply]
  have hvalue := congrArg (fun vector : U.orthogonal x ↦ U.quadraticForm vector.1)
    ((U.orthogonalBasis x).equivFun.symm.map_add y z)
  exact congrArg (fun value ↦
    value - U.quadraticForm ((U.orthogonalBasis x).equivFun.symm y) -
      U.quadraticForm ((U.orthogonalBasis x).equivFun.symm z)) hvalue

/-- Every lifted complement reflection fixes the distinguished unit line. -/
theorem LocalPadicIntegralUnimodularForm.unitReflection_liftOrthogonal_apply_distinguished
    {p : ℕ} [Fact p.Prime]
    (U : LocalPadicIntegralUnimodularForm p)
    (x : Fin U.rank → ℤ_[p]) (hx : IsUnit (U.quadraticForm x))
    (y : (U.orthogonalUnimodularForm x hx).UnitVector) :
    U.unitReflection (U.liftOrthogonalUnitVector x hx y) x = x := by
  letI : Invertible (U.quadraticForm (U.liftOrthogonalUnitVector x hx y)) :=
    (U.liftOrthogonalUnitVector x hx y).property.invertible
  rw [LocalPadicIntegralUnimodularForm.unitReflection,
    CliffordAlgebra.quadraticReflection_apply]
  have hbilin : U.bilinForm (U.liftOrthogonalUnitVector x hx y) x = 0 := by
    change U.pairingRight x (U.liftOrthogonalUnitVector x hx y) = 0
    exact U.liftOrthogonalUnitVector_mem x hx y
  rw [U.polar_eq_two_mul_bilinForm, hbilin, mul_zero, mul_zero,
    zero_smul, sub_zero]

/-- An ambient reflection in a lifted complement vector is the conjugate of
the recursive complement reflection through the canonical basis. -/
theorem LocalPadicIntegralUnimodularForm.unitReflection_liftOrthogonal_apply
    {p : ℕ} [Fact p.Prime]
    (U : LocalPadicIntegralUnimodularForm p)
    (x : Fin U.rank → ℤ_[p]) (hx : IsUnit (U.quadraticForm x))
    (y : (U.orthogonalUnimodularForm x hx).UnitVector)
    (z : Fin (U.orthogonalUnimodularForm x hx).rank → ℤ_[p]) :
    U.unitReflection (U.liftOrthogonalUnitVector x hx y)
        ((U.orthogonalBasis x).equivFun.symm z : U.orthogonal x) =
      ((U.orthogonalBasis x).equivFun.symm
        ((U.orthogonalUnimodularForm x hx).unitReflection y z) :
          U.orthogonal x) := by
  let V := U.orthogonalUnimodularForm x hx
  letI : Invertible (U.quadraticForm (U.liftOrthogonalUnitVector x hx y)) :=
    (U.liftOrthogonalUnitVector x hx y).property.invertible
  letI : Invertible (V.quadraticForm y) := y.property.invertible
  rw [LocalPadicIntegralUnimodularForm.unitReflection,
    LocalPadicIntegralUnimodularForm.unitReflection,
    CliffordAlgebra.quadraticReflection_apply,
    CliffordAlgebra.quadraticReflection_apply]
  have hQ :
      U.quadraticForm (U.liftOrthogonalUnitVector x hx y) =
        V.quadraticForm y :=
    U.quadraticForm_liftOrthogonalUnitVector x hx y
  have hpolar :
      QuadraticMap.polar U.quadraticForm
          (U.liftOrthogonalUnitVector x hx y)
          ((U.orthogonalBasis x).equivFun.symm z : U.orthogonal x) =
        QuadraticMap.polar V.quadraticForm y z := by
    symm
    simpa [V, LocalPadicIntegralUnimodularForm.liftOrthogonalUnitVector] using
      U.orthogonalUnimodularForm_polar x hx y.val z
  have hinv :
      ⅟(U.quadraticForm (U.liftOrthogonalUnitVector x hx y)) =
        ⅟(V.quadraticForm y) := by
    apply invOf_eq_right_inv
    rw [hQ, mul_invOf_self]
  rw [hinv, hpolar]
  let a : ℤ_[p] := ⅟(V.quadraticForm y) *
    QuadraticMap.polar V.quadraticForm y z
  have hcoord :
      (U.orthogonalBasis x).equivFun.symm
          (z - a • y.val) =
        (U.orthogonalBasis x).equivFun.symm z -
          a • (U.orthogonalBasis x).equivFun.symm y.val := by
    have hsmul := (U.orthogonalBasis x).equivFun.symm.map_smul a y.val
    exact ((U.orthogonalBasis x).equivFun.symm.map_sub z (a • y.val)).trans
      (congrArg (fun vector : U.orthogonal x ↦
        (U.orthogonalBasis x).equivFun.symm z - vector) hsmul)
  dsimp only [a, V,
    LocalPadicIntegralUnimodularForm.liftOrthogonalUnitVector]
  change
    (((U.orthogonalBasis x).equivFun.symm z : U.orthogonal x) :
        Fin U.rank → ℤ_[p]) -
      a • (((U.orthogonalBasis x).equivFun.symm y.val : U.orthogonal x) :
        Fin U.rank → ℤ_[p]) =
    (((U.orthogonalBasis x).equivFun.symm
      (z - a • y.val) : U.orthogonal x) : Fin U.rank → ℤ_[p])
  rw [hcoord]
  rfl

/-- The coordinate restriction of one lifted ambient reflection is exactly
the corresponding recursive complement reflection. -/
theorem LocalPadicIntegralUnimodularForm.orthogonalCoordinateRestriction_unitReflection
    {p : ℕ} [Fact p.Prime]
    (U : LocalPadicIntegralUnimodularForm p) (hpodd : p ≠ 2)
    (x : Fin U.rank → ℤ_[p]) (hx : IsUnit (U.quadraticForm x))
    (y : (U.orthogonalUnimodularForm x hx).UnitVector) :
    U.orthogonalCoordinateRestriction hpodd x hx
        (U.unitReflectionIsometry (U.liftOrthogonalUnitVector x hx y))
        (U.unitReflection_liftOrthogonal_apply_distinguished x hx y) =
      (U.orthogonalUnimodularForm x hx).unitReflectionIsometry y := by
  apply DFunLike.coe_injective
  funext z
  change (U.orthogonalBasis x).equivFun
      (U.orthogonalRestriction hpodd x
      (U.unitReflectionIsometry (U.liftOrthogonalUnitVector x hx y))
      (U.unitReflection_liftOrthogonal_apply_distinguished x hx y)
      ((U.orthogonalBasis x).equivFun.symm z)) =
    (U.orthogonalUnimodularForm x hx).unitReflection y z
  apply (U.orthogonalBasis x).equivFun.symm.injective
  rw [LinearEquiv.symm_apply_apply]
  apply Subtype.ext
  exact U.unitReflection_liftOrthogonal_apply x hx y z

@[simp]
theorem LocalPadicIntegralUnimodularForm.UnitReflectionWord.eval_cons_apply
    {p : ℕ} [Fact p.Prime]
    (U : LocalPadicIntegralUnimodularForm p)
    (y : U.UnitVector) (ys : U.UnitReflectionWord)
    (z : Fin U.rank → ℤ_[p]) :
    LocalPadicIntegralUnimodularForm.UnitReflectionWord.eval U (y :: ys) z =
      LocalPadicIntegralUnimodularForm.UnitReflectionWord.eval U ys
        (U.unitReflection y z) :=
  rfl

/-- Lift a recursive complement reflection word through the canonical
complement basis. -/
def LocalPadicIntegralUnimodularForm.UnitReflectionWord.liftOrthogonal
    {p : ℕ} [Fact p.Prime]
    (U : LocalPadicIntegralUnimodularForm p)
    (x : Fin U.rank → ℤ_[p]) (hx : IsUnit (U.quadraticForm x)) :
    (U.orthogonalUnimodularForm x hx).UnitReflectionWord →
      U.UnitReflectionWord :=
  List.map (U.liftOrthogonalUnitVector x hx)

@[simp]
theorem LocalPadicIntegralUnimodularForm.UnitReflectionWord.length_liftOrthogonal
    {p : ℕ} [Fact p.Prime]
    (U : LocalPadicIntegralUnimodularForm p)
    (x : Fin U.rank → ℤ_[p]) (hx : IsUnit (U.quadraticForm x))
    (ys : (U.orthogonalUnimodularForm x hx).UnitReflectionWord) :
    (LocalPadicIntegralUnimodularForm.UnitReflectionWord.liftOrthogonal
      U x hx ys).length = ys.length := by
  simp [LocalPadicIntegralUnimodularForm.UnitReflectionWord.liftOrthogonal]

/-- A lifted recursive word fixes the distinguished unit vector. -/
theorem LocalPadicIntegralUnimodularForm.UnitReflectionWord.eval_liftOrthogonal_apply_distinguished
    {p : ℕ} [Fact p.Prime]
    (U : LocalPadicIntegralUnimodularForm p)
    (x : Fin U.rank → ℤ_[p]) (hx : IsUnit (U.quadraticForm x))
    (ys : (U.orthogonalUnimodularForm x hx).UnitReflectionWord) :
    LocalPadicIntegralUnimodularForm.UnitReflectionWord.eval U
        (LocalPadicIntegralUnimodularForm.UnitReflectionWord.liftOrthogonal
          U x hx ys) x = x := by
  induction ys with
  | nil => rfl
  | cons y ys ih =>
      rw [LocalPadicIntegralUnimodularForm.UnitReflectionWord.liftOrthogonal,
        List.map_cons,
        LocalPadicIntegralUnimodularForm.UnitReflectionWord.eval_cons_apply,
        U.unitReflection_liftOrthogonal_apply_distinguished]
      exact ih

/-- Evaluation of a lifted word on the complement is evaluation of the
recursive word transported through the canonical basis. -/
theorem LocalPadicIntegralUnimodularForm.UnitReflectionWord.eval_liftOrthogonal_apply
    {p : ℕ} [Fact p.Prime]
    (U : LocalPadicIntegralUnimodularForm p)
    (x : Fin U.rank → ℤ_[p]) (hx : IsUnit (U.quadraticForm x))
    (ys : (U.orthogonalUnimodularForm x hx).UnitReflectionWord)
    (z : Fin (U.orthogonalUnimodularForm x hx).rank → ℤ_[p]) :
    LocalPadicIntegralUnimodularForm.UnitReflectionWord.eval U
        (LocalPadicIntegralUnimodularForm.UnitReflectionWord.liftOrthogonal
          U x hx ys)
        ((U.orthogonalBasis x).equivFun.symm z : U.orthogonal x) =
      ((U.orthogonalBasis x).equivFun.symm
        (LocalPadicIntegralUnimodularForm.UnitReflectionWord.eval
          (U.orthogonalUnimodularForm x hx) ys z) : U.orthogonal x) := by
  induction ys generalizing z with
  | nil => rfl
  | cons y ys ih =>
      rw [LocalPadicIntegralUnimodularForm.UnitReflectionWord.liftOrthogonal,
        List.map_cons,
        LocalPadicIntegralUnimodularForm.UnitReflectionWord.eval_cons_apply,
        U.unitReflection_liftOrthogonal_apply]
      exact ih ((U.orthogonalUnimodularForm x hx).unitReflection y z)

/-- If a recursive word evaluates to the coordinate restriction of a
fixed-vector isometry, its ambient lift evaluates to that isometry. -/
theorem LocalPadicIntegralUnimodularForm.UnitReflectionWord.eval_liftOrthogonal_eq_of_fixed
    {p : ℕ} [Fact p.Prime]
    (U : LocalPadicIntegralUnimodularForm p) (hpodd : p ≠ 2)
    (x : Fin U.rank → ℤ_[p]) (hx : IsUnit (U.quadraticForm x))
    (g : U.quadraticForm.IsometryEquiv U.quadraticForm)
    (hfix : g x = x)
    (ys : (U.orthogonalUnimodularForm x hx).UnitReflectionWord)
    (heval :
      LocalPadicIntegralUnimodularForm.UnitReflectionWord.eval
          (U.orthogonalUnimodularForm x hx) ys =
        U.orthogonalCoordinateRestriction hpodd x hx g hfix) :
    LocalPadicIntegralUnimodularForm.UnitReflectionWord.eval U
        (LocalPadicIntegralUnimodularForm.UnitReflectionWord.liftOrthogonal
          U x hx ys) = g := by
  apply DFunLike.coe_injective
  funext m
  obtain ⟨⟨y, z⟩, rfl⟩ := (U.decompositionEquiv x hx).surjective m
  rw [U.decompositionEquiv_apply]
  change
    LocalPadicIntegralUnimodularForm.UnitReflectionWord.eval U
        (LocalPadicIntegralUnimodularForm.UnitReflectionWord.liftOrthogonal
          U x hx ys) ((y : Fin U.rank → ℤ_[p]) + (z : Fin U.rank → ℤ_[p])) =
      g ((y : Fin U.rank → ℤ_[p]) + (z : Fin U.rank → ℤ_[p]))
  rw [map_add, map_add]
  congr 1
  · obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp y.property
    rw [← ha, map_smul, map_smul,
      LocalPadicIntegralUnimodularForm.UnitReflectionWord.eval_liftOrthogonal_apply_distinguished,
      hfix]
  · have hz :
        LocalPadicIntegralUnimodularForm.UnitReflectionWord.eval
            (U.orthogonalUnimodularForm x hx) ys
            ((U.orthogonalBasis x).equivFun z) =
          U.orthogonalCoordinateRestriction hpodd x hx g hfix
            ((U.orthogonalBasis x).equivFun z) :=
      DFunLike.congr_fun heval ((U.orthogonalBasis x).equivFun z)
    have hlift :=
      LocalPadicIntegralUnimodularForm.UnitReflectionWord.eval_liftOrthogonal_apply
        U x hx ys ((U.orthogonalBasis x).equivFun z)
    rw [hz] at hlift
    have hcoord :
        (U.orthogonalBasis x).equivFun.symm
            (U.orthogonalCoordinateRestriction hpodd x hx g hfix
              ((U.orthogonalBasis x).equivFun z)) =
          U.orthogonalRestriction hpodd x g hfix z := by
      change (U.orthogonalBasis x).equivFun.symm
          ((U.orthogonalBasis x).equivFun
            (U.orthogonalRestriction hpodd x g hfix
              ((U.orthogonalBasis x).equivFun.symm
                ((U.orthogonalBasis x).equivFun z)))) =
        U.orthogonalRestriction hpodd x g hfix z
      simp
    rw [hcoord] at hlift
    simpa using hlift

end PositiveDefiniteIntegralLattice
