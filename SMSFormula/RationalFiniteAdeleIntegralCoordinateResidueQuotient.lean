import SMSFormula.RationalFiniteAdeleIntegralLatticeFiniteQuotient

/-!
# Coordinate residue models for integral finite-adele quotients

The scalar strong-approximation equivalence
`ZMod m ≃+ Zhat / m Zhat` extends canonically to the coordinate quotient
`Zhat^n / m Zhat^n`.  This file records that extension without choosing a
system of finite-adelic residue representatives.
-/

noncomputable section

open Set

namespace PositiveDefiniteIntegralLattice

/-- The coordinate quotient maps to the product of its scalar quotients by
taking every coordinate. -/
noncomputable def integralFiniteAdeleCoordinateDilationQuotientToPi
    (n m : ℕ) :
    ((Fin n → IntegralFiniteAdele) ⧸
        (integralFiniteAdeleCoordinateNatDilation n m).range) →+
      (Fin n →
        IntegralFiniteAdele ⧸ (integralFiniteAdeleNatDilation m).range) :=
  QuotientAddGroup.lift
    (integralFiniteAdeleCoordinateNatDilation n m).range
    { toFun := fun x i ↦
        (x i : IntegralFiniteAdele ⧸
          (integralFiniteAdeleNatDilation m).range)
      map_zero' := by funext i; rfl
      map_add' := by intro x y; funext i; rfl }
    (by
      rintro x ⟨y, rfl⟩
      funext i
      apply QuotientAddGroup.eq.mpr
      refine ⟨-y i, ?_⟩
      ext
      simp [integralFiniteAdeleCoordinateNatDilation,
        integralFiniteAdeleNatDilation])

@[simp]
theorem integralFiniteAdeleCoordinateDilationQuotientToPi_mk
    (n m : ℕ) (x : Fin n → IntegralFiniteAdele) :
    integralFiniteAdeleCoordinateDilationQuotientToPi n m
        (x : (Fin n → IntegralFiniteAdele) ⧸
          (integralFiniteAdeleCoordinateNatDilation n m).range) =
      fun i ↦
        (x i : IntegralFiniteAdele ⧸
          (integralFiniteAdeleNatDilation m).range) :=
  rfl

theorem integralFiniteAdeleCoordinateDilationQuotientToPi_injective
    (n m : ℕ) :
    Function.Injective
      (integralFiniteAdeleCoordinateDilationQuotientToPi n m) := by
  intro q r hqr
  induction q using Quotient.inductionOn' with
  | _ x =>
      induction r using Quotient.inductionOn' with
      | _ y =>
          apply QuotientAddGroup.eq.mpr
          have hi : ∀ i,
              -(x i) + y i ∈
                (integralFiniteAdeleNatDilation m).range := by
            intro i
            apply QuotientAddGroup.eq.mp
            exact congrFun hqr i
          choose z hz using hi
          refine ⟨z, ?_⟩
          funext i
          exact hz i

theorem integralFiniteAdeleCoordinateDilationQuotientToPi_surjective
    (n m : ℕ) :
    Function.Surjective
      (integralFiniteAdeleCoordinateDilationQuotientToPi n m) := by
  intro q
  choose x hx using fun i ↦ Quotient.exists_rep (q i)
  refine ⟨(x : (Fin n → IntegralFiniteAdele) ⧸
    (integralFiniteAdeleCoordinateNatDilation n m).range), ?_⟩
  funext i
  exact hx i

/-- The coordinate quotient is canonically the product of the scalar
quotients.  Its inverse is obtained from bijectivity of the coordinate map,
not from a section into finite adeles. -/
noncomputable def integralFiniteAdeleCoordinateDilationQuotientEquivPi
    (n m : ℕ) :
    ((Fin n → IntegralFiniteAdele) ⧸
        (integralFiniteAdeleCoordinateNatDilation n m).range) ≃+
      (Fin n →
        IntegralFiniteAdele ⧸ (integralFiniteAdeleNatDilation m).range) :=
  AddEquiv.ofBijective
    (integralFiniteAdeleCoordinateDilationQuotientToPi n m)
    ⟨integralFiniteAdeleCoordinateDilationQuotientToPi_injective n m,
      integralFiniteAdeleCoordinateDilationQuotientToPi_surjective n m⟩

@[simp]
theorem integralFiniteAdeleCoordinateDilationQuotientEquivPi_mk
    (n m : ℕ) (x : Fin n → IntegralFiniteAdele) :
    integralFiniteAdeleCoordinateDilationQuotientEquivPi n m
        (x : (Fin n → IntegralFiniteAdele) ⧸
          (integralFiniteAdeleCoordinateNatDilation n m).range) =
      fun i ↦
        (x i : IntegralFiniteAdele ⧸
          (integralFiniteAdeleNatDilation m).range) :=
  rfl

/-- The exact section-free residue model
`(ZMod m)^n ≃+ Zhat^n / m Zhat^n`. -/
noncomputable def coordinateResidueEquivIntegralFiniteAdeleModDilation
    (n m : ℕ) (hm : m ≠ 0) :
    (Fin n → ZMod m) ≃+
      ((Fin n → IntegralFiniteAdele) ⧸
        (integralFiniteAdeleCoordinateNatDilation n m).range) :=
  (AddEquiv.piCongrRight fun _ : Fin n ↦
      residueEquivIntegralFiniteAdeleModDilation m hm).trans
    (integralFiniteAdeleCoordinateDilationQuotientEquivPi n m).symm

@[simp]
theorem coordinateResidueEquivIntegralFiniteAdeleModDilation_apply_intCast
    (n m : ℕ) (hm : m ≠ 0) (z : Fin n → ℤ) :
    coordinateResidueEquivIntegralFiniteAdeleModDilation n m hm
        (fun i ↦ (z i : ZMod m)) =
      (fun i ↦ integerToIntegralFiniteAdele (z i) :
        (Fin n → IntegralFiniteAdele) ⧸
          (integralFiniteAdeleCoordinateNatDilation n m).range) := by
  apply (integralFiniteAdeleCoordinateDilationQuotientEquivPi n m).injective
  funext i
  rw [integralFiniteAdeleCoordinateDilationQuotientEquivPi_mk]
  simp only [coordinateResidueEquivIntegralFiniteAdeleModDilation,
    AddEquiv.trans_apply, AddEquiv.apply_symm_apply]
  change residueToIntegralFiniteAdeleModDilation m (z i : ZMod m) =
    (integerToIntegralFiniteAdele (z i) :
      IntegralFiniteAdele ⧸ (integralFiniteAdeleNatDilation m).range)
  exact residueToIntegralFiniteAdeleModDilation_intCast m (z i)

end PositiveDefiniteIntegralLattice
