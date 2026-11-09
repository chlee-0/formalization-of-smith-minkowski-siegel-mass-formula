import SMSFormula.QuadraticReflectionPairCliffordSpinorNorm

/-!
# The spinor norm on determinant-one quadratic isometries

This file packages determinant-one self-isometries of a finite-dimensional
quadratic form as a group.  Since `QuadraticMap.IsometryEquiv.trans` composes
left-to-right, the group product of `g` and `h` is `h.trans g`; this is the
usual right-to-left convention for automorphism groups.

A bounded reflection-pair presentation is chosen for each element.  The
completed Clifford factorization-independence theorem makes the associated
square class independent of this choice.  Appending pair presentations then
proves the identity and multiplication laws and bundles the result as a
group homomorphism.

No kernel, continuity, local measure, or Tamagawa statement is made here.
-/

noncomputable section

open Module

namespace QuadraticMap.ReflectionWord

variable {K M : Type*} [Field K]
variable [AddCommGroup M] [Module K M] [FiniteDimensional K M]
variable (Q : QuadraticForm K M)

/-- The group of determinant-one self-isometries of `Q`.

The product is reversed relative to `IsometryEquiv.trans`, so it agrees with
the standard composition convention for linear automorphisms and matrices. -/
def DetOneIsometryGroup :=
  {g : Q.IsometryEquiv Q // LinearEquiv.det g.toLinearEquiv = 1}

instance : Group (DetOneIsometryGroup Q) where
  one := ⟨.refl Q, by
    change LinearEquiv.det (LinearEquiv.refl K M) = 1
    exact map_one LinearEquiv.det⟩
  mul g h := ⟨h.1.trans g.1, by
    rw [show (h.1.trans g.1).toLinearEquiv =
      h.1.toLinearEquiv.trans g.1.toLinearEquiv by rfl,
      LinearEquiv.det_trans, g.2, h.2, mul_one]⟩
  inv g := ⟨g.1.symm, by
    change LinearEquiv.det g.1.toLinearEquiv.symm = 1
    rw [LinearEquiv.det_symm, map_inv, g.2, inv_one]⟩
  mul_assoc a b c := by
    apply Subtype.ext
    apply DFunLike.coe_injective
    funext x
    rfl
  one_mul a := by
    apply Subtype.ext
    apply DFunLike.coe_injective
    funext x
    rfl
  mul_one a := by
    apply Subtype.ext
    apply DFunLike.coe_injective
    funext x
    rfl
  inv_mul_cancel a := by
    apply Subtype.ext
    apply DFunLike.coe_injective
    funext x
    exact a.1.toLinearEquiv.symm_apply_apply x

omit [FiniteDimensional K M] in
@[simp]
theorem detOneIsometryGroup_det (g : DetOneIsometryGroup Q) :
    LinearMap.det g.1.toLinearEquiv.toLinearMap = 1 := by
  simpa only [LinearEquiv.coe_det, Units.val_one] using congrArg Units.val g.2

omit [FiniteDimensional K M] in
@[simp]
theorem detOneIsometryGroup_mul_val (g h : DetOneIsometryGroup Q) :
    (g * h).1 = h.1.trans g.1 := rfl

omit [FiniteDimensional K M] in
theorem reflectionPairSquareClassProduct_append
    (ps qs : List (ReflectionPair Q)) :
    reflectionPairSquareClassProduct Q (ps ++ qs) =
      reflectionPairSquareClassProduct Q ps *
        reflectionPairSquareClassProduct Q qs := by
  simp [reflectionPairSquareClassProduct]

omit [FiniteDimensional K M] in
theorem flattenPairs_append (ps qs : List (ReflectionPair Q)) :
    flattenPairs Q (ps ++ qs) =
      flattenPairs Q ps ++ flattenPairs Q qs := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [ih]

variable [CharZero K]

/-- A bounded reflection-pair presentation chosen for a determinant-one
self-isometry. -/
noncomputable def chosenDetOneReflectionPairs
    (hQ : Q.associated.Nondegenerate) (g : DetOneIsometryGroup Q) :
    List (ReflectionPair Q) :=
  Classical.choose (exists_reflectionPairs_eval_eq Q hQ g.1
    (detOneIsometryGroup_det Q g))

theorem eval_chosenDetOneReflectionPairs
    (hQ : Q.associated.Nondegenerate) (g : DetOneIsometryGroup Q) :
    eval Q (flattenPairs Q (chosenDetOneReflectionPairs Q hQ g)) = g.1 :=
  (Classical.choose_spec (exists_reflectionPairs_eval_eq Q hQ g.1
    (detOneIsometryGroup_det Q g))).1

theorem length_chosenDetOneReflectionPairs_le
    (hQ : Q.associated.Nondegenerate) (g : DetOneIsometryGroup Q) :
    (chosenDetOneReflectionPairs Q hQ g).length ≤ finrank K M :=
  (Classical.choose_spec (exists_reflectionPairs_eval_eq Q hQ g.1
    (detOneIsometryGroup_det Q g))).2

/-- The presentation-level determinant-one spinor norm. -/
noncomputable def determinantOneSpinorNorm
    (hQ : Q.associated.Nondegenerate) (g : DetOneIsometryGroup Q) :
    Rat.SquareClass K :=
  reflectionPairSquareClassProduct Q (chosenDetOneReflectionPairs Q hQ g)

/-- The determinant-one spinor norm agrees with every reflection-pair
presentation, not only the chosen one. -/
theorem determinantOneSpinorNorm_eq_reflectionPairSquareClassProduct
    (hQ : Q.associated.Nondegenerate) (g : DetOneIsometryGroup Q)
    (ps : List (ReflectionPair Q))
    (hps : eval Q (flattenPairs Q ps) = g.1) :
    determinantOneSpinorNorm Q hQ g =
      reflectionPairSquareClassProduct Q ps := by
  exact reflectionPairSpinorNormFactorizationIndependent Q hQ _ _
    ((eval_chosenDetOneReflectionPairs Q hQ g).trans hps.symm)

@[simp]
theorem determinantOneSpinorNorm_one
    (hQ : Q.associated.Nondegenerate) :
    determinantOneSpinorNorm Q hQ 1 = 1 := by
  rw [determinantOneSpinorNorm_eq_reflectionPairSquareClassProduct
    Q hQ 1 []]
  · rfl
  · rfl

theorem determinantOneSpinorNorm_mul
    (hQ : Q.associated.Nondegenerate) (g h : DetOneIsometryGroup Q) :
    determinantOneSpinorNorm Q hQ (g * h) =
      determinantOneSpinorNorm Q hQ g * determinantOneSpinorNorm Q hQ h := by
  rw [determinantOneSpinorNorm_eq_reflectionPairSquareClassProduct Q hQ
    (g * h) (chosenDetOneReflectionPairs Q hQ h ++
      chosenDetOneReflectionPairs Q hQ g)]
  · rw [reflectionPairSquareClassProduct_append, mul_comm]
    rfl
  · rw [flattenPairs_append, eval_append,
      eval_chosenDetOneReflectionPairs, eval_chosenDetOneReflectionPairs]
    rfl

/-- The determinant-one spinor norm as a group homomorphism to square
classes. -/
noncomputable def determinantOneSpinorNormHom
    (hQ : Q.associated.Nondegenerate) :
    DetOneIsometryGroup Q →* Rat.SquareClass K where
  toFun := determinantOneSpinorNorm Q hQ
  map_one' := determinantOneSpinorNorm_one Q hQ
  map_mul' := determinantOneSpinorNorm_mul Q hQ

/-- Every value of the determinant-one spinor norm is computed by a
reflection-pair presentation of bounded length. -/
theorem exists_bounded_reflectionPairs_determinantOneSpinorNorm_eq
    (hQ : Q.associated.Nondegenerate) (g : DetOneIsometryGroup Q) :
    ∃ ps : List (ReflectionPair Q),
      eval Q (flattenPairs Q ps) = g.1 ∧
        ps.length ≤ finrank K M ∧
          determinantOneSpinorNormHom Q hQ g =
            reflectionPairSquareClassProduct Q ps := by
  exact ⟨chosenDetOneReflectionPairs Q hQ g,
    eval_chosenDetOneReflectionPairs Q hQ g,
    length_chosenDetOneReflectionPairs_le Q hQ g, rfl⟩

end QuadraticMap.ReflectionWord
