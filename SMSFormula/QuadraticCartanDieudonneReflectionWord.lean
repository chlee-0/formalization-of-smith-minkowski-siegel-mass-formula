import SMSFormula.QuadraticCartanDieudonneOrthogonal

/-!
# Reflection words for quadratic Cartan--Dieudonne

This file packages finite lists of anisotropic reflection vectors and their
evaluated quadratic isometries.  It also proves the compatibility needed for
dimension induction: a reflection word in the orthogonal complement of an
anisotropic line lifts to the ambient quadratic space, fixes the distinguished
vector, and restricts to the original word.
-/

noncomputable section

open Module
open CliffordAlgebra

namespace QuadraticMap

variable {K M : Type*} [Field K] [CharZero K]
variable [AddCommGroup M] [Module K M]
variable (Q : QuadraticForm K M)

/-- An anisotropic vector, carrying the nonvanishing certificate needed to
define its quadratic reflection over a field. -/
abbrev AnisotropicVector := {x : M // Q x ≠ 0}

/-- A finite word in anisotropic quadratic reflections. -/
abbrev ReflectionWord := List (Q.AnisotropicVector)

namespace ReflectionWord

/-- Evaluate a reflection word from left to right. -/
def eval : Q.ReflectionWord → Q.IsometryEquiv Q
  | [] => .refl Q
  | x :: xs =>
      (quadraticReflectionIsometryEquivOfNeZero Q x x.property).trans
        (eval xs)

omit [CharZero K] in
@[simp]
theorem eval_nil : eval Q [] = .refl Q :=
  rfl

omit [CharZero K] in
@[simp]
theorem eval_cons (x : Q.AnisotropicVector) (xs : Q.ReflectionWord) :
    eval Q (x :: xs) =
      (quadraticReflectionIsometryEquivOfNeZero Q x x.property).trans
        (eval Q xs) :=
  rfl

omit [CharZero K] in
@[simp]
theorem eval_cons_apply (x : Q.AnisotropicVector) (xs : Q.ReflectionWord)
    (m : M) :
    eval Q (x :: xs) m =
      eval Q xs (quadraticReflectionOfNeZero Q x x.property m) :=
  rfl

omit [CharZero K] in
theorem eval_append (xs ys : Q.ReflectionWord) :
    eval Q (xs ++ ys) = (eval Q xs).trans (eval Q ys) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.cons_append, eval_cons, ih]
      apply DFunLike.coe_injective
      funext m
      rfl

/-- Regard a reflection word in an anisotropic orthogonal complement as a
word in the ambient quadratic space. -/
def liftOrthogonal (x : M) :
    (Q.orthogonalRestriction x).ReflectionWord → Q.ReflectionWord :=
  List.map fun y => ⟨(y : M), y.property⟩

@[simp]
theorem length_liftOrthogonal (x : M)
    (xs : (Q.orthogonalRestriction x).ReflectionWord) :
    (liftOrthogonal Q x xs).length = xs.length := by
  simp [liftOrthogonal]

theorem quadraticReflection_liftOrthogonal_apply_distinguished
    (x : M) (y : (Q.orthogonalRestriction x).AnisotropicVector) :
    quadraticReflectionOfNeZero Q (y : M) y.property x = x := by
  rw [quadraticReflectionOfNeZero_apply]
  have hxy : Q.associated x (y : M) = 0 :=
    Q.mem_anisotropicOrthogonal_iff.mp y.val.property
  have hyx : Q.associated (y : M) x = 0 := by
    rw [QuadraticMap.associated_isSymm K Q (y : M) x]
    exact hxy
  have hpolar : QuadraticMap.polar Q (y : M) x = 0 := by
    have hmaps : 2 • Q.associated = Q.polarBilin :=
      Q.two_nsmul_associated (S := K)
    have happ := congrArg
      (fun B : LinearMap.BilinMap K M K => B (y : M) x) hmaps
    calc
      QuadraticMap.polar Q (y : M) x = Q.polarBilin (y : M) x := rfl
      _ = (2 • Q.associated) (y : M) x := happ.symm
      _ = 0 := by
        change (2 : ℕ) • Q.associated (y : M) x = 0
        rw [hyx, nsmul_zero]
  rw [hpolar, mul_zero, zero_smul, sub_zero]

theorem quadraticReflection_liftOrthogonal_apply
    (x : M) (y : (Q.orthogonalRestriction x).AnisotropicVector)
    (z : Q.anisotropicOrthogonal x) :
    quadraticReflectionOfNeZero Q (y : M) y.property (z : M) =
      (quadraticReflectionOfNeZero (Q.orthogonalRestriction x) y y.property z : M) := by
  rw [quadraticReflectionOfNeZero_apply,
    quadraticReflectionOfNeZero_apply]
  rfl

theorem eval_liftOrthogonal_apply_distinguished (x : M)
    (xs : (Q.orthogonalRestriction x).ReflectionWord) :
    eval Q (liftOrthogonal Q x xs) x = x := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
      rw [liftOrthogonal, List.map_cons, eval_cons_apply,
        quadraticReflection_liftOrthogonal_apply_distinguished]
      exact ih

theorem eval_liftOrthogonal_apply (x : M)
    (xs : (Q.orthogonalRestriction x).ReflectionWord)
    (z : Q.anisotropicOrthogonal x) :
    eval Q (liftOrthogonal Q x xs) (z : M) =
      (eval (Q.orthogonalRestriction x) xs z : M) := by
  induction xs generalizing z with
  | nil => rfl
  | cons y ys ih =>
      rw [liftOrthogonal, List.map_cons, eval_cons_apply,
        quadraticReflection_liftOrthogonal_apply]
      exact ih (quadraticReflectionOfNeZero
        (Q.orthogonalRestriction x) y y.property z)

theorem eval_liftOrthogonal_eq_of_fixed_of_restrict_eq
    (x : M) (hx : Q x ≠ 0)
    (g : Q.IsometryEquiv Q) (hfix : g x = x)
    (xs : (Q.orthogonalRestriction x).ReflectionWord)
    (heval : eval (Q.orthogonalRestriction x) xs =
      g.restrictIsometryEquivToAnisotropicOrthogonal Q x hfix) :
    eval Q (liftOrthogonal Q x xs) = g := by
  apply DFunLike.coe_injective
  funext m
  obtain ⟨⟨y, z⟩, rfl⟩ := (Q.anisotropicDecompositionEquiv x hx).surjective m
  rw [Q.anisotropicDecompositionEquiv_apply x hx]
  change eval Q (liftOrthogonal Q x xs) ((y : M) + (z : M)) =
    g ((y : M) + (z : M))
  rw [map_add, map_add]
  congr 1
  · obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp y.property
    rw [← ha, map_smul, map_smul,
      eval_liftOrthogonal_apply_distinguished Q x xs, hfix]
  · have hz := congrArg (fun e => (e z : M)) heval
    rw [eval_liftOrthogonal_apply Q]
    exact hz

/-- The reflection word evaluating to the inverse of an alignment
correction.  In the two-reflection case the order is reversed. -/
def inverseAlignmentWord {x y : M}
    (a : ReflectionAlignment Q x y) : Q.ReflectionWord := by
  cases a with
  | one hsub _ =>
      exact [⟨y - x, hsub⟩]
  | two hadd hx _ =>
      exact [⟨x, hx⟩, ⟨y + x, hadd⟩]

omit [CharZero K] in
@[simp]
theorem length_inverseAlignmentWord {x y : M}
    (a : ReflectionAlignment Q x y) :
    (inverseAlignmentWord Q a).length = a.length := by
  cases a <;> rfl

omit [CharZero K] in
theorem eval_inverseAlignmentWord {x y : M}
    (a : ReflectionAlignment Q x y) :
    eval Q (inverseAlignmentWord Q a) = a.correction.symm := by
  cases a <;>
    apply DFunLike.coe_injective <;>
    funext m <;>
    rfl

variable [FiniteDimensional K M]

theorem exists_anisotropic_of_finrank_pos
    (hQ : Q.associated.Nondegenerate) (hpos : 0 < finrank K M) :
    ∃ x : M, Q x ≠ 0 := by
  letI : Nontrivial M := Module.finrank_pos_iff.mp hpos
  have hBne : Q.associated ≠ 0 :=
    LinearMap.BilinForm.Nondegenerate.ne_zero hQ
  obtain ⟨x, hx⟩ := LinearMap.BilinForm.exists_bilinForm_self_ne_zero
    hBne (QuadraticForm.associated_isSymm K Q)
  refine ⟨x, ?_⟩
  rwa [← Q.associated_eq_self_apply ℕ x]

/-- Finite-dimensional Cartan--Dieudonne in certified reflection-word form.
The elementary alignment used here costs at most two reflections per
dimension, giving the sufficient bound `2 * finrank`. -/
theorem exists_reflectionWord_eval_eq
    {K' M' : Type*} [Field K'] [CharZero K']
    [AddCommGroup M'] [Module K' M'] [FiniteDimensional K' M']
    (Q' : QuadraticForm K' M')
    (hQ : Q'.associated.Nondegenerate) (g : Q'.IsometryEquiv Q') :
    ∃ xs : Q'.ReflectionWord,
      eval Q' xs = g ∧ xs.length ≤ 2 * finrank K' M' := by
  by_cases hzero : finrank K' M' = 0
  · letI : Subsingleton M' := Module.finrank_zero_iff.mp hzero
    refine ⟨[], ?_, by simp [hzero]⟩
    apply DFunLike.coe_injective
    funext m
    exact Subsingleton.elim _ _
  · have hpos : 0 < finrank K' M' := Nat.pos_of_ne_zero hzero
    obtain ⟨x, hx⟩ := exists_anisotropic_of_finrank_pos Q' hQ hpos
    let a := g.reflectionAlignmentAt Q' x hx
    let corrected := g.reflectionCorrectionAt Q' x hx
    let restricted := g.reflectionCorrectionAtOrthogonal Q' x hx
    have hQorth : (Q'.orthogonalRestriction x).associated.Nondegenerate :=
      Q'.orthogonalRestriction_associated_nondegenerate hQ x hx
    obtain ⟨ys, hys, hlen⟩ :=
      exists_reflectionWord_eval_eq (Q'.orthogonalRestriction x)
        hQorth restricted
    let lifted := liftOrthogonal Q' x ys
    let tail := inverseAlignmentWord Q' a
    refine ⟨lifted ++ tail, ?_, ?_⟩
    · rw [eval_append, show eval Q' lifted = corrected by
          exact eval_liftOrthogonal_eq_of_fixed_of_restrict_eq Q' x hx corrected
            (g.reflectionCorrectionAt_apply_self Q' x hx) ys hys,
        show eval Q' tail = a.correction.symm by
          exact eval_inverseAlignmentWord Q' a]
      apply DFunLike.coe_injective
      funext m
      exact a.correction.toLinearEquiv.symm_apply_apply (g m)
    · have hdim := Q'.finrank_anisotropicOrthogonal_add_one x hx
      have halen : tail.length ≤ 2 := by
        change (inverseAlignmentWord Q' a).length ≤ 2
        rw [length_inverseAlignmentWord]
        exact a.length_le_two
      rw [List.length_append]
      change (liftOrthogonal Q' x ys).length + tail.length ≤
        2 * finrank K' M'
      rw [length_liftOrthogonal]
      calc
        ys.length + tail.length ≤
            2 * finrank K' (Q'.anisotropicOrthogonal x) + 2 :=
          Nat.add_le_add hlen halen
        _ = 2 * finrank K' M' := by omega
termination_by finrank K' M'
decreasing_by
  have hdim := Q'.finrank_anisotropicOrthogonal_add_one x hx
  omega

end ReflectionWord

end QuadraticMap
