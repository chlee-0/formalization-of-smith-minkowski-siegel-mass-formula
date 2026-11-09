import SMSFormula.QuadraticCartanDieudonneReflectionWord

/-!
# Determinant parity for quadratic reflection words

This file proves that a single certified quadratic reflection has determinant
`-1`, and consequently that the determinant of a reflection word is
`(-1)` raised to its length.  It then extracts even length from determinant
one and packages even words as consecutive reflection pairs.
-/

noncomputable section

open Module
open CliffordAlgebra

namespace CliffordAlgebra

variable {K M : Type*} [Field K]
variable [AddCommGroup M] [Module K M] [FiniteDimensional K M]
variable (Q : QuadraticForm K M)

/-- A quadratic reflection in an anisotropic vector has determinant `-1` in
arbitrary finite dimension. -/
theorem quadraticReflectionOfNeZero_det (v : M) (hv : Q v ≠ 0) :
    LinearMap.det (quadraticReflectionOfNeZero Q v hv).toLinearMap = -1 := by
  let b := Module.finBasis K M
  let e := b.equivFun
  let a : Fin (finrank K M) → K := e v
  let f : Module.Dual K (Fin (finrank K M) → K) :=
    (Q v)⁻¹ • (Q.polarBilin v).comp e.symm.toLinearMap
  have hf : f a = 2 := by
    dsimp only [f, a]
    rw [LinearMap.smul_apply, LinearMap.comp_apply]
    change (Q v)⁻¹ • Q.polarBilin v (e.symm (e v)) = 2
    rw [e.symm_apply_apply,
      QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self]
    simp only [nsmul_eq_mul, smul_eq_mul]
    field_simp
    norm_num
  have hconj :
      e.toLinearMap ∘ₗ (quadraticReflectionOfNeZero Q v hv).toLinearMap ∘ₗ
          e.symm.toLinearMap =
        LinearMap.id - f.smulRight a := by
    apply LinearMap.ext
    intro z
    change e (quadraticReflectionOfNeZero Q v hv (e.symm z)) =
      z - ((Q v)⁻¹ * QuadraticMap.polar Q v (e.symm z)) • e v
    rw [quadraticReflectionOfNeZero_apply]
    rw [map_sub, map_smul, e.apply_symm_apply]
  have hmatrix := Matrix.det_toMatrix'_reflection_of_apply_eq_two a f hf
  rw [LinearMap.det_toMatrix'] at hmatrix
  calc
    LinearMap.det (quadraticReflectionOfNeZero Q v hv).toLinearMap =
        LinearMap.det
          (e.toLinearMap ∘ₗ
            (quadraticReflectionOfNeZero Q v hv).toLinearMap ∘ₗ
              e.symm.toLinearMap) :=
      (LinearMap.det_conj
        (quadraticReflectionOfNeZero Q v hv).toLinearMap e).symm
    _ = LinearMap.det (LinearMap.id - f.smulRight a) := by rw [hconj]
    _ = -1 := hmatrix

end CliffordAlgebra

namespace QuadraticMap.ReflectionWord

variable {K M : Type*} [Field K]
variable [AddCommGroup M] [Module K M] [FiniteDimensional K M]
variable (Q : QuadraticForm K M)

/-- The determinant of a reflection word is the sign determined by its
length. -/
theorem det_eval (xs : Q.ReflectionWord) :
    LinearMap.det (eval Q xs).toLinearEquiv.toLinearMap =
      (-1 : K) ^ xs.length := by
  induction xs with
  | nil =>
      simpa only [eval_nil, QuadraticMap.IsometryEquiv.refl,
        LinearEquiv.refl_toLinearMap, List.length_nil, pow_zero] using
        (LinearMap.det_id (M := M) (A := K))
  | cons x xs ih =>
      change LinearMap.det
          ((eval Q xs).toLinearEquiv.toLinearMap ∘ₗ
            (quadraticReflectionOfNeZero Q x x.property).toLinearMap) =
        (-1 : K) ^ (xs.length + 1)
      rw [LinearMap.det_comp, ih,
        CliffordAlgebra.quadraticReflectionOfNeZero_det]
      rw [pow_succ]

/-- Determinant one forces every representing reflection word to have even
length. -/
theorem even_length_of_det_eval_eq_one (xs : Q.ReflectionWord)
    [CharZero K]
    (hdet : LinearMap.det (eval Q xs).toLinearEquiv.toLinearMap = 1) :
    Even xs.length := by
  apply (neg_one_pow_eq_one_iff_even (R := K) (by norm_num)).mp
  calc
    (-1 : K) ^ xs.length =
        LinearMap.det (eval Q xs).toLinearEquiv.toLinearMap :=
      (det_eval Q xs).symm
    _ = 1 := hdet

/-- A consecutive pair of certified anisotropic reflection vectors. -/
abbrev ReflectionPair := Q.AnisotropicVector × Q.AnisotropicVector

/-- Flatten a list of consecutive reflection pairs to its reflection word. -/
def flattenPairs : List (ReflectionPair Q) → Q.ReflectionWord :=
  List.flatMap fun p => [p.1, p.2]

omit [FiniteDimensional K M] in
@[simp]
theorem flattenPairs_nil : flattenPairs Q [] = [] :=
  rfl

omit [FiniteDimensional K M] in
@[simp]
theorem flattenPairs_cons (p : ReflectionPair Q) (ps : List (ReflectionPair Q)) :
    flattenPairs Q (p :: ps) = p.1 :: p.2 :: flattenPairs Q ps :=
  rfl

omit [FiniteDimensional K M] in
@[simp]
theorem eval_pair_apply (p : ReflectionPair Q) (m : M) :
    eval Q [p.1, p.2] m =
      quadraticReflectionOfNeZero Q p.2 p.2.property
        (quadraticReflectionOfNeZero Q p.1 p.1.property m) :=
  rfl

omit [FiniteDimensional K M] in
@[simp]
theorem length_flattenPairs (ps : List (ReflectionPair Q)) :
    (flattenPairs Q ps).length = 2 * ps.length := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      simp only [flattenPairs_cons, List.length_cons, ih]
      omega

/-- Every even reflection word is uniquely unnecessary but existentially
sufficiently a flattening of consecutive pairs. -/
theorem exists_pairs_flatten_eq
    {K' M' : Type*} [Field K'] [AddCommGroup M'] [Module K' M']
    (Q' : QuadraticForm K' M') (xs' : Q'.ReflectionWord)
    (heven : Even xs'.length) :
    ∃ ps : List (ReflectionPair Q'), flattenPairs Q' ps = xs' := by
  cases xs' with
  | nil => exact ⟨[], rfl⟩
  | cons x xs =>
      cases xs with
      | nil =>
          exfalso
          simp only [List.length_cons, List.length_nil] at heven
          exact Nat.not_even_one heven
      | cons y ys =>
          have hys : Even ys.length := by
            rcases heven with ⟨k, hk⟩
            refine ⟨k - 1, ?_⟩
            simp only [List.length_cons] at hk
            omega
          obtain ⟨ps, hps⟩ := exists_pairs_flatten_eq Q' ys hys
          exact ⟨(x, y) :: ps, by simp [hps]⟩

/-- A determinant-one isometry of a nondegenerate finite-dimensional form is
represented by consecutive reflection pairs.  The number of pairs is at most
the ambient finrank. -/
theorem exists_reflectionPairs_eval_eq
    [CharZero K]
    (hQ : Q.associated.Nondegenerate) (g : Q.IsometryEquiv Q)
    (hdet : LinearMap.det g.toLinearEquiv.toLinearMap = 1) :
    ∃ ps : List (ReflectionPair Q),
      eval Q (flattenPairs Q ps) = g ∧ ps.length ≤ finrank K M := by
  obtain ⟨xs, hxs, hlen⟩ := exists_reflectionWord_eval_eq Q hQ g
  have hdetxs : LinearMap.det (eval Q xs).toLinearEquiv.toLinearMap = 1 := by
    rw [hxs]
    exact hdet
  obtain ⟨ps, hps⟩ := exists_pairs_flatten_eq Q xs
    (even_length_of_det_eval_eq_one Q xs hdetxs)
  refine ⟨ps, ?_, ?_⟩
  · rw [hps, hxs]
  · have hpairlen := length_flattenPairs Q ps
    rw [hps] at hpairlen
    omega

end QuadraticMap.ReflectionWord
