import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-!
# Naturality of contraction, change of form and the exterior isomorphism under isometries

For a linear map `f : M → N` that is an isometry `Q_M → Q_N`, Mathlib's algebra map
`CliffordAlgebra.map f` intertwines

* left contraction: `d ⌋ map f x = map f ((d ∘ f) ⌋ x)`;
* change of form, when the two bilinear forms are compatible, `B_N (f x) (f y) = B_M x y`, and
  `f` is also an isometry for the changed forms;
* hence the existing exterior-algebra isomorphism `equivExterior`, whose bilinear form is minus
  the associated form, which every isometry preserves.

These are general Clifford-algebra facts, proved by the left induction; nothing is chosen.
-/

noncomputable section

open LinearMap (BilinForm)

namespace CliffordAlgebra

variable {R : Type*} [CommRing R]
variable {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- Left contraction is natural under the algebra map of an isometry. -/
theorem contractLeft_map {Q₁ : QuadraticForm R M} {Q₂ : QuadraticForm R N} (f : Q₁ →qᵢ Q₂)
    (d : Module.Dual R N) (x : CliffordAlgebra Q₁) :
    contractLeft d (map f x) = map f (contractLeft (d ∘ₗ f.toLinearMap) x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp only [AlgHom.commutes, contractLeft_algebraMap, map_zero]
  | add _ _ hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]
  | ι_mul x m hx =>
    rw [map_mul, map_apply_ι, contractLeft_ι_mul, contractLeft_ι_mul, hx, map_sub, map_smul,
      map_mul, map_apply_ι]
    rfl

/-- Change of form is natural under a map that is an isometry for both pairs of forms and carries
the source change-of-form bilinear form to the target one. -/
theorem changeForm_map {Q₁ Q₁' : QuadraticForm R M} {Q₂ Q₂' : QuadraticForm R N}
    {B₁ : BilinForm R M} {B₂ : BilinForm R N} (h₁ : B₁.toQuadraticMap = Q₁' - Q₁)
    (h₂ : B₂.toQuadraticMap = Q₂' - Q₂) (f : Q₁ →qᵢ Q₂) (f' : Q₁' →qᵢ Q₂')
    (hff' : f.toLinearMap = f'.toLinearMap)
    (hB : ∀ x y, B₂ (f x) (f y) = B₁ x y) (x : CliffordAlgebra Q₁) :
    changeForm h₂ (map f x) = map f' (changeForm h₁ x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp only [AlgHom.commutes, changeForm_algebraMap]
  | add _ _ hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]
  | ι_mul x m hx =>
    rw [map_mul, map_apply_ι, changeForm_ι_mul, changeForm_ι_mul, hx, map_sub, map_mul,
      map_apply_ι, contractLeft_map]
    have hm : f m = f' m := congrArg (fun g : M →ₗ[R] N ↦ g m) hff'
    have hd : B₂ (f' m) ∘ₗ f'.toLinearMap = B₁ m := by
      ext y
      change B₂ (f' m) (f' y) = B₁ m y
      rw [← hm, show f' y = f y from (congrArg (fun g : M →ₗ[R] N ↦ g y) hff').symm]
      exact hB m y
    rw [hm, hd]

section Exterior

variable [Invertible (2 : R)]

/-- An isometry preserves the associated bilinear form. -/
theorem associated_isometry {Q₁ : QuadraticForm R M} {Q₂ : QuadraticForm R N} (f : Q₁ →qᵢ Q₂)
    (x y : M) :
    QuadraticMap.associated Q₂ (f x) (f y) = QuadraticMap.associated Q₁ x y := by
  simp only [QuadraticMap.associated_apply, ← map_add, f.map_app]

/-- The underlying linear map of an isometry is an isometry of the zero forms. -/
def zeroFormIsometry {Q₁ : QuadraticForm R M} {Q₂ : QuadraticForm R N} (f : Q₁ →qᵢ Q₂) :
    (0 : QuadraticForm R M) →qᵢ (0 : QuadraticForm R N) where
  toLinearMap := f.toLinearMap
  map_app' _ := rfl

/-- The exterior isomorphism is natural: `equivExterior Q_N ∘ map f = map f₀ ∘ equivExterior Q_M`
with `f₀` the same linear map viewed as an isometry of the zero forms. -/
theorem equivExterior_map {Q₁ : QuadraticForm R M} {Q₂ : QuadraticForm R N} (f : Q₁ →qᵢ Q₂)
    (x : CliffordAlgebra Q₁) :
    equivExterior Q₂ (map f x) = map (zeroFormIsometry f) (equivExterior Q₁ x) := by
  simp only [equivExterior, changeFormEquiv, LinearEquiv.coe_mk]
  refine changeForm_map changeForm.associated_neg_proof changeForm.associated_neg_proof f
    (zeroFormIsometry f) rfl (fun x y ↦ ?_) x
  rw [map_neg, map_neg, LinearMap.neg_apply, LinearMap.neg_apply, LinearMap.neg_apply,
    LinearMap.neg_apply, associated_isometry]

/-- The same naturality with Mathlib's `ExteriorAlgebra.map`, which is the zero-form algebra
map of the underlying linear map. -/
theorem equivExterior_map_eq_exteriorMap {Q₁ : QuadraticForm R M} {Q₂ : QuadraticForm R N}
    (f : Q₁ →qᵢ Q₂) (x : CliffordAlgebra Q₁) :
    equivExterior Q₂ (map f x) = ExteriorAlgebra.map f.toLinearMap (equivExterior Q₁ x) :=
  equivExterior_map f x

/-- The inverse form: the algebra map of an isometry carries the inverse exterior image of `y`
to the inverse exterior image of `ExteriorAlgebra.map f y`. -/
theorem map_equivExterior_symm {Q₁ : QuadraticForm R M} {Q₂ : QuadraticForm R N}
    (f : Q₁ →qᵢ Q₂) (y : ExteriorAlgebra R M) :
    map f ((equivExterior Q₁).symm y) =
      (equivExterior Q₂).symm (ExteriorAlgebra.map f.toLinearMap y) := by
  apply (equivExterior Q₂).injective
  rw [LinearEquiv.apply_symm_apply, equivExterior_map_eq_exteriorMap, LinearEquiv.apply_symm_apply]

end Exterior

end CliffordAlgebra

namespace ExteriorAlgebra

variable {R : Type*} [CommRing R]
variable {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- The ordered embedding of a mapped subset is the composite ordered embedding. -/
theorem ofFinEmbEquiv_symm_map {I J : Type*} [LinearOrder I] [LinearOrder J] {k : ℕ}
    (g : I ↪o J) (s : Set.powersetCard I k) :
    Set.powersetCard.ofFinEmbEquiv.symm (Set.powersetCard.map k g.toEmbedding s) =
      (Set.powersetCard.ofFinEmbEquiv.symm s).trans g := by
  rw [Set.powersetCard.ofFinEmbEquiv_symm_apply]
  symm
  apply Finset.orderEmbOfFin_unique'
  intro x
  rw [Set.powersetCard.val_map, Finset.mem_map]
  refine ⟨Set.powersetCard.ofFinEmbEquiv.symm s x, ?_, rfl⟩
  rw [Set.powersetCard.ofFinEmbEquiv_symm_apply]
  exact Finset.orderEmbOfFin_mem _ _ x

/-- Exterior monomials are natural: if a linear map sends the family `b` to `c ∘ g` for an order
embedding `g`, it sends the ordered monomial of `s` to the ordered monomial of `g(s)`. -/
theorem map_ιMulti_ofFinEmbEquiv_symm {I J : Type*} [LinearOrder I] [LinearOrder J] {k : ℕ}
    (g : I ↪o J) (b : I → M) (c : J → N) (f : M →ₗ[R] N) (hf : ∀ i, f (b i) = c (g i))
    (s : Set.powersetCard I k) :
    map f (ιMulti R k (b ∘ Set.powersetCard.ofFinEmbEquiv.symm s)) =
      ιMulti R k (c ∘ Set.powersetCard.ofFinEmbEquiv.symm
        (Set.powersetCard.map k g.toEmbedding s)) := by
  rw [map_apply_ιMulti, ofFinEmbEquiv_symm_map]
  congr 1
  funext i
  exact hf _

end ExteriorAlgebra
