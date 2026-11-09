import SMSFormula.RationalCliffordSpinCandidateFinitePresentation
import Mathlib.RingTheory.AdjoinRoot

/-!
# Quadratic fppf square-root covers

For a nonzero commutative ring `A` and `a : A`, the monic quadratic algebra

```text
A[t] / (t² - a)
```

is free of rank two over `A`.  Its structure map is therefore faithfully
flat and finitely presented, so the induced affine morphism is an fppf cover.
The distinguished root squares to `a`.

The construction is also functorial under arbitrary ring homomorphisms.  This
is the algebraic square-root primitive needed for later fppf-local
normalization of Clifford reflection products.  No reflection generation or
surjectivity of the Clifford--Spin candidate cover is proved here.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial

namespace RationalTamagawa

universe u v

variable (A : Type u) [CommRing A]

/-- The monic polynomial defining the quadratic square-root algebra. -/
def quadraticRootPolynomial (a : A) : A[X] := X ^ 2 - C a

theorem quadraticRootPolynomial_monic (a : A) :
    (quadraticRootPolynomial A a).Monic := by
  exact monic_X_pow_sub_C a (by norm_num)

theorem quadraticRootPolynomial_natDegree [Nontrivial A] (a : A) :
    (quadraticRootPolynomial A a).natDegree = 2 := by
  exact natDegree_X_pow_sub_C (R := A)

/-- The quadratic algebra obtained by adjoining a square root of `a`. -/
abbrev QuadraticRootAlgebra (a : A) :=
  AdjoinRoot (quadraticRootPolynomial A a)

/-- The standard power basis `1, t` of the quadratic root algebra. -/
def quadraticRootPowerBasis (a : A) :
    PowerBasis A (QuadraticRootAlgebra A a) :=
  AdjoinRoot.powerBasis' (quadraticRootPolynomial_monic A a)

@[simp] theorem quadraticRootPowerBasis_dim [Nontrivial A] (a : A) :
    (quadraticRootPowerBasis A a).dim = 2 := by
  exact quadraticRootPolynomial_natDegree A a

/-- The square-root algebra is finite free over its base ring. -/
theorem quadraticRootAlgebra_finite_free (a : A) :
    Module.Finite A (QuadraticRootAlgebra A a) ∧
      Module.Free A (QuadraticRootAlgebra A a) := by
  exact ⟨(quadraticRootPolynomial_monic A a).finite_adjoinRoot,
    (quadraticRootPolynomial_monic A a).free_adjoinRoot⟩

set_option backward.isDefEq.respectTransparency false in
/-- The distinguished element of the quadratic root algebra squares to `a`. -/
theorem quadraticRootAlgebra_root_sq (a : A) :
    (AdjoinRoot.root (quadraticRootPolynomial A a)) ^ 2 =
      algebraMap A (QuadraticRootAlgebra A a) a := by
  have h := AdjoinRoot.eval₂_root (quadraticRootPolynomial A a)
  apply sub_eq_zero.mp
  simpa only [quadraticRootPolynomial, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C] using h

/-- The standard two-element basis makes the quadratic root algebra
faithfully flat. -/
theorem quadraticRootAlgebra_faithfullyFlat [Nontrivial A] (a : A) :
    (algebraMap A (QuadraticRootAlgebra A a)).FaithfullyFlat := by
  rw [RingHom.faithfullyFlat_algebraMap_iff]
  let pb := quadraticRootPowerBasis A a
  haveI : Nonempty (Fin pb.dim) := by
    rw [show pb.dim = 2 by exact quadraticRootPowerBasis_dim A a]
    infer_instance
  exact Module.FaithfullyFlat.of_linearEquiv A (Fin pb.dim →₀ A) pb.basis.repr

/-- A monic quadratic root algebra is finitely presented over its base. -/
theorem quadraticRootAlgebra_finitePresentation (a : A) :
    (algebraMap A (QuadraticRootAlgebra A a)).FinitePresentation := by
  rw [RingHom.finitePresentation_algebraMap]
  infer_instance

section Nontrivial

variable [Nontrivial A]

/-- The affine scheme of the quadratic root algebra. -/
abbrev quadraticRootAffineScheme (a : A) : Scheme :=
  Spec (CommRingCat.of (QuadraticRootAlgebra A a))

/-- The affine structure morphism associated with adjoining a square root. -/
def quadraticRootSchemeHom (a : A) :
    quadraticRootAffineScheme A a ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A (QuadraticRootAlgebra A a)))

instance quadraticRootSchemeHomFlat (a : A) :
    Flat (quadraticRootSchemeHom A a) := by
  exact ((flat_and_surjective_SpecMap_iff
    (CommRingCat.ofHom (algebraMap A (QuadraticRootAlgebra A a)))).mpr
      (quadraticRootAlgebra_faithfullyFlat A a)).1

instance quadraticRootSchemeHomSurjective (a : A) :
    Surjective (quadraticRootSchemeHom A a) := by
  exact ((flat_and_surjective_SpecMap_iff
    (CommRingCat.ofHom (algebraMap A (QuadraticRootAlgebra A a)))).mpr
      (quadraticRootAlgebra_faithfullyFlat A a)).2

instance quadraticRootSchemeHomLocallyOfFinitePresentation (a : A) :
    LocallyOfFinitePresentation (quadraticRootSchemeHom A a) := by
  change LocallyOfFinitePresentation
    (Spec.map (CommRingCat.ofHom (algebraMap A (QuadraticRootAlgebra A a))))
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)]
  exact quadraticRootAlgebra_finitePresentation A a

/-- The quadratic square-root morphism is flat, surjective, and locally of
finite presentation. -/
theorem quadraticRootSchemeHom_fppf (a : A) :
    (Surjective (quadraticRootSchemeHom A a) ∧
        Flat (quadraticRootSchemeHom A a)) ∧
      LocallyOfFinitePresentation (quadraticRootSchemeHom A a) := by
  exact ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩

end Nontrivial

variable (B : Type v) [CommRing B]

/-- Scalar extension of a quadratic root algebra along a ring homomorphism. -/
def quadraticRootMap (f : A →+* B) (a : A) :
    QuadraticRootAlgebra A a →+* QuadraticRootAlgebra B (f a) :=
  AdjoinRoot.map f (quadraticRootPolynomial A a)
    (quadraticRootPolynomial B (f a)) (by
      rw [show (quadraticRootPolynomial A a).map f =
        quadraticRootPolynomial B (f a) by simp [quadraticRootPolynomial]])

@[simp] theorem quadraticRootMap_root (f : A →+* B) (a : A) :
    quadraticRootMap A B f a (AdjoinRoot.root (quadraticRootPolynomial A a)) =
      AdjoinRoot.root (quadraticRootPolynomial B (f a)) := by
  simp [quadraticRootMap]

@[simp] theorem quadraticRootMap_algebraMap (f : A →+* B) (a x : A) :
    quadraticRootMap A B f a (algebraMap A (QuadraticRootAlgebra A a) x) =
      algebraMap B (QuadraticRootAlgebra B (f a)) (f x) := by
  simp [quadraticRootMap, AdjoinRoot.algebraMap_eq]

@[simp] theorem quadraticRootMap_id (a : A) :
    quadraticRootMap A A (RingHom.id A) a =
      RingHom.id (QuadraticRootAlgebra A a) := by
  apply AdjoinRoot.ringHom_ext
  · ext x
    change quadraticRootMap A A (RingHom.id A) a
      (algebraMap A (QuadraticRootAlgebra A a) x) =
        algebraMap A (QuadraticRootAlgebra A a) x
    rw [quadraticRootMap_algebraMap]
    rfl
  · exact quadraticRootMap_root A A (RingHom.id A) a

variable (C : Type*) [CommRing C]

/-- Quadratic root scalar extension is compatible with composition. -/
theorem quadraticRootMap_comp (f : A →+* B) (g : B →+* C) (a : A) :
    quadraticRootMap A C (g.comp f) a =
      (quadraticRootMap B C g (f a)).comp (quadraticRootMap A B f a) := by
  apply AdjoinRoot.ringHom_ext
  · ext x
    change quadraticRootMap A C (g.comp f) a
      (algebraMap A (QuadraticRootAlgebra A a) x) =
        quadraticRootMap B C g (f a)
          (quadraticRootMap A B f a
            (algebraMap A (QuadraticRootAlgebra A a) x))
    rw [quadraticRootMap_algebraMap, quadraticRootMap_algebraMap,
      quadraticRootMap_algebraMap]
    rfl
  · rw [quadraticRootMap_root]
    change AdjoinRoot.root (quadraticRootPolynomial C (g (f a))) =
      quadraticRootMap B C g (f a)
        (quadraticRootMap A B f a
          (AdjoinRoot.root (quadraticRootPolynomial A a)))
    rw [quadraticRootMap_root, quadraticRootMap_root]

end RationalTamagawa
