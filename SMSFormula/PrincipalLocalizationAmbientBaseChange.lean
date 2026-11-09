import SMSFormula.PrincipalLocalizationScalarExtension

/-!
# Ambient principal localizations after scalar extension

This file identifies a scalar-extended principal localization with the
literal principal localization of the scalar-extended ambient ring.  We use
the right-tensor orientation `A ⊗[R] K`, for which the base-changed element is
`d ⊗ 1`.

The construction is independent of the Spin application.  It packages the
natural algebra structure on `A[d⁻¹] ⊗[R] K`, proves that this tensor product
is the localization of `A ⊗[R] K` away from `d ⊗ 1`, and records the
resulting canonical equivalence.
-/

noncomputable section

open TensorProduct

universe u

namespace Algebra.TensorProduct

variable {R K A B : Type u} [CommRing R] [CommRing K] [Algebra R K]
  [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Base change of an algebra homomorphism, in the right-tensor orientation. -/
noncomputable def mapRightAlgHom (f : A →ₐ[R] B) :
    A ⊗[R] K →ₐ[K] B ⊗[R] K :=
  (Algebra.TensorProduct.commRight R K B).toAlgHom.comp <|
    (Algebra.TensorProduct.map (AlgHom.id K K) f).comp <|
      (Algebra.TensorProduct.commRight R K A).symm.toAlgHom

@[simp]
theorem mapRightAlgHom_apply_tmul (f : A →ₐ[R] B) (a : A) (k : K) :
    mapRightAlgHom (K := K) f (a ⊗ₜ[R] k) = f a ⊗ₜ[R] k := by
  simp [mapRightAlgHom]

/-- The natural `A ⊗[R] K`-algebra structure on `A[d⁻¹] ⊗[R] K`. -/
noncomputable instance awayTensorRightAlgebra (d : A) :
    Algebra (A ⊗[R] K) (Localization.Away d ⊗[R] K) :=
  (Algebra.TensorProduct.map
    (IsScalarTower.toAlgHom R A (Localization.Away d))
    (AlgHom.id R K)).toRingHom.toAlgebra

@[simp]
theorem awayTensorRight_algebraMap_tmul (d : A) (a : A) (k : K) :
    algebraMap (A ⊗[R] K) (Localization.Away d ⊗[R] K) (a ⊗ₜ[R] k) =
      algebraMap A (Localization.Away d) a ⊗ₜ[R] k := by
  simp [RingHom.algebraMap_toAlgebra]

/-- The original `A`-action factors through the base-changed ambient ring. -/
noncomputable instance awayTensorRightIsScalarTower (d : A) :
    IsScalarTower A (A ⊗[R] K) (Localization.Away d ⊗[R] K) := by
  constructor
  intro a x y
  change
    (Algebra.TensorProduct.map
      (IsScalarTower.toAlgHom R A (Localization.Away d))
      (AlgHom.id R K)) (a • x) * y =
      a •
        ((Algebra.TensorProduct.map
          (IsScalarTower.toAlgHom R A (Localization.Away d))
          (AlgHom.id R K)) x * y)
  have hmap :
      (Algebra.TensorProduct.map
        (IsScalarTower.toAlgHom R A (Localization.Away d))
        (AlgHom.id R K)) (a • x) =
        a •
          (Algebra.TensorProduct.map
            (IsScalarTower.toAlgHom R A (Localization.Away d))
            (AlgHom.id R K)) x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul x k =>
        simp [Algebra.smul_def]
    | add x y hx hy => simp [hx, hy]
  rw [hmap, smul_mul_assoc]

private theorem awayTensorRight_algebraMap_comp_includeRight (d : A) :
    (algebraMap (A ⊗[R] K) (Localization.Away d ⊗[R] K)).comp
        Algebra.TensorProduct.includeRight.toRingHom =
      Algebra.TensorProduct.includeRight.toRingHom := by
  ext a
  simp [RingHom.algebraMap_toAlgebra]

/-- `A[d⁻¹] ⊗[R] K` is the localization of `A ⊗[R] K` away from
`d ⊗ 1`. -/
noncomputable instance awayTensorRightIsLocalization (d : A) :
    IsLocalization.Away
      (Algebra.TensorProduct.includeLeft
        (R := R) (S := R) (A := A) (B := K) d)
      (Localization.Away d ⊗[R] K) := by
  change IsLocalization
    (Submonoid.powers (algebraMap A (A ⊗[R] K) d))
    (Localization.Away d ⊗[R] K)
  simpa only [← Algebra.algebraMapSubmonoid_powers] using
    (IsLocalization.tensorProduct_tensorProduct R K (Submonoid.powers d)
      (Localization.Away d)
      (awayTensorRight_algebraMap_comp_includeRight (R := R) (K := K) d))

/-- Canonical identification of the tensor-localized ring with the literal
principal localization of the scalar-extended ambient ring. -/
noncomputable def awayTensorRightAmbientAlgEquiv (d : A) :
    Localization.Away d ⊗[R] K ≃ₐ[A ⊗[R] K]
      Localization.Away
        (Algebra.TensorProduct.includeLeft
          (R := R) (S := R) (A := A) (B := K) d) :=
  IsLocalization.algEquiv
    (Submonoid.powers
      (Algebra.TensorProduct.includeLeft
        (R := R) (S := R) (A := A) (B := K) d)) _ _

@[simp]
theorem awayTensorRightAmbientAlgEquiv_algebraMap (d : A) (x : A ⊗[R] K) :
    awayTensorRightAmbientAlgEquiv (R := R) (K := K) d
        (algebraMap (A ⊗[R] K) (Localization.Away d ⊗[R] K) x) =
      algebraMap (A ⊗[R] K)
        (Localization.Away
          (Algebra.TensorProduct.includeLeft
            (R := R) (S := R) (A := A) (B := K) d)) x := by
  exact (awayTensorRightAmbientAlgEquiv (R := R) (K := K) d).commutes x

@[simp]
theorem awayTensorRightAmbientAlgEquiv_symm_algebraMap (d : A)
    (x : A ⊗[R] K) :
    (awayTensorRightAmbientAlgEquiv (R := R) (K := K) d).symm
        (algebraMap (A ⊗[R] K)
          (Localization.Away
            (Algebra.TensorProduct.includeLeft
              (R := R) (S := R) (A := A) (B := K) d)) x) =
      algebraMap (A ⊗[R] K) (Localization.Away d ⊗[R] K) x := by
  exact (awayTensorRightAmbientAlgEquiv (R := R) (K := K) d).symm.commutes x

@[simp]
theorem awayTensorRightAmbientAlgEquiv_toRingEquiv_algebraMap (d : A)
    (x : A ⊗[R] K) :
    (awayTensorRightAmbientAlgEquiv (R := R) (K := K) d).toRingEquiv
        (algebraMap (A ⊗[R] K) (Localization.Away d ⊗[R] K) x) =
      algebraMap (A ⊗[R] K)
        (Localization.Away
          (Algebra.TensorProduct.includeLeft
            (R := R) (S := R) (A := A) (B := K) d)) x :=
  awayTensorRightAmbientAlgEquiv_algebraMap (R := R) (K := K) d x

@[simp]
theorem awayTensorRightAmbientAlgEquiv_symm_toRingEquiv_algebraMap (d : A)
    (x : A ⊗[R] K) :
    (awayTensorRightAmbientAlgEquiv (R := R) (K := K) d).symm.toRingEquiv
        (algebraMap (A ⊗[R] K)
          (Localization.Away
            (Algebra.TensorProduct.includeLeft
              (R := R) (S := R) (A := A) (B := K) d)) x) =
      algebraMap (A ⊗[R] K) (Localization.Away d ⊗[R] K) x :=
  awayTensorRightAmbientAlgEquiv_symm_algebraMap (R := R) (K := K) d x

/-- The ring equivalence on literal ambient principal localizations obtained
by conjugating scalar extension of a bijective away map through the two
tensor-localization identifications. -/
noncomputable def awayMapRightScalarExtensionRingEquiv
    (f : A →ₐ[R] B) (d : A)
    (h : Function.Bijective (Localization.awayMap f.toRingHom d)) :
    Localization.Away
        (Algebra.TensorProduct.includeLeft
          (R := R) (S := R) (A := A) (B := K) d) ≃+*
      Localization.Away
        (Algebra.TensorProduct.includeLeft
          (R := R) (S := R) (A := B) (B := K) (f d)) :=
  (awayTensorRightAmbientAlgEquiv (R := R) (K := K) d).symm.toRingEquiv |>.trans <|
    (Algebra.TensorProduct.commRight R K (Localization.Away d)).symm.toRingEquiv |>.trans <|
      (Localization.awayMapScalarExtensionAlgEquiv (K := K) f d h).toRingEquiv |>.trans <|
        (Algebra.TensorProduct.commRight R K
          (Localization.Away (f d))).toRingEquiv |>.trans <|
          (awayTensorRightAmbientAlgEquiv
            (R := R) (K := K) (f d)).toRingEquiv

set_option backward.isDefEq.respectTransparency false in
/-- The conjugated scalar-extension equivalence is literally the away map of
the base-changed ambient homomorphism. -/
theorem awayMapRightScalarExtensionRingEquiv_toRingHom
    (f : A →ₐ[R] B) (d : A)
    (h : Function.Bijective (Localization.awayMap f.toRingHom d)) :
    (awayMapRightScalarExtensionRingEquiv (K := K) f d h).toRingHom =
      Localization.awayMap
        (mapRightAlgHom (K := K) f).toRingHom
        (Algebra.TensorProduct.includeLeft
          (R := R) (S := R) (A := A) (B := K) d) := by
  apply IsLocalization.ringHom_ext
    (Submonoid.powers
      (Algebra.TensorProduct.includeLeft
        (R := R) (S := R) (A := A) (B := K) d))
  apply RingHom.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a k =>
      change awayMapRightScalarExtensionRingEquiv (K := K) f d h
          (algebraMap (A ⊗[R] K)
            (Localization.Away
              (Algebra.TensorProduct.includeLeft
                (R := R) (S := R) (A := A) (B := K) d)) (a ⊗ₜ[R] k)) = _
      simp only [awayMapRightScalarExtensionRingEquiv, RingEquiv.trans_apply]
      rw [awayTensorRightAmbientAlgEquiv_symm_toRingEquiv_algebraMap]
      rw [Algebra.TensorProduct.awayTensorRight_algebraMap_tmul]
      rw [show
        (Algebra.TensorProduct.commRight R K (Localization.Away d)).symm.toRingEquiv
            (algebraMap A (Localization.Away d) a ⊗ₜ[R] k) =
          k ⊗ₜ[R] algebraMap A (Localization.Away d) a by rfl]
      rw [show
        (Localization.awayMapScalarExtensionAlgEquiv (K := K) f d h).toRingEquiv
            (k ⊗ₜ[R] algebraMap A (Localization.Away d) a) =
          k ⊗ₜ[R]
            Localization.awayMapₐ f d (algebraMap A (Localization.Away d) a) by
        exact Localization.awayMapScalarExtensionAlgEquiv_apply_tmul
          (K := K) f d h k (algebraMap A (Localization.Away d) a)]
      rw [show
        (Algebra.TensorProduct.commRight R K
          (Localization.Away (f d))).toRingEquiv
            (k ⊗ₜ[R]
              Localization.awayMapₐ f d (algebraMap A (Localization.Away d) a)) =
          Localization.awayMapₐ f d
            (algebraMap A (Localization.Away d) a) ⊗ₜ[R] k by rfl]
      rw [show Localization.awayMapₐ f d
          (algebraMap A (Localization.Away d) a) =
          algebraMap B (Localization.Away (f d)) (f a) by
        simp [Localization.awayMapₐ, IsLocalization.Away.mapₐ,
          IsLocalization.Away.map, IsLocalization.map_eq]]
      rw [← Algebra.TensorProduct.awayTensorRight_algebraMap_tmul]
      rw [awayTensorRightAmbientAlgEquiv_toRingEquiv_algebraMap]
      simp [mapRightAlgHom, IsLocalization.Away.map]
  | add x y hx hy =>
      simpa only [RingHom.comp_apply, map_add] using congrArg₂ (.+.) hx hy

/-- Bijectivity of a principal away map survives scalar extension as a
literal principal away-map statement on the base-changed ambient rings. -/
theorem awayMapRightScalarExtension_bijective
    (f : A →ₐ[R] B) (d : A)
    (h : Function.Bijective (Localization.awayMap f.toRingHom d)) :
    Function.Bijective
      (Localization.awayMap
        (mapRightAlgHom (K := K) f).toRingHom
        (Algebra.TensorProduct.includeLeft
          (R := R) (S := R) (A := A) (B := K) d)) := by
  rw [← awayMapRightScalarExtensionRingEquiv_toRingHom (K := K) f d h]
  exact (awayMapRightScalarExtensionRingEquiv (K := K) f d h).bijective

/-- In the right-tensor orientation, an element avoiding a prime remains
nonnilpotent after faithfully flat scalar extension. -/
theorem includeLeft_not_isNilpotent_of_not_mem
    [Module.FaithfullyFlat R K]
    (p : Ideal A) [p.IsPrime] (d : A) (hd : d ∉ p) :
    ¬ IsNilpotent
      (Algebra.TensorProduct.includeLeft
        (R := R) (S := R) (A := A) (B := K) d) := by
  intro hnil
  apply Algebra.TensorProduct.includeRight_not_isNilpotent_of_not_mem
    (R := R) (K := K) p d hd
  obtain ⟨n, hn⟩ := hnil
  refine ⟨n, ?_⟩
  have hcomm := congrArg
    (Algebra.TensorProduct.comm R A K).toRingEquiv hn
  simpa using hcomm

/-- The right-oriented base-changed principal element is avoided by a prime. -/
theorem exists_prime_not_mem_includeLeft
    [Module.FaithfullyFlat R K]
    (p : Ideal A) [p.IsPrime] (d : A) (hd : d ∉ p) :
    ∃ q : Ideal (A ⊗[R] K), q.IsPrime ∧
      Algebra.TensorProduct.includeLeft
        (R := R) (S := R) (A := A) (B := K) d ∉ q := by
  have hnil := includeLeft_not_isNilpotent_of_not_mem
    (R := R) (K := K) p d hd
  by_contra h
  push_neg at h
  exact hnil (nilpotent_iff_mem_prime.mpr h)

end Algebra.TensorProduct
