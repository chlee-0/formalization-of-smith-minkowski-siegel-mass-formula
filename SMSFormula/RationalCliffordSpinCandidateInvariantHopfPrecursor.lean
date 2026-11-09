import SMSFormula.RationalCliffordSpinCandidateInvariantEpi
import SMSFormula.RationalCliffordSpinCandidateCoordinateHopf

/-!
# Hopf-operation stability of the literal Spin invariant quotient

Write `B` for the Spin-candidate coordinate ring and let `sigma` be right
translation by the nontrivial central `mu_2` point.  This file proves that
the literal fixed subalgebra `C = B^sigma` is stable under the coordinate
counit and antipode.  For comultiplication, it proves the sharper translation
identities

```text
Delta ∘ sigma = (sigma tensor id) ∘ Delta
              = (id tensor sigma) ∘ Delta
```

and factors `Delta|C` through the subalgebra of `B tensor_Q B` fixed
separately in both tensor factors.

The remaining bundling step is to identify that separately fixed tensor
subalgebra with `C tensor_Q C`.  No flatness or quotient-effectivity theorem
is assumed here.
-/

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 800000

open RationalTamagawa

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

private abbrev B := V.cliffordSpinCandidateCoordinateRing
private abbrev BB := TensorProduct ℚ V.B V.B
private abbrev C := V.negOneInvariantSubalgebra

/-- The rational algebra structure on the fixed subalgebra, inherited through
the implemented special-orthogonal coordinate ring. -/
noncomputable instance negOneInvariantSubalgebraRatAlgebra : Algebra ℚ V.C :=
  V.negOneInvariantQuotientStructureRingHom.toAlgebra

local instance invariantHopfRatTower :
    IsScalarTower ℚ V.specialOrthogonalCoordinateRing V.C :=
  IsScalarTower.of_algebraMap_eq' (R := ℚ)
    (S := V.specialOrthogonalCoordinateRing) (A := V.C) rfl

@[simp] theorem coe_algebraMap_negOneInvariantSubalgebra (q : ℚ) :
    ((algebraMap ℚ V.C q : V.C) : V.B) = algebraMap ℚ V.B q := by
  change V.specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom
      (algebraMap ℚ V.specialOrthogonalCoordinateRing q) =
    algebraMap ℚ V.B q
  exact V.specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom.commutes q

/-- Translation by the nontrivial scalar point in the left tensor factor. -/
def negOneTensorLeft : V.BB →ₐ[ℚ] V.BB :=
  Algebra.TensorProduct.map V.cliffordSpinCandidateNegOneCoordinateEnd
    (AlgHom.id ℚ V.B)

/-- Translation by the nontrivial scalar point in the right tensor factor. -/
def negOneTensorRight : V.BB →ₐ[ℚ] V.BB :=
  Algebra.TensorProduct.map (AlgHom.id ℚ V.B)
    V.cliffordSpinCandidateNegOneCoordinateEnd

/-- Right translation before comultiplication is right translation in the
second tensor factor afterward. -/
theorem coordinateComul_comp_negOne_eq_tensorRight :
    V.cliffordSpinCandidateCoordinateComul.comp
        V.cliffordSpinCandidateNegOneCoordinateEnd =
      V.negOneTensorRight.comp V.cliffordSpinCandidateCoordinateComul := by
  let T := V.BB
  letI : Group (V.B →ₐ[ℚ] T) :=
    V.cliffordSpinCandidateCoordinateAlgHomGroup T
  letI : Monoid (V.B →ₐ[ℚ] T) :=
    (V.cliffordSpinCandidateCoordinateAlgHomGroup T).toMonoid
  letI : Group (V.B →ₐ[ℚ] V.B) :=
    V.cliffordSpinCandidateCoordinateAlgHomGroup V.B
  letI : Monoid (V.B →ₐ[ℚ] V.B) :=
    (V.cliffordSpinCandidateCoordinateAlgHomGroup V.B).toMonoid
  let l : V.B →ₐ[ℚ] T := Algebra.TensorProduct.includeLeft
  let r : V.B →ₐ[ℚ] T := Algebra.TensorProduct.includeRight
  let e : V.B →ₐ[ℚ] V.B := AlgHom.id ℚ V.B
  let k : V.B →ₐ[ℚ] V.B := V.cliffordSpinCandidateNegOneKernelPoint
  let kT : V.B →ₐ[ℚ] T :=
    (V.rootsOfUnityMulEquivCliffordSpinCandidateAffineCoordinateKernelPoint T
      (negOneRootOfUnity T)).1
  have hmapk (f : V.B →ₐ[ℚ] T) : f.comp k = kT := by
    have hnat :=
      V.rootsOfUnityMulEquivCliffordSpinCandidateAffineCoordinateKernelPoint_naturality
        (A := V.B) (B := T) f (negOneRootOfUnity V.B)
    change f.comp
        ((V.rootsOfUnityMulEquivCliffordSpinCandidateAffineCoordinateKernelPoint
          V.B (negOneRootOfUnity V.B)).1) = _ at hnat
    rw [restrictRootsOfUnity_negOne V.B T f] at hnat
    simpa [k, kT, cliffordSpinCandidateNegOneKernelPoint] using hnat
  have hsigma : V.cliffordSpinCandidateNegOneCoordinateEnd = e * k := by
    rfl
  have hcomul : V.cliffordSpinCandidateCoordinateComul = l * r := rfl
  let mapR : (V.B →ₐ[ℚ] V.B) →* (V.B →ₐ[ℚ] T) :=
    V.cliffordSpinCandidateCoordinateAlgHomMap V.B (B := T) r
  let mapDelta : (V.B →ₐ[ℚ] V.B) →* (V.B →ₐ[ℚ] T) :=
    V.cliffordSpinCandidateCoordinateAlgHomMap V.B (B := T) (l * r)
  let mapAct : (V.B →ₐ[ℚ] T) →* (V.B →ₐ[ℚ] T) :=
    V.cliffordSpinCandidateCoordinateAlgHomMap T (B := T) V.negOneTensorRight
  have hright : V.negOneTensorRight.comp l = l := by
    ext b
    simp [negOneTensorRight, l]
  have hright' : V.negOneTensorRight.comp r = r * kT := by
    calc
      V.negOneTensorRight.comp r = r.comp
          V.cliffordSpinCandidateNegOneCoordinateEnd := by
        ext b
        change (1 : V.B) ⊗ₜ[ℚ]
            V.cliffordSpinCandidateNegOneCoordinateEnd b =
          (1 : V.B) ⊗ₜ[ℚ] V.cliffordSpinCandidateNegOneCoordinateEnd b
        rfl
      _ = r.comp (e * k) := by rw [hsigma]
      _ = r * r.comp k := by
        exact mapR.map_mul e k
      _ = r * kT := by rw [hmapk r]
  rw [hcomul, hsigma]
  calc
    (l * r).comp (e * k) = (l * r) * (l * r).comp k := by
      exact mapDelta.map_mul e k
    _ = (l * r) * kT := by rw [hmapk (l * r)]
    _ = l * (r * kT) := by rw [mul_assoc]
    _ = V.negOneTensorRight.comp l * V.negOneTensorRight.comp r := by
      rw [hright, hright']
    _ = V.negOneTensorRight.comp (l * r) := by
      exact (mapAct.map_mul l r).symm

/-- Centrality also identifies right translation before comultiplication with
translation in the first tensor factor afterward. -/
theorem coordinateComul_comp_negOne_eq_tensorLeft :
    V.cliffordSpinCandidateCoordinateComul.comp
        V.cliffordSpinCandidateNegOneCoordinateEnd =
      V.negOneTensorLeft.comp V.cliffordSpinCandidateCoordinateComul := by
  let T := V.BB
  letI : Group (V.B →ₐ[ℚ] T) :=
    V.cliffordSpinCandidateCoordinateAlgHomGroup T
  letI : Monoid (V.B →ₐ[ℚ] T) :=
    (V.cliffordSpinCandidateCoordinateAlgHomGroup T).toMonoid
  letI : Group (V.B →ₐ[ℚ] V.B) :=
    V.cliffordSpinCandidateCoordinateAlgHomGroup V.B
  letI : Monoid (V.B →ₐ[ℚ] V.B) :=
    (V.cliffordSpinCandidateCoordinateAlgHomGroup V.B).toMonoid
  let l : V.B →ₐ[ℚ] T := Algebra.TensorProduct.includeLeft
  let r : V.B →ₐ[ℚ] T := Algebra.TensorProduct.includeRight
  let e : V.B →ₐ[ℚ] V.B := AlgHom.id ℚ V.B
  let k : V.B →ₐ[ℚ] V.B := V.cliffordSpinCandidateNegOneKernelPoint
  let kT : V.B →ₐ[ℚ] T :=
    (V.rootsOfUnityMulEquivCliffordSpinCandidateAffineCoordinateKernelPoint T
      (negOneRootOfUnity T)).1
  have hmapk (f : V.B →ₐ[ℚ] T) : f.comp k = kT := by
    have hnat :=
      V.rootsOfUnityMulEquivCliffordSpinCandidateAffineCoordinateKernelPoint_naturality
        (A := V.B) (B := T) f (negOneRootOfUnity V.B)
    change f.comp
        ((V.rootsOfUnityMulEquivCliffordSpinCandidateAffineCoordinateKernelPoint
          V.B (negOneRootOfUnity V.B)).1) = _ at hnat
    rw [restrictRootsOfUnity_negOne V.B T f] at hnat
    simpa [k, kT, cliffordSpinCandidateNegOneKernelPoint] using hnat
  have hsigma : V.cliffordSpinCandidateNegOneCoordinateEnd = e * k := by
    rfl
  have hcomul : V.cliffordSpinCandidateCoordinateComul = l * r := rfl
  let mapL : (V.B →ₐ[ℚ] V.B) →* (V.B →ₐ[ℚ] T) :=
    V.cliffordSpinCandidateCoordinateAlgHomMap V.B (B := T) l
  let mapDelta : (V.B →ₐ[ℚ] V.B) →* (V.B →ₐ[ℚ] T) :=
    V.cliffordSpinCandidateCoordinateAlgHomMap V.B (B := T) (l * r)
  let mapAct : (V.B →ₐ[ℚ] T) →* (V.B →ₐ[ℚ] T) :=
    V.cliffordSpinCandidateCoordinateAlgHomMap T (B := T) V.negOneTensorLeft
  have hleft : V.negOneTensorLeft.comp r = r := by
    ext b
    simp [negOneTensorLeft, r]
  have hleft' : V.negOneTensorLeft.comp l = l * kT := by
    calc
      V.negOneTensorLeft.comp l = l.comp
          V.cliffordSpinCandidateNegOneCoordinateEnd := by
        ext b
        change V.cliffordSpinCandidateNegOneCoordinateEnd b ⊗ₜ[ℚ] (1 : V.B) =
          V.cliffordSpinCandidateNegOneCoordinateEnd b ⊗ₜ[ℚ] (1 : V.B)
        rfl
      _ = l.comp (e * k) := by rw [hsigma]
      _ = l * l.comp k := by
        exact mapL.map_mul e k
      _ = l * kT := by rw [hmapk l]
  have hkcomm : kT * r = r * kT :=
    V.rootsOfUnityMulEquivCliffordSpinCandidateAffineCoordinateKernelPoint_commutes
      (negOneRootOfUnity T) r
  rw [hcomul, hsigma]
  calc
    (l * r).comp (e * k) = (l * r) * (l * r).comp k := by
      exact mapDelta.map_mul e k
    _ = (l * r) * kT := by rw [hmapk (l * r)]
    _ = (l * kT) * r := by rw [mul_assoc, mul_assoc, hkcomm]
    _ = V.negOneTensorLeft.comp l * V.negOneTensorLeft.comp r := by
      rw [hleft, hleft']
    _ = V.negOneTensorLeft.comp (l * r) := by
      exact (mapAct.map_mul l r).symm

/-- Inversion commutes with translation by the central order-two point. -/
theorem coordinateAntipode_commutes_negOne :
    V.cliffordSpinCandidateCoordinateAntipode.comp
        V.cliffordSpinCandidateNegOneCoordinateEnd =
      V.cliffordSpinCandidateNegOneCoordinateEnd.comp
        V.cliffordSpinCandidateCoordinateAntipode := by
  letI : Group (V.B →ₐ[ℚ] V.B) :=
    V.cliffordSpinCandidateCoordinateAlgHomGroup V.B
  letI : Monoid (V.B →ₐ[ℚ] V.B) :=
    (V.cliffordSpinCandidateCoordinateAlgHomGroup V.B).toMonoid
  let e : V.B →ₐ[ℚ] V.B := AlgHom.id ℚ V.B
  let k : V.B →ₐ[ℚ] V.B := V.cliffordSpinCandidateNegOneKernelPoint
  let S : V.B →ₐ[ℚ] V.B := V.cliffordSpinCandidateCoordinateAntipode
  let sigma : V.B →ₐ[ℚ] V.B := V.cliffordSpinCandidateNegOneCoordinateEnd
  let mapS : (V.B →ₐ[ℚ] V.B) →* (V.B →ₐ[ℚ] V.B) :=
    V.cliffordSpinCandidateCoordinateAlgHomMap V.B (B := V.B) S
  let mapSigma : (V.B →ₐ[ℚ] V.B) →* (V.B →ₐ[ℚ] V.B) :=
    V.cliffordSpinCandidateCoordinateAlgHomMap V.B (B := V.B) sigma
  have hsigma : sigma = e * k := rfl
  have hS : S = e⁻¹ := rfl
  have hkself : k * k = 1 := by
    let E :=
      V.rootsOfUnityMulEquivCliffordSpinCandidateAffineCoordinateKernelPoint V.B
    have hm := congrArg Subtype.val
      (E.map_mul (negOneRootOfUnity V.B) (negOneRootOfUnity V.B))
    change (E (negOneRootOfUnity V.B * negOneRootOfUnity V.B)).1 = k * k at hm
    rw [← hm, negOneRootOfUnity_mul_self]
    exact congrArg Subtype.val E.map_one
  have hkcomm : k * S = S * k :=
    V.rootsOfUnityMulEquivCliffordSpinCandidateAffineCoordinateKernelPoint_commutes
      (negOneRootOfUnity V.B) S
  have hkecomm : k * e = e * k :=
    V.rootsOfUnityMulEquivCliffordSpinCandidateAffineCoordinateKernelPoint_commutes
      (negOneRootOfUnity V.B) e
  have hmapSk : S.comp k = k := by
    have hnat :=
      V.rootsOfUnityMulEquivCliffordSpinCandidateAffineCoordinateKernelPoint_naturality
        (A := V.B) (B := V.B) S (negOneRootOfUnity V.B)
    change S.comp k = _ at hnat
    rw [restrictRootsOfUnity_negOne V.B V.B S] at hnat
    simpa [k, cliffordSpinCandidateNegOneKernelPoint] using hnat
  have hleft : S.comp sigma = S * k := by
    calc
      S.comp sigma = mapS sigma := rfl
      _ = mapS (e * k) := by rw [hsigma]
      _ = mapS e * mapS k := map_mul mapS e k
      _ = S * k := by
        change S.comp e * S.comp k = S * k
        rw [hmapSk]
        rfl
  have hright : sigma.comp S = S * k := by
    have hsigma_inv : sigma⁻¹ = S * k := by
      apply (eq_inv_of_mul_eq_one_left ?_).symm
      rw [hsigma]
      calc
        (S * k) * (e * k) = S * (k * e) * k := by simp only [mul_assoc]
        _ = S * (e * k) * k := by rw [hkecomm]
        _ = (S * e) * (k * k) := by simp only [mul_assoc]
        _ = 1 := by rw [hS, inv_mul_cancel, hkself, one_mul]
    calc
      sigma.comp S = mapSigma S := rfl
      _ = mapSigma (e⁻¹) := by rw [hS]
      _ = (mapSigma e)⁻¹ := map_inv mapSigma e
      _ = sigma⁻¹ := by rfl
      _ = S * k := hsigma_inv
  exact hleft.trans hright.symm

/-- The Spin comultiplication of an invariant element is fixed by translation
in the right tensor factor. -/
theorem coordinateComul_invariant_tensorRight (c : V.C) :
    V.negOneTensorRight (V.cliffordSpinCandidateCoordinateComul c.1) =
      V.cliffordSpinCandidateCoordinateComul c.1 := by
  calc
    V.negOneTensorRight (V.cliffordSpinCandidateCoordinateComul c.1) =
        V.cliffordSpinCandidateCoordinateComul
          (V.cliffordSpinCandidateNegOneCoordinateEnd c.1) := by
      exact DFunLike.congr_fun
        V.coordinateComul_comp_negOne_eq_tensorRight c.1 |>.symm
    _ = V.cliffordSpinCandidateCoordinateComul c.1 := by
      rw [show V.cliffordSpinCandidateNegOneCoordinateEnd c.1 = c.1 from c.2]

/-- The Spin comultiplication of an invariant element is fixed by translation
in the left tensor factor. -/
theorem coordinateComul_invariant_tensorLeft (c : V.C) :
    V.negOneTensorLeft (V.cliffordSpinCandidateCoordinateComul c.1) =
      V.cliffordSpinCandidateCoordinateComul c.1 := by
  calc
    V.negOneTensorLeft (V.cliffordSpinCandidateCoordinateComul c.1) =
        V.cliffordSpinCandidateCoordinateComul
          (V.cliffordSpinCandidateNegOneCoordinateEnd c.1) := by
      exact DFunLike.congr_fun
        V.coordinateComul_comp_negOne_eq_tensorLeft c.1 |>.symm
    _ = V.cliffordSpinCandidateCoordinateComul c.1 := by
      rw [show V.cliffordSpinCandidateNegOneCoordinateEnd c.1 = c.1 from c.2]

/-- The subalgebra of the candidate self-tensor fixed separately by the two
nontrivial scalar translations. -/
def negOneBiInvariantTensorSubalgebra : Subalgebra ℚ V.BB where
  carrier := {z | V.negOneTensorLeft z = z ∧ V.negOneTensorRight z = z}
  mul_mem' := by
    intro x y hx hy
    exact ⟨by rw [map_mul, hx.1, hy.1], by rw [map_mul, hx.2, hy.2]⟩
  one_mem' := ⟨V.negOneTensorLeft.map_one', V.negOneTensorRight.map_one'⟩
  add_mem' := by
    intro x y hx hy
    exact ⟨by rw [map_add, hx.1, hy.1], by rw [map_add, hx.2, hy.2]⟩
  zero_mem' := ⟨map_zero _, map_zero _⟩
  algebraMap_mem' := by
    intro q
    exact ⟨V.negOneTensorLeft.commutes q, V.negOneTensorRight.commutes q⟩

/-- The candidate comultiplication restricted to the literal invariant ring,
with codomain the separately invariant part of the candidate self-tensor. -/
def negOneInvariantComulToBiInvariant :
    V.C →ₐ[ℚ] V.negOneBiInvariantTensorSubalgebra where
  toFun c := ⟨V.cliffordSpinCandidateCoordinateComul c.1,
    V.coordinateComul_invariant_tensorLeft c,
    V.coordinateComul_invariant_tensorRight c⟩
  map_one' := by ext; exact V.cliffordSpinCandidateCoordinateComul.map_one'
  map_mul' x y := by ext; exact map_mul _ x.1 y.1
  map_zero' := by ext; exact map_zero _
  map_add' x y := by ext; exact map_add _ x.1 y.1
  commutes' q := by
    apply Subtype.ext
    calc
      V.cliffordSpinCandidateCoordinateComul
          ((algebraMap ℚ V.C q : V.C) : V.B) =
        V.cliffordSpinCandidateCoordinateComul (algebraMap ℚ V.B q) := by
          rw [V.coe_algebraMap_negOneInvariantSubalgebra]
      _ = algebraMap ℚ V.BB q :=
        V.cliffordSpinCandidateCoordinateComul.commutes q
      _ = ((algebraMap ℚ V.negOneBiInvariantTensorSubalgebra q :
          V.negOneBiInvariantTensorSubalgebra) : V.BB) := by rfl

/-- The candidate counit restricted to the literal invariant ring. -/
def negOneInvariantCounit : V.C →ₐ[ℚ] ℚ :=
  V.cliffordSpinCandidateCoordinateCounit.comp (V.C.val.restrictScalars ℚ)

/-- The candidate antipode preserves the literal invariant ring. -/
def negOneInvariantAntipode : V.C →ₐ[ℚ] V.C where
  toFun c := ⟨V.cliffordSpinCandidateCoordinateAntipode c.1, by
    change V.cliffordSpinCandidateNegOneCoordinateEnd
        (V.cliffordSpinCandidateCoordinateAntipode c.1) =
      V.cliffordSpinCandidateCoordinateAntipode c.1
    calc
      V.cliffordSpinCandidateNegOneCoordinateEnd
          (V.cliffordSpinCandidateCoordinateAntipode c.1) =
        V.cliffordSpinCandidateCoordinateAntipode
          (V.cliffordSpinCandidateNegOneCoordinateEnd c.1) := by
        exact DFunLike.congr_fun V.coordinateAntipode_commutes_negOne c.1 |>.symm
      _ = V.cliffordSpinCandidateCoordinateAntipode c.1 := by
        rw [show V.cliffordSpinCandidateNegOneCoordinateEnd c.1 = c.1 from c.2]⟩
  map_one' := by ext; exact map_one _
  map_mul' x y := by ext; exact map_mul _ x.1 y.1
  map_zero' := by ext; exact map_zero _
  map_add' x y := by ext; exact map_add _ x.1 y.1
  commutes' q := by
    apply Subtype.ext
    calc
      V.cliffordSpinCandidateCoordinateAntipode
          ((algebraMap ℚ V.C q : V.C) : V.B) =
        V.cliffordSpinCandidateCoordinateAntipode (algebraMap ℚ V.B q) := by
          rw [V.coe_algebraMap_negOneInvariantSubalgebra]
      _ = algebraMap ℚ V.B q :=
        V.cliffordSpinCandidateCoordinateAntipode.commutes q
      _ = ((algebraMap ℚ V.C q : V.C) : V.B) := by
        rw [V.coe_algebraMap_negOneInvariantSubalgebra]

end RationalQuadraticSpaceMatrix
