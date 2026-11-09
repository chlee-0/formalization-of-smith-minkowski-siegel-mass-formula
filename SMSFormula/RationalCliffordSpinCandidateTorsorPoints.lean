import SMSFormula.RationalCliffordSpinCandidateKernelMuTwo

/-!
# Pointwise `mu_2` torsor law for the affine Clifford--Spin candidate

For every commutative rational algebra `A`, two affine Spin-candidate points
with the same image in `SO` differ by a unique scalar root of unity.  This is
packaged as the multiplicative equivalence

```text
SpinCandidate(A) x mu_2(A)
  ~= SpinCandidate(A) x_{SO(A)} SpinCandidate(A),
(x,z) |-> (x,x*z).
```

The equivalence is natural under arbitrary rational-algebra homomorphisms.
This is the pointwise torsor law.  Its upgrade to an isomorphism of the
represented affine schemes, and the resulting flatness argument, remain
separate categorical steps.
-/

noncomputable section

open RationalTamagawa

namespace MonoidHom

variable {G H Z : Type*} [Group G] [Group H] [Group Z]

/-- Pairs of group elements with the same image under a homomorphism. -/
def selfFiberSubgroup (φ : G →* H) : Subgroup (G × G) where
  carrier := { p | φ p.1 = φ p.2 }
  one_mem' := by simp
  mul_mem' := by
    intro p q hp hq
    change φ (p.1 * q.1) = φ (p.2 * q.2)
    rw [map_mul, map_mul, hp, hq]
  inv_mem' := by
    intro p hp
    change φ p.1⁻¹ = φ p.2⁻¹
    rw [map_inv, map_inv, hp]

/-- A central identification of `Z` with the kernel of `φ` gives the
pointwise torsor equivalence `(G x Z) ~= (G x_H G)`. -/
def centralKernelTorsorMulEquiv (φ : G →* H) (e : Z ≃* φ.ker)
    (hcentral : ∀ (z : Z) (x : G), (e z).1 * x = x * (e z).1) :
    (G × Z) ≃* φ.selfFiberSubgroup where
  toFun p := ⟨(p.1, p.1 * (e p.2).1), by
    change φ p.1 = φ (p.1 * (e p.2).1)
    rw [map_mul, (e p.2).2]
    simp⟩
  invFun p := (p.1.1, e.symm ⟨p.1.1⁻¹ * p.1.2, by
    change φ (p.1.1⁻¹ * p.1.2) = 1
    rw [map_mul, map_inv, p.2]
    simp⟩)
  left_inv p := by
    apply Prod.ext
    · rfl
    · change e.symm ⟨p.1⁻¹ * (p.1 * (e p.2).1), _⟩ = p.2
      apply e.injective
      rw [e.apply_symm_apply]
      apply Subtype.ext
      change p.1⁻¹ * (p.1 * (e p.2).1) = (e p.2).1
      simp
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change p.1.1 *
          (e (e.symm ⟨p.1.1⁻¹ * p.1.2, _⟩)).1 = p.1.2
      rw [e.apply_symm_apply]
      simp
  map_mul' p q := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change (p.1 * q.1) * (e (p.2 * q.2)).1 =
        (p.1 * (e p.2).1) * (q.1 * (e q.2).1)
      rw [map_mul]
      change (p.1 * q.1) * ((e p.2).1 * (e q.2).1) =
        (p.1 * (e p.2).1) * (q.1 * (e q.2).1)
      calc
        (p.1 * q.1) * ((e p.2).1 * (e q.2).1) =
            p.1 * (q.1 * (e p.2).1) * (e q.2).1 := by
              simp only [mul_assoc]
        _ = p.1 * ((e p.2).1 * q.1) * (e q.2).1 := by
          rw [hcentral p.2 q.1]
        _ = (p.1 * (e p.2).1) * (q.1 * (e q.2).1) := by
          simp only [mul_assoc]

end MonoidHom

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

/-- Pairs of affine Spin-candidate coordinate points with the same `SO`
image. -/
abbrev cliffordSpinCandidateCoordinateSelfFiber
    (A : Type) [CommRing A] [Algebra ℚ A] :=
  (V.cliffordSpinCandidateCoordinateAlgHomToSpecialOrthogonalGroup A
    ).selfFiberSubgroup

/-- Base change on pairs of candidate points having the same `SO` image. -/
def cliffordSpinCandidateCoordinateSelfFiberMap
    {A B : Type} [CommRing A] [CommRing B] [Algebra ℚ A] [Algebra ℚ B]
    (f : A →ₐ[ℚ] B) :
    V.cliffordSpinCandidateCoordinateSelfFiber A →*
      V.cliffordSpinCandidateCoordinateSelfFiber B where
  toFun p := ⟨
    (V.cliffordSpinCandidateCoordinateAlgHomMap A f p.1.1,
      V.cliffordSpinCandidateCoordinateAlgHomMap A f p.1.2), by
        change
          V.cliffordSpinCandidateCoordinateAlgHomToSpecialOrthogonalGroup B
              (f.comp p.1.1) =
            V.cliffordSpinCandidateCoordinateAlgHomToSpecialOrthogonalGroup B
              (f.comp p.1.2)
        rw [V.cliffordSpinCandidateCoordinateAlgHomToSpecialOrthogonalGroup_map,
          V.cliffordSpinCandidateCoordinateAlgHomToSpecialOrthogonalGroup_map,
          p.2]⟩
  map_one' := by
    apply Subtype.ext
    apply Prod.ext
    · exact map_one (V.cliffordSpinCandidateCoordinateAlgHomMap A f)
    · exact map_one (V.cliffordSpinCandidateCoordinateAlgHomMap A f)
  map_mul' p q := by
    apply Subtype.ext
    apply Prod.ext
    · exact map_mul
        (V.cliffordSpinCandidateCoordinateAlgHomMap A f) p.1.1 q.1.1
    · exact map_mul
        (V.cliffordSpinCandidateCoordinateAlgHomMap A f) p.1.2 q.1.2

/-- The affine pointwise torsor equivalence.  Its inverse sends `(x,y)` to
`(x,x^-1*y)`, with the second component identified with `mu_2(A)`. -/
def cliffordSpinCandidateCoordinateTorsorMulEquiv
    (A : Type) [CommRing A] [Algebra ℚ A] :
    ((V.cliffordSpinCandidateCoordinateRing →ₐ[ℚ] A) × rootsOfUnity 2 A) ≃*
      V.cliffordSpinCandidateCoordinateSelfFiber A :=
  MonoidHom.centralKernelTorsorMulEquiv
    (V.cliffordSpinCandidateCoordinateAlgHomToSpecialOrthogonalGroup A)
    (V.rootsOfUnityMulEquivCliffordSpinCandidateAffineCoordinateKernelPoint A)
    (fun z F =>
      V.rootsOfUnityMulEquivCliffordSpinCandidateAffineCoordinateKernelPoint_commutes
        z F)

/-- The affine pointwise torsor equivalence commutes with every rational
algebra homomorphism. -/
theorem cliffordSpinCandidateCoordinateTorsorMulEquiv_naturality
    {A B : Type} [CommRing A] [CommRing B] [Algebra ℚ A] [Algebra ℚ B]
    (f : A →ₐ[ℚ] B)
    (p : (V.cliffordSpinCandidateCoordinateRing →ₐ[ℚ] A) × rootsOfUnity 2 A) :
    V.cliffordSpinCandidateCoordinateSelfFiberMap f
        (V.cliffordSpinCandidateCoordinateTorsorMulEquiv A p) =
      V.cliffordSpinCandidateCoordinateTorsorMulEquiv B
        (V.cliffordSpinCandidateCoordinateAlgHomMap A f p.1,
          restrictRootsOfUnity f 2 p.2) := by
  apply Subtype.ext
  apply Prod.ext
  · change f.comp p.1 = f.comp p.1
    rfl
  · change V.cliffordSpinCandidateCoordinateAlgHomMap A f
          (p.1 *
            (V.rootsOfUnityMulEquivCliffordSpinCandidateAffineCoordinateKernelPoint
              A p.2).1) =
        V.cliffordSpinCandidateCoordinateAlgHomMap A f p.1 *
          (V.rootsOfUnityMulEquivCliffordSpinCandidateAffineCoordinateKernelPoint
            B (restrictRootsOfUnity f 2 p.2)).1
    rw [map_mul]
    rw [V.rootsOfUnityMulEquivCliffordSpinCandidateAffineCoordinateKernelPoint_naturality]

end RationalQuadraticSpaceMatrix
