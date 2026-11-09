import Mathlib.RingTheory.HopfAlgebra.Basic

/-!
# Hopf algebras from natural affine-point groups

This file reconstructs the commutative Hopf algebra represented by an affine
functor whose algebra-valued points carry a natural group law.  It is a small
bridge for affine group schemes assembled by representability rather than from
pre-existing coordinate Hopf data.
-/

noncomputable section

open scoped TensorProduct

/-- A natural group structure on the functor `B ↦ Hom_R(A, B)`. -/
structure AffinePointGroupData (R A : Type) [CommRing R] [CommRing A]
    [Algebra R A] where
  pointGroup (B : Type) [CommRing B] [Algebra R B] :
    Group (A →ₐ[R] B)
  map {B C : Type} [CommRing B] [CommRing C] [Algebra R B] [Algebra R C]
      (f : B →ₐ[R] C) :
      letI := pointGroup B
      letI := pointGroup C
      (A →ₐ[R] B) →* (A →ₐ[R] C)
  map_apply {B C : Type} [CommRing B] [CommRing C] [Algebra R B] [Algebra R C]
      (f : B →ₐ[R] C) (F : A →ₐ[R] B) :
      letI := pointGroup B
      letI := pointGroup C
      map f F = f.comp F

namespace AffinePointGroupData

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A]

/-- The comultiplication represented by multiplying the two universal points. -/
def comul (D : AffinePointGroupData R A) : A →ₐ[R] A ⊗[R] A := by
  letI := D.pointGroup (A ⊗[R] A)
  exact (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] A) *
    (Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A)

/-- The counit represented by the identity point. -/
def counit (D : AffinePointGroupData R A) : A →ₐ[R] R := by
  letI := D.pointGroup R
  exact 1

/-- The antipode represented by inversion of the universal point. -/
def antipode (D : AffinePointGroupData R A) : A →ₐ[R] A := by
  letI := D.pointGroup A
  exact (AlgHom.id R A)⁻¹

set_option maxHeartbeats 1200000 in
theorem comul_coassoc (D : AffinePointGroupData R A) :
    (Algebra.TensorProduct.assoc R R R A A A).toAlgHom.comp
      ((Algebra.TensorProduct.map D.comul (AlgHom.id R A)).comp D.comul) =
    (Algebra.TensorProduct.map (AlgHom.id R A) D.comul).comp D.comul := by
  let AA := A ⊗[R] A
  let AAA := A ⊗[R] AA
  letI := D.pointGroup AA
  letI := D.pointGroup AAA
  let l : A →ₐ[R] AA := Algebra.TensorProduct.includeLeft
  let r : A →ₐ[R] AA := Algebra.TensorProduct.includeRight
  let p1 : A →ₐ[R] AAA := Algebra.TensorProduct.includeLeft
  let p2 : A →ₐ[R] AAA :=
    (Algebra.TensorProduct.includeRight : AA →ₐ[R] AAA).comp l
  let p3 : A →ₐ[R] AAA :=
    (Algebra.TensorProduct.includeRight : AA →ₐ[R] AAA).comp r
  let tL : AA →ₐ[R] AAA :=
    (Algebra.TensorProduct.assoc R R R A A A).toAlgHom.comp
      (Algebra.TensorProduct.map D.comul (AlgHom.id R A))
  let tR : AA →ₐ[R] AAA :=
    Algebra.TensorProduct.map (AlgHom.id R A) D.comul
  let qL : AA →ₐ[R] AAA :=
    (Algebra.TensorProduct.assoc R R R A A A).toAlgHom.comp
      (Algebra.TensorProduct.includeLeft : AA →ₐ[R] AA ⊗[R] A)
  let qR : AA →ₐ[R] AAA := Algebra.TensorProduct.includeRight
  have hqL_l : qL.comp l = p1 := by
    ext x
    rfl
  have hqL_r : qL.comp r = p2 := by
    ext x
    rfl
  have htL_l : tL.comp l = p1 * p2 := by
    calc
      tL.comp l = qL.comp D.comul := by
        ext x
        change (Algebra.TensorProduct.assoc R R R A A A)
            ((Algebra.TensorProduct.map D.comul (AlgHom.id R A))
              ((Algebra.TensorProduct.includeLeft : A →ₐ[R] AA) x)) =
          (Algebra.TensorProduct.assoc R R R A A A)
            ((Algebra.TensorProduct.includeLeft :
              AA →ₐ[R] AA ⊗[R] A) (D.comul x))
        rw [Algebra.TensorProduct.includeLeft_apply,
          Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
          Algebra.TensorProduct.includeLeft_apply]
      _ = D.map (B := AA) (C := AAA) qL D.comul :=
        (D.map_apply (B := AA) (C := AAA) qL D.comul).symm
      _ = D.map (B := AA) (C := AAA) qL (l * r) := by rfl
      _ = D.map (B := AA) (C := AAA) qL l *
          D.map (B := AA) (C := AAA) qL r :=
        map_mul (D.map (B := AA) (C := AAA) qL) l r
      _ = qL.comp l * qL.comp r := by
        rw [D.map_apply (B := AA) (C := AAA) qL l,
          D.map_apply (B := AA) (C := AAA) qL r]
      _ = p1 * p2 := by rw [hqL_l, hqL_r]
  have htL_r : tL.comp r = p3 := by
    ext x
    change (Algebra.TensorProduct.assoc R R R A A A)
          ((Algebra.TensorProduct.map D.comul (AlgHom.id R A))
            ((Algebra.TensorProduct.includeRight : A →ₐ[R] AA) x)) =
        (Algebra.TensorProduct.includeRight : AA →ₐ[R] AAA)
          ((Algebra.TensorProduct.includeRight : A →ₐ[R] AA) x)
    rw [Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
    rw [show (1 : AA) = (1 : A) ⊗ₜ[R] (1 : A) from
      Algebra.TensorProduct.one_def]
    rw [
      Algebra.TensorProduct.assoc_tmul,
      Algebra.TensorProduct.includeRight_apply]
  have htR_l : tR.comp l = p1 := by
    ext x
    dsimp only [tR, l, p1, AlgHom.comp_apply]
    rw [Algebra.TensorProduct.includeLeft_apply,
      Algebra.TensorProduct.map_tmul, map_one]
    rfl
  have hqR_l : qR.comp l = p2 := by
    rfl
  have hqR_r : qR.comp r = p3 := by
    rfl
  have htR_r : tR.comp r = p2 * p3 := by
    calc
      tR.comp r = qR.comp D.comul := by
        ext x
        dsimp only [tR, qR, r, AlgHom.comp_apply]
        rw [Algebra.TensorProduct.includeRight_apply,
          Algebra.TensorProduct.map_tmul]
        rfl
      _ = D.map (B := AA) (C := AAA) qR D.comul :=
        (D.map_apply (B := AA) (C := AAA) qR D.comul).symm
      _ = D.map (B := AA) (C := AAA) qR (l * r) := by rfl
      _ = D.map (B := AA) (C := AAA) qR l *
          D.map (B := AA) (C := AAA) qR r :=
        map_mul (D.map (B := AA) (C := AAA) qR) l r
      _ = qR.comp l * qR.comp r := by
        rw [D.map_apply (B := AA) (C := AAA) qR l,
          D.map_apply (B := AA) (C := AAA) qR r]
      _ = p2 * p3 := by rw [hqR_l, hqR_r]
  calc
    tL.comp D.comul = D.map (B := AA) (C := AAA) tL D.comul :=
      (D.map_apply (B := AA) (C := AAA) tL D.comul).symm
    _ = D.map (B := AA) (C := AAA) tL (l * r) := by rfl
    _ = D.map (B := AA) (C := AAA) tL l *
        D.map (B := AA) (C := AAA) tL r :=
      map_mul (D.map (B := AA) (C := AAA) tL) l r
    _ = tL.comp l * tL.comp r := by
      rw [D.map_apply (B := AA) (C := AAA) tL l,
        D.map_apply (B := AA) (C := AAA) tL r]
    _ = (p1 * p2) * p3 := by rw [htL_l, htL_r]
    _ = p1 * (p2 * p3) := mul_assoc _ _ _
    _ = tR.comp l * tR.comp r := by rw [htR_l, htR_r]
    _ = D.map (B := AA) (C := AAA) tR l *
        D.map (B := AA) (C := AAA) tR r := by
      rw [D.map_apply (B := AA) (C := AAA) tR l,
        D.map_apply (B := AA) (C := AAA) tR r]
    _ = D.map (B := AA) (C := AAA) tR (l * r) :=
      (map_mul (D.map (B := AA) (C := AAA) tR) l r).symm
    _ = D.map (B := AA) (C := AAA) tR D.comul := by rfl
    _ = tR.comp D.comul :=
      D.map_apply (B := AA) (C := AAA) tR D.comul

set_option maxHeartbeats 800000 in
theorem comul_rTensor_counit (D : AffinePointGroupData R A) :
    (Algebra.TensorProduct.map D.counit (AlgHom.id R A)).comp D.comul =
      (Algebra.TensorProduct.lid R A).symm := by
  let AA := A ⊗[R] A
  let RA := R ⊗[R] A
  letI := D.pointGroup R
  letI := D.pointGroup AA
  letI := D.pointGroup RA
  let l : A →ₐ[R] AA := Algebra.TensorProduct.includeLeft
  let r : A →ₐ[R] AA := Algebra.TensorProduct.includeRight
  let t : AA →ₐ[R] RA :=
    Algebra.TensorProduct.map D.counit (AlgHom.id R A)
  let q : R →ₐ[R] RA := Algebra.TensorProduct.includeLeft
  let p : A →ₐ[R] RA := (Algebra.TensorProduct.lid R A).symm
  have ht_l : t.comp l = 1 := by
    calc
      t.comp l = q.comp D.counit := by
        ext x
        dsimp only [t, l, q, AlgHom.comp_apply]
        rw [Algebra.TensorProduct.includeLeft_apply,
          Algebra.TensorProduct.map_tmul]
        rfl
      _ = D.map (B := R) (C := RA) q D.counit :=
        (D.map_apply (B := R) (C := RA) q D.counit).symm
      _ = D.map (B := R) (C := RA) q 1 := by rfl
      _ = 1 := map_one (D.map (B := R) (C := RA) q)
  have ht_r : t.comp r = p := by
    ext x
    dsimp only [t, r, p, AlgHom.comp_apply]
    rw [Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.map_tmul]
    rw [map_one, AlgHom.id_apply]
    exact (Algebra.TensorProduct.lid_symm_apply R x).symm
  calc
    t.comp D.comul = D.map (B := AA) (C := RA) t D.comul :=
      (D.map_apply (B := AA) (C := RA) t D.comul).symm
    _ = D.map (B := AA) (C := RA) t (l * r) := by rfl
    _ = D.map (B := AA) (C := RA) t l *
        D.map (B := AA) (C := RA) t r :=
      map_mul (D.map (B := AA) (C := RA) t) l r
    _ = t.comp l * t.comp r := by
      rw [D.map_apply (B := AA) (C := RA) t l,
        D.map_apply (B := AA) (C := RA) t r]
    _ = 1 * p := by rw [ht_l, ht_r]
    _ = p := one_mul p

set_option maxHeartbeats 800000 in
theorem comul_lTensor_counit (D : AffinePointGroupData R A) :
    (Algebra.TensorProduct.map (AlgHom.id R A) D.counit).comp D.comul =
      (Algebra.TensorProduct.rid R R A).symm := by
  let AA := A ⊗[R] A
  let AR := A ⊗[R] R
  letI := D.pointGroup R
  letI := D.pointGroup AA
  letI := D.pointGroup AR
  let l : A →ₐ[R] AA := Algebra.TensorProduct.includeLeft
  let r : A →ₐ[R] AA := Algebra.TensorProduct.includeRight
  let t : AA →ₐ[R] AR :=
    Algebra.TensorProduct.map (AlgHom.id R A) D.counit
  let q : R →ₐ[R] AR := Algebra.TensorProduct.includeRight
  let p : A →ₐ[R] AR := (Algebra.TensorProduct.rid R R A).symm
  have ht_l : t.comp l = p := by
    ext x
    dsimp only [t, l, p, AlgHom.comp_apply]
    rw [Algebra.TensorProduct.includeLeft_apply,
      Algebra.TensorProduct.map_tmul]
    rw [map_one, AlgHom.id_apply]
    exact (Algebra.TensorProduct.rid_symm_apply R R x).symm
  have ht_r : t.comp r = 1 := by
    calc
      t.comp r = q.comp D.counit := by
        ext x
        dsimp only [t, r, q, AlgHom.comp_apply]
        rw [Algebra.TensorProduct.includeRight_apply,
          Algebra.TensorProduct.map_tmul]
        rfl
      _ = D.map (B := R) (C := AR) q D.counit :=
        (D.map_apply (B := R) (C := AR) q D.counit).symm
      _ = D.map (B := R) (C := AR) q 1 := by rfl
      _ = 1 := map_one (D.map (B := R) (C := AR) q)
  calc
    t.comp D.comul = D.map (B := AA) (C := AR) t D.comul :=
      (D.map_apply (B := AA) (C := AR) t D.comul).symm
    _ = D.map (B := AA) (C := AR) t (l * r) := by rfl
    _ = D.map (B := AA) (C := AR) t l *
        D.map (B := AA) (C := AR) t r :=
      map_mul (D.map (B := AA) (C := AR) t) l r
    _ = t.comp l * t.comp r := by
      rw [D.map_apply (B := AA) (C := AR) t l,
        D.map_apply (B := AA) (C := AR) t r]
    _ = p * 1 := by rw [ht_l, ht_r]
    _ = p := mul_one p

def mulAlgHom : A ⊗[R] A →ₐ[R] A :=
  Algebra.TensorProduct.lift (AlgHom.id R A) (AlgHom.id R A)
    fun _ _ => Commute.all _ _

def unitAlgHom : R →ₐ[R] A := Algebra.ofId R A

set_option maxHeartbeats 800000 in
theorem antipode_rTensor (D : AffinePointGroupData R A) :
    (mulAlgHom (R := R) (A := A)).comp
      ((Algebra.TensorProduct.map D.antipode (AlgHom.id R A)).comp D.comul) =
      (unitAlgHom (R := R) (A := A)).comp D.counit := by
  let AA := A ⊗[R] A
  letI := D.pointGroup R
  letI := D.pointGroup A
  letI := D.pointGroup AA
  letI : Monoid (A →ₐ[R] A) := (D.pointGroup A).toMonoid
  letI : Monoid (A →ₐ[R] AA) := (D.pointGroup AA).toMonoid
  let l : A →ₐ[R] AA := Algebra.TensorProduct.includeLeft
  let r : A →ₐ[R] AA := Algebra.TensorProduct.includeRight
  let t : AA →ₐ[R] A := (mulAlgHom (R := R) (A := A)).comp
    (Algebra.TensorProduct.map D.antipode (AlgHom.id R A))
  let e : A →ₐ[R] A := AlgHom.id R A
  let eOne : A →ₐ[R] A := (D.pointGroup A).one
  have ht_l : t.comp l = D.antipode := by
    ext x
    change (mulAlgHom (R := R) (A := A))
      ((Algebra.TensorProduct.map D.antipode (AlgHom.id R A))
        ((Algebra.TensorProduct.includeLeft : A →ₐ[R] AA) x)) =
          D.antipode x
    rw [Algebra.TensorProduct.includeLeft_apply,
      Algebra.TensorProduct.map_tmul]
    simp [mulAlgHom]
  have ht_r : t.comp r = e := by
    ext x
    change (mulAlgHom (R := R) (A := A))
      ((Algebra.TensorProduct.map D.antipode (AlgHom.id R A))
        ((Algebra.TensorProduct.includeRight : A →ₐ[R] AA) x)) = x
    rw [Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.map_tmul]
    simp [mulAlgHom]
  calc
    t.comp D.comul = D.map (B := AA) (C := A) t D.comul :=
      (D.map_apply (B := AA) (C := A) t D.comul).symm
    _ = D.map (B := AA) (C := A) t (l * r) := by rfl
    _ = (D.pointGroup A).mul (D.map (B := AA) (C := A) t l)
        (D.map (B := AA) (C := A) t r) := by
      exact (D.map (B := AA) (C := A) t).map_mul l r
    _ = (D.pointGroup A).mul (t.comp l) (t.comp r) := by
      rw [D.map_apply (B := AA) (C := A) t l,
        D.map_apply (B := AA) (C := A) t r]
    _ = eOne := by
      rw [ht_l, ht_r]
      exact @inv_mul_cancel _ (D.pointGroup A) e
    _ = D.map (B := R) (C := A)
        (unitAlgHom (R := R) (A := A))
          ((D.pointGroup R).one) :=
      (map_one (D.map (B := R) (C := A)
        (unitAlgHom (R := R) (A := A)))).symm
    _ = D.map (B := R) (C := A)
        (unitAlgHom (R := R) (A := A)) D.counit := by rfl
    _ = (unitAlgHom (R := R) (A := A)).comp D.counit :=
      D.map_apply (B := R) (C := A)
        (unitAlgHom (R := R) (A := A)) D.counit

set_option maxHeartbeats 800000 in
theorem antipode_lTensor (D : AffinePointGroupData R A) :
    (mulAlgHom (R := R) (A := A)).comp
      ((Algebra.TensorProduct.map (AlgHom.id R A) D.antipode).comp D.comul) =
      (unitAlgHom (R := R) (A := A)).comp D.counit := by
  let AA := A ⊗[R] A
  letI := D.pointGroup R
  letI := D.pointGroup A
  letI := D.pointGroup AA
  letI : Monoid (A →ₐ[R] A) := (D.pointGroup A).toMonoid
  letI : Monoid (A →ₐ[R] AA) := (D.pointGroup AA).toMonoid
  let l : A →ₐ[R] AA := Algebra.TensorProduct.includeLeft
  let r : A →ₐ[R] AA := Algebra.TensorProduct.includeRight
  let t : AA →ₐ[R] A := (mulAlgHom (R := R) (A := A)).comp
    (Algebra.TensorProduct.map (AlgHom.id R A) D.antipode)
  let e : A →ₐ[R] A := AlgHom.id R A
  let eOne : A →ₐ[R] A := (D.pointGroup A).one
  have ht_l : t.comp l = e := by
    ext x
    change (mulAlgHom (R := R) (A := A))
      ((Algebra.TensorProduct.map (AlgHom.id R A) D.antipode)
        ((Algebra.TensorProduct.includeLeft : A →ₐ[R] AA) x)) = x
    rw [Algebra.TensorProduct.includeLeft_apply,
      Algebra.TensorProduct.map_tmul]
    simp [mulAlgHom]
  have ht_r : t.comp r = D.antipode := by
    ext x
    change (mulAlgHom (R := R) (A := A))
      ((Algebra.TensorProduct.map (AlgHom.id R A) D.antipode)
        ((Algebra.TensorProduct.includeRight : A →ₐ[R] AA) x)) =
          D.antipode x
    rw [Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.map_tmul]
    simp [mulAlgHom]
  calc
    t.comp D.comul = D.map (B := AA) (C := A) t D.comul :=
      (D.map_apply (B := AA) (C := A) t D.comul).symm
    _ = D.map (B := AA) (C := A) t (l * r) := by rfl
    _ = (D.pointGroup A).mul (D.map (B := AA) (C := A) t l)
        (D.map (B := AA) (C := A) t r) := by
      exact (D.map (B := AA) (C := A) t).map_mul l r
    _ = (D.pointGroup A).mul (t.comp l) (t.comp r) := by
      rw [D.map_apply (B := AA) (C := A) t l,
        D.map_apply (B := AA) (C := A) t r]
    _ = eOne := by
      rw [ht_l, ht_r]
      exact @mul_inv_cancel _ (D.pointGroup A) e
    _ = D.map (B := R) (C := A)
        (unitAlgHom (R := R) (A := A))
          ((D.pointGroup R).one) :=
      (map_one (D.map (B := R) (C := A)
        (unitAlgHom (R := R) (A := A)))).symm
    _ = D.map (B := R) (C := A)
        (unitAlgHom (R := R) (A := A)) D.counit := by rfl
    _ = (unitAlgHom (R := R) (A := A)).comp D.counit :=
      D.map_apply (B := R) (C := A)
        (unitAlgHom (R := R) (A := A)) D.counit

/-- The bialgebra represented by the natural monoid part of the point group. -/
@[implicit_reducible]
noncomputable def bialgebra (D : AffinePointGroupData R A) : Bialgebra R A :=
  Bialgebra.ofAlgHom D.comul D.counit D.comul_coassoc
    D.comul_rTensor_counit D.comul_lTensor_counit

set_option maxHeartbeats 800000 in
/-- The Hopf algebra represented by the natural affine-point group. -/
@[implicit_reducible]
noncomputable def hopfAlgebra (D : AffinePointGroupData R A) : HopfAlgebra R A := by
  letI : Bialgebra R A := D.bialgebra
  letI : HopfAlgebraStruct R A :=
    { antipode := D.antipode.toLinearMap }
  refine
    { mul_antipode_rTensor_comul := ?_
      mul_antipode_lTensor_comul := ?_ }
  · apply LinearMap.ext
    intro x
    have h := congrArg (fun F : A →ₐ[R] A => F x) D.antipode_rTensor
    simpa [mulAlgHom, unitAlgHom] using h
  · apply LinearMap.ext
    intro x
    have h := congrArg (fun F : A →ₐ[R] A => F x) D.antipode_lTensor
    simpa [mulAlgHom, unitAlgHom] using h

end AffinePointGroupData
