import SMSFormula.AffinePointGroupHopf
import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.RingTheory.Bialgebra.Hom
import Mathlib.RingTheory.Coalgebra.Convolution

/-!
# Affine-point groups from commutative Hopf algebras

This file supplies the reverse of `AffinePointGroupHopf.lean` for the
commutative coordinate rings used in this project.  If the antipode of a Hopf
algebra is available as an algebra homomorphism, convolution makes every
algebra-valued point set into a group, naturally in the target algebra.

Mathlib already proves associativity and the unit laws for convolution on
linear maps.  The only additional ingredients here are closure on algebra
homomorphisms and reflection of the Hopf inverse identity.  No quotient or
flatness theorem is used.
-/

noncomputable section

set_option maxHeartbeats 1000000

open Coalgebra WithConv
open scoped TensorProduct

namespace HopfAlgebra

variable {R A D : Type} [CommRing R] [CommRing A] [CommRing D]
  [Algebra R D] [HopfAlgebra R A]

/-- Convolution of two algebra-valued points of a commutative Hopf algebra. -/
def algHomConvolution (f g : A →ₐ[R] D) : A →ₐ[R] D :=
  (AffinePointGroupData.mulAlgHom (R := R) (A := D)).comp
    ((Algebra.TensorProduct.map f g).comp (Bialgebra.comulAlgHom R A))

/-- The convolution unit on algebra-valued points. -/
def algHomUnit : A →ₐ[R] D :=
  (AffinePointGroupData.unitAlgHom (R := R) (A := D)).comp
    (Bialgebra.counitAlgHom R A)

/-- Inversion of an algebra-valued point by precomposition with an algebraic
antipode. -/
def algHomInv (S : A →ₐ[R] A) (f : A →ₐ[R] D) : A →ₐ[R] D :=
  f.comp S

theorem algHomConvolution_apply (f g : A →ₐ[R] D) (a : A) :
    algHomConvolution f g a =
      (toConv f.toLinearMap * toConv g.toLinearMap :
        WithConv (A →ₗ[R] D)) a := by
  rfl

theorem algHomUnit_apply (a : A) :
    (algHomUnit : A →ₐ[R] D) a =
      (1 : WithConv (A →ₗ[R] D)) a := by
  rfl

theorem algHomConvolution_assoc (f g h : A →ₐ[R] D) :
    algHomConvolution (algHomConvolution f g) h =
      algHomConvolution f (algHomConvolution g h) := by
  apply AlgHom.ext
  intro a
  simp only [algHomConvolution_apply]
  exact DFunLike.congr_fun (congrArg WithConv.ofConv (mul_assoc
    (toConv f.toLinearMap) (toConv g.toLinearMap) (toConv h.toLinearMap))) a

theorem algHomUnit_mul (f : A →ₐ[R] D) :
    algHomConvolution algHomUnit f = f := by
  apply AlgHom.ext
  intro a
  rw [algHomConvolution_apply]
  have hu : toConv (algHomUnit : A →ₐ[R] D).toLinearMap =
      (1 : WithConv (A →ₗ[R] D)) := by
    ext x
    exact algHomUnit_apply x
  rw [hu, one_mul]
  rfl

theorem algHomInv_mul (S : A →ₐ[R] A)
    (hS : S.toLinearMap = HopfAlgebra.antipode R) (f : A →ₐ[R] D) :
    algHomConvolution (algHomInv S f) f = algHomUnit := by
  apply AlgHom.ext
  intro a
  rw [algHomConvolution_apply, algHomUnit_apply]
  have hconv :
      (toConv S.toLinearMap * toConv (LinearMap.id : A →ₗ[R] A) :
        WithConv (A →ₗ[R] A)) a =
        (1 : WithConv (A →ₗ[R] A)) a := by
    simp only [LinearMap.convMul_apply, LinearMap.convOne_apply, hS]
    exact HopfAlgebra.mul_antipode_rTensor_comul_apply a
  have hmap := LinearMap.algHom_comp_convMul_distrib f
    (toConv S.toLinearMap) (toConv (LinearMap.id : A →ₗ[R] A))
  calc
    (toConv (algHomInv S f).toLinearMap * toConv f.toLinearMap :
        WithConv (A →ₗ[R] D)) a =
        f ((toConv S.toLinearMap *
          toConv (LinearMap.id : A →ₗ[R] A) :
            WithConv (A →ₗ[R] A)) a) := by
      exact (LinearMap.congr_fun hmap a).symm
    _ = f ((1 : WithConv (A →ₗ[R] A)) a) := congrArg f hconv
    _ = (1 : WithConv (A →ₗ[R] D)) a := by
      simp only [LinearMap.convOne_apply]
      exact f.commutes _

theorem algHomPostcomp_convolution {E : Type} [CommRing E] [Algebra R E]
    (q : D →ₐ[R] E) (f g : A →ₐ[R] D) :
    q.comp (algHomConvolution f g) =
      algHomConvolution (q.comp f) (q.comp g) := by
  apply AlgHom.toLinearMap_injective
  exact LinearMap.algHom_comp_convMul_distrib q
    (toConv f.toLinearMap) (toConv g.toLinearMap)

theorem algHomPostcomp_unit {E : Type} [CommRing E] [Algebra R E]
    (q : D →ₐ[R] E) :
    q.comp (algHomUnit : A →ₐ[R] D) = algHomUnit := by
  apply AlgHom.ext
  intro a
  simp only [AlgHom.comp_apply, algHomUnit_apply, LinearMap.convOne_apply]
  exact q.commutes _

/-- The convolution group on algebra-valued points of a commutative Hopf
algebra whose antipode is an algebra homomorphism. -/
@[implicit_reducible]
def algHomGroup (S : A →ₐ[R] A)
    (hS : S.toLinearMap = HopfAlgebra.antipode R) :
    Group (A →ₐ[R] D) := by
  letI : Mul (A →ₐ[R] D) := ⟨algHomConvolution⟩
  letI : One (A →ₐ[R] D) := ⟨algHomUnit⟩
  letI : Inv (A →ₐ[R] D) := ⟨algHomInv S⟩
  exact Group.ofLeftAxioms algHomConvolution_assoc algHomUnit_mul
    (algHomInv_mul S hS)

/-- The natural affine-point group represented by a commutative Hopf algebra
with algebraic antipode. -/
def affinePointGroupData (S : A →ₐ[R] A)
    (hS : S.toLinearMap = HopfAlgebra.antipode R) :
    AffinePointGroupData R A where
  pointGroup D _ _ := algHomGroup S hS
  map {B E} _ _ _ _ q := by
    letI := algHomGroup (D := B) S hS
    letI := algHomGroup (D := E) S hS
    exact
      { toFun := fun f => q.comp f
        map_one' := by
          change q.comp algHomUnit = algHomUnit
          exact algHomPostcomp_unit q
        map_mul' := by
          intro f g
          change q.comp (algHomConvolution f g) =
            algHomConvolution (q.comp f) (q.comp g)
          exact algHomPostcomp_convolution q f g }
  map_apply q f := rfl

theorem algHomPrecompBialgHom_convolution
    {E : Type} [CommRing E] [HopfAlgebra R E]
    (q : A →ₐc[R] E) (f g : E →ₐ[R] D) :
    (algHomConvolution f g).comp (q : A →ₐ[R] E) =
      algHomConvolution (f.comp (q : A →ₐ[R] E))
        (g.comp (q : A →ₐ[R] E)) := by
  apply AlgHom.ext
  intro a
  change (AffinePointGroupData.mulAlgHom (R := R) (A := D))
      ((Algebra.TensorProduct.map f g)
        ((Bialgebra.comulAlgHom R E) (q a))) =
    (AffinePointGroupData.mulAlgHom (R := R) (A := D))
      ((Algebra.TensorProduct.map (f.comp q) (g.comp q))
        ((Bialgebra.comulAlgHom R A) a))
  have hΔ := DFunLike.congr_fun
    (BialgHomClass.map_comp_comulAlgHom q) a
  change (Algebra.TensorProduct.map (q : A →ₐ[R] E) q)
      ((Bialgebra.comulAlgHom R A) a) =
    (Bialgebra.comulAlgHom R E) (q a) at hΔ
  rw [← hΔ]
  apply congrArg (AffinePointGroupData.mulAlgHom (R := R) (A := D))
  change TensorProduct.map f.toLinearMap g.toLinearMap
      (TensorProduct.map (q : A →ₐ[R] E).toLinearMap
        (q : A →ₐ[R] E).toLinearMap
          ((Bialgebra.comulAlgHom R A) a)) =
    TensorProduct.map (f.comp (q : A →ₐ[R] E)).toLinearMap
      (g.comp (q : A →ₐ[R] E)).toLinearMap
        ((Bialgebra.comulAlgHom R A) a)
  exact TensorProduct.map_map f.toLinearMap g.toLinearMap
    (q : A →ₐ[R] E).toLinearMap (q : A →ₐ[R] E).toLinearMap _

theorem algHomPrecompBialgHom_unit
    {E : Type} [CommRing E] [HopfAlgebra R E]
    (q : A →ₐc[R] E) :
    (algHomUnit : E →ₐ[R] D).comp (q : A →ₐ[R] E) = algHomUnit := by
  apply AlgHom.ext
  intro a
  change algebraMap R D ((Bialgebra.counitAlgHom R E) (q a)) =
    algebraMap R D ((Bialgebra.counitAlgHom R A) a)
  have hε := DFunLike.congr_fun
    (BialgHomClass.counitAlgHom_comp q) a
  change (Bialgebra.counitAlgHom R E) (q a) =
    (Bialgebra.counitAlgHom R A) a at hε
  rw [hε]

/-- Precomposition by a bialgebra homomorphism is a monoid homomorphism on
the convolution point groups. -/
def algHomPrecompBialgHom
    {E : Type} [CommRing E] [HopfAlgebra R E]
    (Sₐ : A →ₐ[R] A) (hSₐ : Sₐ.toLinearMap = HopfAlgebra.antipode R)
    (Sₑ : E →ₐ[R] E) (hSₑ : Sₑ.toLinearMap = HopfAlgebra.antipode R)
    (q : A →ₐc[R] E) :
    letI := algHomGroup (D := D) Sₐ hSₐ
    letI := algHomGroup (D := D) Sₑ hSₑ
    (E →ₐ[R] D) →* (A →ₐ[R] D) := by
  letI := algHomGroup (D := D) Sₐ hSₐ
  letI := algHomGroup (D := D) Sₑ hSₑ
  exact
    { toFun := fun f => f.comp (q : A →ₐ[R] E)
      map_one' := by
        change (algHomUnit : E →ₐ[R] D).comp
          (q : A →ₐ[R] E) = algHomUnit
        exact algHomPrecompBialgHom_unit q
      map_mul' := by
        intro f g
        change (algHomConvolution f g).comp (q : A →ₐ[R] E) =
          algHomConvolution (f.comp (q : A →ₐ[R] E))
            (g.comp (q : A →ₐ[R] E))
        exact algHomPrecompBialgHom_convolution q f g }

end HopfAlgebra

namespace AffinePointGroupData

variable {R A D : Type} [CommRing R] [CommRing A] [CommRing D]
  [Algebra R A] [Algebra R D]

/-- Convolution for the Hopf algebra reconstructed from affine-point group
data recovers the original point multiplication. -/
theorem algHomConvolution_eq_mul (G : AffinePointGroupData R A)
    (f g : A →ₐ[R] D) :
    letI := G.pointGroup D
    letI : HopfAlgebra R A := G.hopfAlgebra
    HopfAlgebra.algHomConvolution f g = f * g := by
  letI := G.pointGroup D
  letI := G.pointGroup (A ⊗[R] A)
  letI : HopfAlgebra R A := G.hopfAlgebra
  let q : A ⊗[R] A →ₐ[R] D :=
    (mulAlgHom (R := R) (A := D)).comp
      (Algebra.TensorProduct.map f g)
  calc
    HopfAlgebra.algHomConvolution f g = q.comp G.comul := by rfl
    _ = G.map q G.comul := (G.map_apply q G.comul).symm
    _ = G.map q ((Algebra.TensorProduct.includeLeft :
          A →ₐ[R] A ⊗[R] A) *
        (Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A)) := by
      rfl
    _ = G.map q (Algebra.TensorProduct.includeLeft :
          A →ₐ[R] A ⊗[R] A) *
        G.map q (Algebra.TensorProduct.includeRight :
          A →ₐ[R] A ⊗[R] A) := by
      exact map_mul (G.map q) _ _
    _ = q.comp (Algebra.TensorProduct.includeLeft :
          A →ₐ[R] A ⊗[R] A) *
        q.comp (Algebra.TensorProduct.includeRight :
          A →ₐ[R] A ⊗[R] A) := by
      rw [G.map_apply, G.map_apply]
    _ = f * g := by
      congr 1 <;> apply AlgHom.ext <;> intro a <;>
        simp [q, mulAlgHom]

set_option backward.isDefEq.respectTransparency false in
/-- The convolution unit for the reconstructed Hopf algebra is the original
point-group unit. -/
theorem algHomUnit_eq_one (G : AffinePointGroupData R A) :
    letI := G.pointGroup D
    letI : HopfAlgebra R A := G.hopfAlgebra
    (HopfAlgebra.algHomUnit : A →ₐ[R] D) = 1 := by
  letI := G.pointGroup R
  letI := G.pointGroup D
  letI : HopfAlgebra R A := G.hopfAlgebra
  calc
    (HopfAlgebra.algHomUnit : A →ₐ[R] D) =
        (unitAlgHom (R := R) (A := D)).comp G.counit := by rfl
    _ = G.map (unitAlgHom (R := R) (A := D)) G.counit :=
      (G.map_apply (unitAlgHom (R := R) (A := D)) G.counit).symm
    _ = G.map (unitAlgHom (R := R) (A := D)) 1 := by rfl
    _ = 1 := map_one (G.map (unitAlgHom (R := R) (A := D)))

end AffinePointGroupData
