import SMSFormula.PadicSpecialOrthogonalDifferentialGoodPrimeCoordinateTarget
import SMSFormula.SkewAdjointPadicElementaryCoordinateMeasureScale

/-!
# Form-adapted p-adic skew-adjoint coordinates

For a symmetric nonsingular rational form `F`, the continuous equivalence
`X ↦ F_p X` is exposed at the linear level.  The
scalar-extended form-adapted basis is then unreindexed by strict upper pairs
and transported to the canonical skew-symmetric basis.
-/

noncomputable section

open scoped Matrix

namespace Matrix

variable {n : ℕ}

/-- The linear equivalence `X ↦ F_p X` from transported skew-adjoint matrices
to skew-symmetric matrices. -/
def skewAdjointFormPadicSkewSymmetricLinearEquiv
    (p : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) :
    (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule ≃ₗ[ℚ_[p]]
      skewSymmetricMatricesSubmodule (R := ℚ_[p]) (ι := Fin n) :=
  (skewAdjointPadicSkewSymmetricContinuousLinearEquiv
    p F hF hdet).toLinearEquiv

/-- The forward p-adic form-adapted equivalence is left multiplication by
the scalar-extended form. -/
@[simp]
theorem coe_skewAdjointFormPadicSkewSymmetricLinearEquiv_apply
    (p : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0)
    (X : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
    (skewAdjointFormPadicSkewSymmetricLinearEquiv
        p F hF hdet X : Matrix (Fin n) (Fin n) ℚ_[p]) =
      F.map (algebraMap ℚ ℚ_[p]) *
        (X : Matrix (Fin n) (Fin n) ℚ_[p]) :=
  rfl

/-- The inverse p-adic form-adapted equivalence is left multiplication by
the inverse scalar-extended form. -/
@[simp]
theorem coe_skewAdjointFormPadicSkewSymmetricLinearEquiv_symm_apply
    (p : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0)
    (Y : skewSymmetricMatricesSubmodule
      (R := ℚ_[p]) (ι := Fin n)) :
    ((skewAdjointFormPadicSkewSymmetricLinearEquiv
        p F hF hdet).symm Y : Matrix (Fin n) (Fin n) ℚ_[p]) =
      (F.map (algebraMap ℚ ℚ_[p]))⁻¹ *
        (Y : Matrix (Fin n) (Fin n) ℚ_[p]) :=
  rfl

/-- The scalar-extended form-adapted p-adic basis with its original strict
upper-pair indexing restored. -/
def skewAdjointFormElementaryPadicBasis
    (p : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) :
    Module.Basis (StrictUpperPair n) ℚ_[p]
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  (skewAdjointFormElementaryPadicFinBasis p F hF hdet).reindex
    (skewAdjointFormElementaryIndexEquiv F hF hdet).symm

/-- The p-adic form equivalence sends every finite-index elementary
basis vector to the correspondingly reindexed skew-symmetric matrix unit. -/
theorem skewAdjointFormPadicSkewSymmetricLinearEquiv_apply_finBasis
    (p : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0)
    (j : Fin (Module.finrank ℚ
      (skewAdjointMatricesLieSubalgebra F))) :
    skewAdjointFormPadicSkewSymmetricLinearEquiv p F hF hdet
        (skewAdjointFormElementaryPadicFinBasis p F hF hdet j) =
      skewSymmetricBasis (K := ℚ_[p]) (by norm_num)
        ((skewAdjointFormElementaryIndexEquiv F hF hdet).symm j) := by
  apply Subtype.ext
  let q :=
    (skewAdjointFormElementaryIndexEquiv F hF hdet).symm j
  have hFunit : IsUnit F.det := isUnit_iff_ne_zero.mpr hdet
  have hrat :
      F * ((skewAdjointFormElementaryRationalFinBasis F hF hdet j :
          skewAdjointMatricesLieSubalgebra F) :
        Matrix (Fin n) (Fin n) ℚ) =
        Matrix.single q.1.1 q.1.2 1 -
          Matrix.single q.1.2 q.1.1 1 := by
    rw [skewAdjointFormElementaryRationalFinBasis,
      Module.Basis.reindex_apply,
      coe_skewAdjointFormElementaryRationalBasis_apply,
      ← Matrix.mul_assoc, Matrix.mul_nonsing_inv F hFunit,
      Matrix.one_mul]
  have hmap := congrArg
    (fun M : Matrix (Fin n) (Fin n) ℚ =>
      M.map (algebraMap ℚ ℚ_[p])) hrat
  change
    (F * ((skewAdjointFormElementaryRationalFinBasis F hF hdet j :
        skewAdjointMatricesLieSubalgebra F) :
      Matrix (Fin n) (Fin n) ℚ)).map (algebraMap ℚ ℚ_[p]) =
      (Matrix.single q.1.1 q.1.2 (1 : ℚ) -
        Matrix.single q.1.2 q.1.1 (1 : ℚ)).map
          (algebraMap ℚ ℚ_[p]) at hmap
  rw [Matrix.map_mul] at hmap
  simp only [
    coe_skewAdjointFormPadicSkewSymmetricLinearEquiv_apply,
    coe_skewAdjointFormElementaryPadicFinBasis_apply,
    skewSymmetricBasis_apply_coe]
  refine hmap.trans ?_
  rw [Matrix.map_sub _ (fun a b =>
    map_sub (algebraMap ℚ ℚ_[p]) a b),
    Matrix.map_single, Matrix.map_single, map_one]

/-- With strict-upper-pair indexing restored, the p-adic form equivalence
sends the form-adapted basis literally to the canonical skew-symmetric
basis. -/
@[simp]
theorem skewAdjointFormPadicSkewSymmetricLinearEquiv_apply_basis
    (p : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) (q : StrictUpperPair n) :
    skewAdjointFormPadicSkewSymmetricLinearEquiv p F hF hdet
        (skewAdjointFormElementaryPadicBasis p F hF hdet q) =
      skewSymmetricBasis (K := ℚ_[p]) (by norm_num) q := by
  have hb :
      skewAdjointFormElementaryPadicBasis p F hF hdet q =
        skewAdjointFormElementaryPadicFinBasis p F hF hdet
          (skewAdjointFormElementaryIndexEquiv F hF hdet q) := by
    change
      ((skewAdjointFormElementaryPadicFinBasis p F hF hdet).reindex
          (skewAdjointFormElementaryIndexEquiv F hF hdet).symm) q =
        skewAdjointFormElementaryPadicFinBasis p F hF hdet
          (skewAdjointFormElementaryIndexEquiv F hF hdet q)
    simpa only [Equiv.symm_symm] using
      Module.Basis.reindex_apply
        (skewAdjointFormElementaryPadicFinBasis p F hF hdet)
        (skewAdjointFormElementaryIndexEquiv F hF hdet).symm q
  rw [hb]
  simpa using
    skewAdjointFormPadicSkewSymmetricLinearEquiv_apply_finBasis
      p F hF hdet (skewAdjointFormElementaryIndexEquiv F hF hdet q)

/-- The coordinates in the canonical skew-symmetric basis are the strict
upper-triangular matrix entries. -/
@[simp]
theorem skewSymmetricBasis_equivFun_apply
    {K : Type*} [Field K] (hK : ringChar K ≠ 2)
    (Y : skewSymmetricMatricesSubmodule
      (R := K) (ι := Fin n))
    (q : StrictUpperPair n) :
    (skewSymmetricBasis hK).equivFun Y q =
      (Y : Matrix (Fin n) (Fin n) K) q.1.1 q.1.2 := by
  simp [skewSymmetricBasis, Module.Basis.map_equivFun,
    skewSymmetricUpperCoordinateEquiv]

/-- The unreindexed form-adapted coordinate equivalence is the p-adic form
equivalence followed by strict-upper skew-symmetric coordinates. -/
theorem skewAdjointFormElementaryPadicBasis_equivFun
    (p : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) :
    (skewAdjointFormElementaryPadicBasis p F hF hdet).equivFun =
      (skewAdjointFormPadicSkewSymmetricLinearEquiv p F hF hdet).trans
        (skewSymmetricBasis (K := ℚ_[p]) (by norm_num)).equivFun := by
  apply LinearEquiv.toLinearMap_injective
  apply (skewAdjointFormElementaryPadicBasis p F hF hdet).ext
  intro q
  change
    (skewAdjointFormElementaryPadicBasis p F hF hdet).equivFun
        (skewAdjointFormElementaryPadicBasis p F hF hdet q) =
      (skewSymmetricBasis (K := ℚ_[p]) (by norm_num)).equivFun
        (skewAdjointFormPadicSkewSymmetricLinearEquiv p F hF hdet
          (skewAdjointFormElementaryPadicBasis p F hF hdet q))
  rw [skewAdjointFormPadicSkewSymmetricLinearEquiv_apply_basis]
  simp

/-- Unreindexed form-adapted coordinates are the strict-upper entries of
`F_p X`. -/
theorem skewAdjointFormElementaryPadicBasis_equivFun_apply
    (p : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0)
    (X : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule)
    (q : StrictUpperPair n) :
    (skewAdjointFormElementaryPadicBasis p F hF hdet).equivFun X q =
      (F.map (algebraMap ℚ ℚ_[p]) *
        (X : Matrix (Fin n) (Fin n) ℚ_[p])) q.1.1 q.1.2 := by
  rw [skewAdjointFormElementaryPadicBasis_equivFun]
  exact skewSymmetricBasis_equivFun_apply (by norm_num)
    (skewAdjointFormPadicSkewSymmetricLinearEquiv p F hF hdet X) q

/-- In the finite reindexing, the `j`-th form-adapted coordinate is
the strict-upper entry indexed by the inverse fixed reindexing. -/
theorem skewAdjointFormElementaryPadicFinBasis_equivFun_apply
    (p : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0)
    (X : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule)
    (j : Fin (Module.finrank ℚ
      (skewAdjointMatricesLieSubalgebra F))) :
    (skewAdjointFormElementaryPadicFinBasis p F hF hdet).equivFun X j =
      (F.map (algebraMap ℚ ℚ_[p]) *
        (X : Matrix (Fin n) (Fin n) ℚ_[p]))
          ((skewAdjointFormElementaryIndexEquiv F hF hdet).symm j).1.1
          ((skewAdjointFormElementaryIndexEquiv F hF hdet).symm j).1.2 := by
  let q := (skewAdjointFormElementaryIndexEquiv F hF hdet).symm j
  have hrepr :=
    Module.Basis.repr_reindex
      (skewAdjointFormElementaryPadicFinBasis p F hF hdet) X
      (skewAdjointFormElementaryIndexEquiv F hF hdet).symm
  have hcoord := congrArg
    (fun c : StrictUpperPair n →₀ ℚ_[p] => c q) hrepr
  have hcoord' :
      (skewAdjointFormElementaryPadicFinBasis p F hF hdet).equivFun X j =
        (skewAdjointFormElementaryPadicBasis p F hF hdet).equivFun X q := by
    simp only [Module.Basis.equivFun_apply,
      skewAdjointFormElementaryPadicBasis]
    simpa only [Finsupp.mapDomain_equiv_apply, Equiv.symm_symm,
      Equiv.apply_symm_apply, q] using hcoord.symm
  rw [hcoord']
  exact skewAdjointFormElementaryPadicBasis_equivFun_apply
    p F hF hdet X q

/-- The continuous form-adapted coordinate equivalence therefore records
the reindexed strict-upper entries of `F_p X`. -/
theorem skewAdjointFormElementaryPadicCoordinateEquiv_apply
    (p : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0)
    (X : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule)
    (j : Fin (Module.finrank ℚ
      (skewAdjointMatricesLieSubalgebra F))) :
    skewAdjointFormElementaryPadicCoordinateEquiv p F hF hdet X j =
      (F.map (algebraMap ℚ ℚ_[p]) *
        (X : Matrix (Fin n) (Fin n) ℚ_[p]))
          ((skewAdjointFormElementaryIndexEquiv F hF hdet).symm j).1.1
          ((skewAdjointFormElementaryIndexEquiv F hF hdet).symm j).1.2 := by
  change
    (skewAdjointFormElementaryPadicFinBasis p F hF hdet).equivFun X j = _
  exact skewAdjointFormElementaryPadicFinBasis_equivFun_apply
    p F hF hdet X j

end Matrix
