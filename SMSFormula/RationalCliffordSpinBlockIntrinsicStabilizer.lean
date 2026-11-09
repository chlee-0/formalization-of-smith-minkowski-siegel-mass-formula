import SMSFormula.RationalCliffordGeneralSpinBlockIntrinsicRange

/-!
# Intrinsic Spin and GSpin stabilizer equivalences on a nonisotropic block

The exact pointwise range theorems are packaged here as multiplicative
equivalences onto the fixed-last-vector stabilizer subgroups.  The same
construction works over every commutative rational algebra and commutes with
arbitrary scalar extension.
-/

noncomputable section

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-- The intrinsic Spin subgroup fixing the added nonisotropic coordinate. -/
def nonisotropicLastComplementSpinStabilizerSubgroup
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A] :
    Subgroup
      ((W.nonisotropicLastExtension a ha).CliffordSpinIntrinsicPoint A) :=
  (W.nonisotropicLastComplementSpinPointHom a ha A).range

theorem mem_nonisotropicLastComplementSpinStabilizerSubgroup_iff
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (z : (W.nonisotropicLastExtension a ha).CliffordSpinIntrinsicPoint A) :
    z ∈ W.nonisotropicLastComplementSpinStabilizerSubgroup a ha A ↔
      W.IsNonisotropicLastBlockSpinFixedPoint a ha A z := by
  constructor
  · rintro ⟨x, rfl⟩
    exact W.nonisotropicLastComplementSpinPoint_fixesLastCoordinate a ha A x
  · intro hz
    have hpre :=
      W.existsUnique_nonisotropicLastComplementSpinPreimage_of_fixes
        a ha A z hz
    unfold HasUniqueNonisotropicLastComplementSpinPreimage at hpre
    rcases hpre with ⟨x, hx, _⟩
    exact ⟨x, hx⟩

/-- Exact multiplicative equivalence from lower intrinsic Spin to the
fixed-last-vector block stabilizer. -/
def nonisotropicLastComplementSpinStabilizerMulEquiv
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A] :
    W.CliffordSpinIntrinsicPoint A ≃*
      W.nonisotropicLastComplementSpinStabilizerSubgroup a ha A :=
  MonoidHom.ofInjective
    (f := W.nonisotropicLastComplementSpinPointHom a ha A)
    (W.nonisotropicLastComplementSpinPointHom_injective a ha A)

@[simp]
theorem coe_nonisotropicLastComplementSpinStabilizerMulEquiv
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (x : W.CliffordSpinIntrinsicPoint A) :
    (W.nonisotropicLastComplementSpinStabilizerMulEquiv a ha A x).1 =
      W.nonisotropicLastComplementSpinPoint a ha A x :=
  rfl

/-- The intrinsic GSpin subgroup fixing the added nonisotropic coordinate. -/
def nonisotropicLastComplementGeneralSpinStabilizerSubgroup
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A] :
    Subgroup
      ((W.nonisotropicLastExtension a ha).CliffordGeneralSpinIntrinsicPoint A) :=
  (W.nonisotropicLastComplementGeneralSpinPointHom a ha A).range

theorem mem_nonisotropicLastComplementGeneralSpinStabilizerSubgroup_iff
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (z : (W.nonisotropicLastExtension a ha).CliffordGeneralSpinIntrinsicPoint A) :
    z ∈ W.nonisotropicLastComplementGeneralSpinStabilizerSubgroup a ha A ↔
      W.IsNonisotropicLastBlockGeneralSpinFixedPoint a ha A z := by
  constructor
  · rintro ⟨x, rfl⟩
    exact W.nonisotropicLastComplementGeneralSpinPoint_fixesLastCoordinate
      a ha A x
  · intro hz
    have hpre :=
      W.existsUnique_nonisotropicLastComplementGeneralSpinPreimage_of_fixes
        a ha A z hz
    unfold HasUniqueNonisotropicLastComplementGeneralSpinPreimage at hpre
    rcases hpre with ⟨x, hx, _⟩
    exact ⟨x, hx⟩

/-- Exact multiplicative equivalence from lower intrinsic GSpin to the
fixed-last-vector block stabilizer. -/
def nonisotropicLastComplementGeneralSpinStabilizerMulEquiv
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A] :
    W.CliffordGeneralSpinIntrinsicPoint A ≃*
      W.nonisotropicLastComplementGeneralSpinStabilizerSubgroup a ha A :=
  MonoidHom.ofInjective
    (f := W.nonisotropicLastComplementGeneralSpinPointHom a ha A)
    (W.nonisotropicLastComplementGeneralSpinPointHom_injective a ha A)

@[simp]
theorem coe_nonisotropicLastComplementGeneralSpinStabilizerMulEquiv
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (x : W.CliffordGeneralSpinIntrinsicPoint A) :
    (W.nonisotropicLastComplementGeneralSpinStabilizerMulEquiv a ha A x).1 =
      W.nonisotropicLastComplementGeneralSpinPoint a ha A x :=
  rfl

/-- The Spin stabilizer equivalence has the certified represented block
action. -/
theorem nonisotropicLastComplementSpinStabilizerMulEquiv_toSpecialOrthogonal
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (x : W.CliffordSpinIntrinsicPoint A) :
    (W.nonisotropicLastExtension a ha).cliffordSpinIntrinsicPointToSpecialOrthogonalGroup A
        (W.nonisotropicLastComplementSpinStabilizerMulEquiv a ha A x).1 =
      W.nonisotropicLastCoordinateFiberEmbedHom a ha A
        (W.cliffordSpinIntrinsicPointToSpecialOrthogonalGroup A x) := by
  exact DFunLike.congr_fun
    (W.nonisotropicLastComplementSpinPointHom_toSpecialOrthogonal a ha A) x

/-- The GSpin stabilizer equivalence has the certified represented block
action. -/
theorem nonisotropicLastComplementGeneralSpinStabilizerMulEquiv_toSpecialOrthogonal
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (x : W.CliffordGeneralSpinIntrinsicPoint A) :
    CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom
        (W.nonisotropicLastExtension a ha) A
        (W.nonisotropicLastComplementGeneralSpinStabilizerMulEquiv a ha A x).1 =
      W.nonisotropicLastCoordinateFiberEmbedHom a ha A
        (CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom W A x) := by
  exact DFunLike.congr_fun
    (W.nonisotropicLastComplementGeneralSpinPointHom_toSpecialOrthogonal a ha A) x

/-- The GSpin stabilizer equivalence preserves similitude exactly. -/
@[simp]
theorem nonisotropicLastComplementGeneralSpinStabilizerMulEquiv_similitude
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (x : W.CliffordGeneralSpinIntrinsicPoint A) :
    CliffordGeneralSpinIntrinsicPoint.similitudeGroupHom
        (W.nonisotropicLastExtension a ha) A
        (W.nonisotropicLastComplementGeneralSpinStabilizerMulEquiv a ha A x).1 =
      CliffordGeneralSpinIntrinsicPoint.similitudeGroupHom W A x :=
  rfl

/-- The GSpin stabilizer equivalence preserves the intrinsic central scalar
inclusion. -/
@[simp]
theorem nonisotropicLastComplementGeneralSpinStabilizerMulEquiv_ofScalar
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A] (z : Aˣ) :
    (W.nonisotropicLastComplementGeneralSpinStabilizerMulEquiv a ha A
      (CliffordGeneralSpinIntrinsicPoint.ofScalar W A z)).1 =
        CliffordGeneralSpinIntrinsicPoint.ofScalar
          (W.nonisotropicLastExtension a ha) A z := by
  exact W.nonisotropicLastComplementGeneralSpinPoint_ofScalar a ha A z

/-- The GSpin stabilizer equivalence restricts to the Spin stabilizer
equivalence under the intrinsic `ofSpin` inclusion. -/
@[simp]
theorem nonisotropicLastComplementGeneralSpinStabilizerMulEquiv_ofSpin
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (x : W.CliffordSpinIntrinsicPoint A) :
    (W.nonisotropicLastComplementGeneralSpinStabilizerMulEquiv a ha A
      (CliffordGeneralSpinIntrinsicPoint.ofSpin W A
        (CliffordSpinIntrinsicPoint.toCandidatePointData W A x))).1 =
      CliffordGeneralSpinIntrinsicPoint.ofSpin
        (W.nonisotropicLastExtension a ha) A
        (CliffordSpinIntrinsicPoint.toCandidatePointData
          (W.nonisotropicLastExtension a ha) A
          (W.nonisotropicLastComplementSpinStabilizerMulEquiv a ha A x).1) := by
  exact W.nonisotropicLastComplementGeneralSpinPoint_ofSpin a ha A x

/-- Scalar extension maps the intrinsic Spin stabilizer subgroup to the
corresponding stabilizer subgroup. -/
def nonisotropicLastComplementSpinStabilizerMapGroupHom
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    {A B : Type*} [CommRing A] [CommRing B]
    [Algebra ℚ A] [Algebra ℚ B]
    (f : A →ₐ[ℚ] B) :
    W.nonisotropicLastComplementSpinStabilizerSubgroup a ha A →*
      W.nonisotropicLastComplementSpinStabilizerSubgroup a ha B where
  toFun z := ⟨
    (W.nonisotropicLastExtension a ha).cliffordSpinIntrinsicPointMap f z.1,
    by
      rcases z.2 with ⟨x, hx⟩
      refine ⟨W.cliffordSpinIntrinsicPointMap f x, ?_⟩
      calc
        W.nonisotropicLastComplementSpinPoint a ha B
            (W.cliffordSpinIntrinsicPointMap f x) =
          (W.nonisotropicLastExtension a ha).cliffordSpinIntrinsicPointMap f
            (W.nonisotropicLastComplementSpinPoint a ha A x) :=
              (W.nonisotropicLastComplementSpinPoint_naturality a ha f x).symm
        _ = (W.nonisotropicLastExtension a ha).cliffordSpinIntrinsicPointMap f z.1 :=
              congrArg
                ((W.nonisotropicLastExtension a ha).cliffordSpinIntrinsicPointMap f)
                hx ⟩
  map_one' := by
    apply Subtype.ext
    exact map_one
      ((W.nonisotropicLastExtension a ha).cliffordSpinIntrinsicPointMap f)
  map_mul' x y := by
    apply Subtype.ext
    exact map_mul
      ((W.nonisotropicLastExtension a ha).cliffordSpinIntrinsicPointMap f) x.1 y.1

/-- Scalar extension maps the intrinsic GSpin stabilizer subgroup to the
corresponding stabilizer subgroup. -/
def nonisotropicLastComplementGeneralSpinStabilizerMapGroupHom
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    {A B : Type*} [CommRing A] [CommRing B]
    [Algebra ℚ A] [Algebra ℚ B]
    (f : A →ₐ[ℚ] B) :
    W.nonisotropicLastComplementGeneralSpinStabilizerSubgroup a ha A →*
      W.nonisotropicLastComplementGeneralSpinStabilizerSubgroup a ha B where
  toFun z := ⟨
    CliffordGeneralSpinIntrinsicPoint.mapGroupHom
      (W.nonisotropicLastExtension a ha) f z.1,
    by
      rcases z.2 with ⟨x, hx⟩
      refine ⟨CliffordGeneralSpinIntrinsicPoint.mapGroupHom W f x, ?_⟩
      calc
        W.nonisotropicLastComplementGeneralSpinPoint a ha B
            (CliffordGeneralSpinIntrinsicPoint.mapGroupHom W f x) =
          CliffordGeneralSpinIntrinsicPoint.mapGroupHom
            (W.nonisotropicLastExtension a ha) f
            (W.nonisotropicLastComplementGeneralSpinPoint a ha A x) :=
              (W.nonisotropicLastComplementGeneralSpinPoint_naturality a ha f x).symm
        _ = CliffordGeneralSpinIntrinsicPoint.mapGroupHom
            (W.nonisotropicLastExtension a ha) f z.1 :=
              congrArg
                (CliffordGeneralSpinIntrinsicPoint.mapGroupHom
                  (W.nonisotropicLastExtension a ha) f)
                hx ⟩
  map_one' := by
    apply Subtype.ext
    exact map_one
      (CliffordGeneralSpinIntrinsicPoint.mapGroupHom
        (W.nonisotropicLastExtension a ha) f)
  map_mul' x y := by
    apply Subtype.ext
    exact map_mul
      (CliffordGeneralSpinIntrinsicPoint.mapGroupHom
        (W.nonisotropicLastExtension a ha) f) x.1 y.1

/-- Naturality of the Spin stabilizer equivalence. -/
@[simp]
theorem nonisotropicLastComplementSpinStabilizerMulEquiv_naturality
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    {A B : Type*} [CommRing A] [CommRing B]
    [Algebra ℚ A] [Algebra ℚ B]
    (f : A →ₐ[ℚ] B) (x : W.CliffordSpinIntrinsicPoint A) :
    W.nonisotropicLastComplementSpinStabilizerMapGroupHom a ha f
        (W.nonisotropicLastComplementSpinStabilizerMulEquiv a ha A x) =
      W.nonisotropicLastComplementSpinStabilizerMulEquiv a ha B
        (W.cliffordSpinIntrinsicPointMap f x) := by
  apply Subtype.ext
  exact W.nonisotropicLastComplementSpinPoint_naturality a ha f x

/-- Naturality of the GSpin stabilizer equivalence. -/
@[simp]
theorem nonisotropicLastComplementGeneralSpinStabilizerMulEquiv_naturality
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    {A B : Type*} [CommRing A] [CommRing B]
    [Algebra ℚ A] [Algebra ℚ B]
    (f : A →ₐ[ℚ] B) (x : W.CliffordGeneralSpinIntrinsicPoint A) :
    W.nonisotropicLastComplementGeneralSpinStabilizerMapGroupHom a ha f
        (W.nonisotropicLastComplementGeneralSpinStabilizerMulEquiv a ha A x) =
      W.nonisotropicLastComplementGeneralSpinStabilizerMulEquiv a ha B
        (CliffordGeneralSpinIntrinsicPoint.mapGroupHom W f x) := by
  apply Subtype.ext
  exact W.nonisotropicLastComplementGeneralSpinPoint_naturality a ha f x

end RationalQuadraticSpaceMatrix
