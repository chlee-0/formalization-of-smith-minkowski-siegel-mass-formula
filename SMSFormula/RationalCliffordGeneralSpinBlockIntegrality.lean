import SMSFormula.RationalCliffordCoordinateBasisMonomial
import SMSFormula.RationalCliffordGeneralSpinBlockIntrinsicPoint
import SMSFormula.RationalCliffordGeneralSpinPadicIntegralCoordinates
import SMSFormula.RationalCliffordGeneralSpinHorizontalFiniteSourceCylinder

/-!
# The block embedding preserves Clifford-coordinate integrality

Over any commutative rational algebra `A`, the coordinate complement Clifford map is the
base change of the rational Clifford map of the complement isometry.  Since the
coordinate basis over `A` is the base change of the rational one, the `A`-coordinates of the
image are those of the source moved to the `castSucc` index sets and zero elsewhere.  Applied
to the Clifford unit of a `GSpin` point and to its inverse, this gives, at every prime,

`IsIntegral_V(ι y) ⟺ IsIntegral_W(y)`.
-/

noncomputable section

open CliffordAlgebra PositiveDefiniteIntegralLattice
open scoped TensorProduct

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-- The coordinate complement map on pure tensors `1 ⊗ c`. -/
theorem nonisotropicLastComplementCoordinateCliffordMap_one_tmul
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A] (c : CliffordAlgebra W.quadraticForm) :
    W.nonisotropicLastComplementCoordinateCliffordMap a ha A (1 ⊗ₜ[ℚ] c) =
      1 ⊗ₜ[ℚ] CliffordAlgebra.map (W.nonisotropicLastComplementRationalIsometry a ha) c := by
  let F : CliffordAlgebra W.quadraticForm →ₐ[ℚ]
      (W.nonisotropicLastExtension a ha).cliffordCoordinateBaseChangeAlgebra A :=
    ((W.nonisotropicLastComplementCoordinateCliffordMap a ha A).restrictScalars ℚ).comp
      Algebra.TensorProduct.includeRight
  let G : CliffordAlgebra W.quadraticForm →ₐ[ℚ]
      (W.nonisotropicLastExtension a ha).cliffordCoordinateBaseChangeAlgebra A :=
    Algebra.TensorProduct.includeRight.comp
      (CliffordAlgebra.map (W.nonisotropicLastComplementRationalIsometry a ha))
  have hFG : F = G := by
    apply CliffordAlgebra.hom_ext
    apply LinearMap.ext
    intro v
    simp only [F, G, LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
      AlgHom.comp_apply, AlgHom.coe_restrictScalars', Algebra.TensorProduct.includeRight_apply,
      CliffordAlgebra.map_apply_ι]
    apply ((W.nonisotropicLastExtension a ha).commutativeTensorCliffordEquiv A).injective
    rw [commutativeTensorCliffordEquiv_nonisotropicLastComplementCoordinateCliffordMap,
      commutativeTensorCliffordEquiv_tmul_ι, commutativeTensorCliffordEquiv_tmul_ι,
      nonisotropicLastComplementCliffordMap_ι]
    congr 1
    funext j
    cases j using Fin.lastCases with
    | last =>
      change nonisotropicLastComplementInclude (fun i ↦ v i • (1 : A)) (Fin.last n) =
        nonisotropicLastComplementInclude v (Fin.last n) • (1 : A)
      simp [nonisotropicLastComplementInclude]
    | cast j =>
      change nonisotropicLastComplementInclude (fun i ↦ v i • (1 : A)) j.castSucc =
        nonisotropicLastComplementInclude v j.castSucc • (1 : A)
      simp [nonisotropicLastComplementInclude]
  have h := congrArg (fun φ ↦ φ c) hFG
  simpa [F, G] using h

/-- The coordinate complement map is a base change of the rational Clifford map. -/
theorem nonisotropicLastComplementCoordinateCliffordMap_eq_baseChange
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A] (x : W.cliffordCoordinateBaseChangeAlgebra A) :
    W.nonisotropicLastComplementCoordinateCliffordMap a ha A x =
      LinearMap.baseChange A
        (CliffordAlgebra.map (W.nonisotropicLastComplementRationalIsometry a ha)).toLinearMap x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r c =>
    rw [LinearMap.baseChange_tmul, show r ⊗ₜ[ℚ] c = r • ((1 : A) ⊗ₜ[ℚ] c) by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], map_smul,
      nonisotropicLastComplementCoordinateCliffordMap_one_tmul, TensorProduct.smul_tmul',
      smul_eq_mul, mul_one]
    rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- Coordinates over `A` are padded: the `A`-coordinates of the image are those of the source
moved to the `castSucc` index sets. -/
theorem cliffordCoordinateBaseChangeBasis_repr_complementCoordinateCliffordMap
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A] (x : W.cliffordCoordinateBaseChangeAlgebra A) :
    ((W.nonisotropicLastExtension a ha).cliffordCoordinateBaseChangeBasis A).repr
        (W.nonisotropicLastComplementCoordinateCliffordMap a ha A x) =
      Finsupp.mapDomain (fun s ↦ s.map (Fin.castSuccOrderEmb (n := n)).toEmbedding)
        ((W.cliffordCoordinateBaseChangeBasis A).repr x) := by
  have hlin : (((W.nonisotropicLastExtension a ha).cliffordCoordinateBaseChangeBasis A).repr.toLinearMap ∘ₗ
      LinearMap.baseChange A
        (CliffordAlgebra.map (W.nonisotropicLastComplementRationalIsometry a ha)).toLinearMap) =
      (Finsupp.lmapDomain A A (fun s ↦ s.map (Fin.castSuccOrderEmb (n := n)).toEmbedding)) ∘ₗ
        (W.cliffordCoordinateBaseChangeBasis A).repr.toLinearMap := by
    apply (W.cliffordCoordinateBaseChangeBasis A).ext
    intro s
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      cliffordCoordinateBaseChangeBasis_apply, LinearMap.baseChange_tmul, AlgHom.toLinearMap_apply,
      map_complementRationalIsometry_cliffordCoordinateBasis, Finsupp.lmapDomain_apply]
    rw [← cliffordCoordinateBaseChangeBasis_apply, ← cliffordCoordinateBaseChangeBasis_apply,
      Module.Basis.repr_self, Module.Basis.repr_self, Finsupp.mapDomain_single]
  rw [nonisotropicLastComplementCoordinateCliffordMap_eq_baseChange]
  exact LinearMap.congr_fun hlin x

/-- Padded families take values in a subring exactly when the source family does. -/
theorem forall_mapDomain_mem_iff {A : Type*} [CommRing A] (R : Subring A)
    (f : Finset (Fin n) → Finset (Fin (n + 1))) (hf : Function.Injective f)
    (c : Finset (Fin n) →₀ A) :
    (∀ t, Finsupp.mapDomain f c t ∈ R) ↔ ∀ s, c s ∈ R := by
  constructor
  · intro h s
    have := h (f s)
    rwa [Finsupp.mapDomain_apply hf] at this
  · intro h t
    by_cases ht : t ∈ Set.range f
    · obtain ⟨s, rfl⟩ := ht
      rw [Finsupp.mapDomain_apply hf]
      exact h s
    · rw [Finsupp.mapDomain_notin_range _ _ ht]
      exact R.zero_mem

/-- A fixed-last block matrix has entries in a subring exactly when its lower block does. -/
theorem fixLastBlockMatrix_entries_mem_iff {R : Type*} [CommRing R] (S : Subring R)
    (M : Matrix (Fin n) (Fin n) R) :
    (∀ i j, fixLastBlockMatrix M i j ∈ S) ↔ ∀ i j, M i j ∈ S := by
  constructor
  · intro h i j
    have := h i.castSucc j.castSucc
    rwa [fixLastBlockMatrix, nonisotropicLastBlockMatrix_castSucc_castSucc] at this
  · intro h i j
    refine Fin.lastCases ?_ (fun i ↦ ?_) i <;> refine Fin.lastCases ?_ (fun j ↦ ?_) j
    · simp [fixLastBlockMatrix, nonisotropicLastBlockMatrix_last_last, S.one_mem]
    · simp [fixLastBlockMatrix, nonisotropicLastBlockMatrix_last_castSucc, S.zero_mem]
    · simp [fixLastBlockMatrix, nonisotropicLastBlockMatrix_castSucc_last, S.zero_mem]
    · rw [fixLastBlockMatrix, nonisotropicLastBlockMatrix_castSucc_castSucc]; exact h i j

/-- The block `SO` embedding preserves `SO`-integrality in both directions. -/
theorem nonisotropicLastCoordinateFiberEmbedGroup_mem_padicSpecialOrthogonalIntegralSubgroup_iff
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) (p : ℕ) [Fact p.Prime]
    (h : W.specialOrthogonalMatrixGroup ℚ_[p]) :
    W.nonisotropicLastCoordinateFiberEmbedGroup a ha ℚ_[p] h ∈
        (W.nonisotropicLastExtension a ha).padicSpecialOrthogonalIntegralSubgroup p ↔
      h ∈ W.padicSpecialOrthogonalIntegralSubgroup p := by
  have hinv : ((W.nonisotropicLastCoordinateFiberEmbedGroup a ha ℚ_[p] h).1.1⁻¹).1 =
      fixLastBlockMatrix ((h.1.1⁻¹).1) := by
    have := congrArg (fun g : (W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroup ℚ_[p] ↦
      g.1.1.1) (map_inv (W.nonisotropicLastCoordinateFiberEmbedHom a ha ℚ_[p]) h)
    exact this.symm
  rw [mem_padicSpecialOrthogonalIntegralSubgroup_iff, mem_padicSpecialOrthogonalIntegralSubgroup_iff,
    hinv, coe_nonisotropicLastCoordinateFiberEmbedGroup, fixLastBlockMatrix_entries_mem_iff,
    fixLastBlockMatrix_entries_mem_iff]

/-- The block embedding preserves integrality at every prime, in both directions. -/
theorem padicCliffordGeneralSpinIsIntegral_nonisotropicLastComplementGeneralSpinPoint_iff
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) (p : ℕ) [Fact p.Prime]
    (y : W.PadicCliffordGeneralSpinGroup p) :
    (W.nonisotropicLastExtension a ha).PadicCliffordGeneralSpinIsIntegral p
        (W.nonisotropicLastComplementGeneralSpinPoint a ha ℚ_[p] y) ↔
      W.PadicCliffordGeneralSpinIsIntegral p y := by
  have hinj : Function.Injective
      (fun s : Finset (Fin n) ↦ s.map (Fin.castSuccOrderEmb (n := n)).toEmbedding) :=
    Finset.map_injective _
  unfold PadicCliffordGeneralSpinIsIntegral
  have hunit : ((W.nonisotropicLastComplementGeneralSpinPoint a ha ℚ_[p] y).cliffordUnit :
      (W.nonisotropicLastExtension a ha).cliffordCoordinateBaseChangeAlgebra ℚ_[p]) =
      W.nonisotropicLastComplementCoordinateCliffordMap a ha ℚ_[p]
        (y.cliffordUnit : W.cliffordCoordinateBaseChangeAlgebra ℚ_[p]) := rfl
  have hinv : (((W.nonisotropicLastComplementGeneralSpinPoint a ha ℚ_[p] y).cliffordUnit⁻¹ :
      ((W.nonisotropicLastExtension a ha).cliffordCoordinateBaseChangeAlgebra ℚ_[p])ˣ) :
      (W.nonisotropicLastExtension a ha).cliffordCoordinateBaseChangeAlgebra ℚ_[p]) =
      W.nonisotropicLastComplementCoordinateCliffordMap a ha ℚ_[p]
        ((y.cliffordUnit⁻¹ : (W.cliffordCoordinateBaseChangeAlgebra ℚ_[p])ˣ) :
          W.cliffordCoordinateBaseChangeAlgebra ℚ_[p]) := rfl
  rw [hunit, hinv, cliffordCoordinateBaseChangeBasis_repr_complementCoordinateCliffordMap,
    cliffordCoordinateBaseChangeBasis_repr_complementCoordinateCliffordMap,
    forall_mapDomain_mem_iff _ _ hinj, forall_mapDomain_mem_iff _ _ hinj,
    nonisotropicLastComplementGeneralSpinPoint_similitude,
    nonisotropicLastComplementGeneralSpinPoint_matrixGroup,
    nonisotropicLastCoordinateFiberEmbedGroup_mem_padicSpecialOrthogonalIntegralSubgroup_iff]

local instance blockIntegralityDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance blockIntegralityPrimeFact (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

/-- The cylinder pullback with `hint` discharged: with equal exceptional sets, the block
embedding pulls the `V` source cylinder over `(s_v)` back to the `W` source cylinder over
`(ι_v⁻¹ s_v)`. -/
theorem preimage_nonisotropicLastComplementGeneralSpinPoint_sourceCylinder_of_eq
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hE : S ∪ (W.nonisotropicLastExtension a ha).cliffordGeneralSpinHorizontalIntegralBadPlaces =
      S ∪ W.cliffordGeneralSpinHorizontalIntegralBadPlaces)
    (s : ∀ v : {v // v ∈ S ∪
        (W.nonisotropicLastExtension a ha).cliffordGeneralSpinHorizontalIntegralBadPlaces},
      Set ((W.nonisotropicLastExtension a ha).HeightOnePadicCliffordGeneralSpinGroup v.1)) :
    W.nonisotropicLastComplementGeneralSpinPoint a ha RationalFiniteAdele ⁻¹'
        (W.nonisotropicLastExtension a ha).cliffordGeneralSpinHorizontalSourceCylinder S s =
      W.cliffordGeneralSpinHorizontalSourceCylinder S
        (fun v ↦ W.nonisotropicLastComplementGeneralSpinPoint a ha _ ⁻¹'
          s ⟨v.1, by rw [hE]; exact v.2⟩) :=
  W.preimage_nonisotropicLastComplementGeneralSpinPoint_sourceCylinder a ha S hE
    (fun _v _ y ↦ W.padicCliffordGeneralSpinIsIntegral_nonisotropicLastComplementGeneralSpinPoint_iff
      a ha _ y) s

end RationalQuadraticSpaceMatrix
