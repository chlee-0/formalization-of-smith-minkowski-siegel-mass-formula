import SMSFormula.QuadraticPadicCayleyProductGroupHaar

/-! The product source measure is the repository lower skew-adjoint coordinate
measure times the unit-cube Haar on the supplied horizontal coefficients. The
proof stays on coordinate spaces `Fin k → Q_p`: the product of unit-cube
Haar measures is unit-cube Haar on the disjoint-sum coordinates, and the
source coordinates are the lower coordinates on the first block and the
identity on the second. No Haar normalization is chosen. -/
noncomputable section
open MeasureTheory Matrix PositiveDefiniteIntegralLattice Metric Set
open scoped Matrix.Norms.Operator ENNReal NNReal Topology

namespace Padic
variable (p : ℕ) [Fact (Nat.Prime p)]

local instance sourceHaarPadicMeasurableSpace : MeasurableSpace ℚ_[p] := borel _
local instance sourceHaarPadicBorelSpace : BorelSpace ℚ_[p] := ⟨rfl⟩

/-- The product of unit-cube Haar measures is unit-cube Haar on disjoint-sum
coordinates `x ↦ Sum.elim x.1 x.2`. -/
theorem map_sumElim_prod_unitHaar (α β : Type*) [Fintype α] [Fintype β] :
    ((unitHaar p α).prod (unitHaar p β)).map
        (fun x : (α → ℚ_[p]) × (β → ℚ_[p]) ↦ (Sum.elim x.1 x.2 : α ⊕ β → ℚ_[p])) =
      unitHaar p (α ⊕ β) := by
  let e : (α → ℚ_[p]) × (β → ℚ_[p]) ≃+ (α ⊕ β → ℚ_[p]) :=
    (LinearEquiv.sumArrowLequivProdArrow α β ℚ_[p] ℚ_[p]).symm.toAddEquiv
  have he : ⇑e = fun x : (α → ℚ_[p]) × (β → ℚ_[p]) ↦ (Sum.elim x.1 x.2 : α ⊕ β → ℚ_[p]) := by
    funext x k; cases k <;> rfl
  have hcont : Continuous e := by
    rw [he]; exact (Homeomorph.sumArrowHomeomorphProdArrow (X := ℚ_[p]) (ι := α) (ι' := β)).symm.continuous
  have hcont' : Continuous e.symm :=
    (Homeomorph.sumArrowHomeomorphProdArrow (X := ℚ_[p]) (ι := α) (ι' := β)).continuous
  haveI : SigmaCompactSpace (α → ℚ_[p]) := inferInstance
  haveI : SFinite (unitHaar p α) := inferInstance
  haveI : SFinite (unitHaar p β) := inferInstance
  haveI : MeasurableAdd (α → ℚ_[p]) := inferInstance
  haveI : MeasurableAdd (β → ℚ_[p]) := inferInstance
  haveI : ((unitHaar p α).prod (unitHaar p β)).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  haveI : (((unitHaar p α).prod (unitHaar p β)).map e).IsAddHaarMeasure :=
    e.isAddHaarMeasure_map _ hcont hcont'
  rw [← he]
  apply eq_unitHaar_of_unitCube
  rw [Measure.map_apply hcont.measurable isClosed_closedBall.measurableSet]
  have hpre : (e : (α → ℚ_[p]) × (β → ℚ_[p]) → (α ⊕ β → ℚ_[p])) ⁻¹'
      closedBall 0 1 = closedBall (0 : α → ℚ_[p]) 1 ×ˢ closedBall (0 : β → ℚ_[p]) 1 := by
    rw [he]
    ext ⟨x, c⟩
    simp only [mem_preimage, mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one,
      mem_prod, Sum.forall, Sum.elim_inl, Sum.elim_inr]
  rw [hpre, Measure.prod_prod, unitHaar_unitCube, unitHaar_unitCube, one_mul]

end Padic

/-- The repository coordinate equivalence is the basis coordinate map. -/
theorem _root_.Matrix.skewAdjointPadicCoordinateEquiv_apply_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (y : (skewAdjointMatricesLieSubalgebra (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
    skewAdjointPadicCoordinateEquiv F p y =
      (skewAdjointScalarExtensionFinBasis (K := ℚ_[p]) F).equivFun y := rfl

theorem _root_.Matrix.skewAdjointPadicCoordinateEquiv_symm_apply_eq {ι : Type*} [Fintype ι]
    [DecidableEq ι] (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (x : Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F)) → ℚ_[p]) :
    (skewAdjointPadicCoordinateEquiv F p).symm x =
      (skewAdjointScalarExtensionFinBasis (K := ℚ_[p]) F).equivFun.symm x := rfl

namespace RationalQuadraticSpaceMatrix
variable {n : ℕ} (W : RationalQuadraticSpaceMatrix n) (p : ℕ) [Fact (Nat.Prime p)]

section SourceHaar

local instance sourceHaarPadicMeasurableSpace' : MeasurableSpace ℚ_[p] := borel _
local instance sourceHaarPadicBorelSpace' : BorelSpace ℚ_[p] := ⟨rfl⟩
local instance sourceHaarLowerMeasurableSpace :
    MeasurableSpace (skewAdjointMatricesLieSubalgebra (W.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _
local instance sourceHaarLowerBorelSpace :
    BorelSpace (skewAdjointMatricesLieSubalgebra (W.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩
local instance sourceHaarLowerLieMeasurableSpace :
    MeasurableSpace (skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p])) :=
  borel _
local instance sourceHaarLowerLieBorelSpace :
    BorelSpace (skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p])) :=
  ⟨rfl⟩

/-- The repository lower coordinate measure is the unit-cube Haar pulled back by
the lower coordinates. -/
theorem skewAdjointPadicCoordinateMeasure_eq_map_unitHaar :
    skewAdjointPadicCoordinateMeasure W.pairingMatrix p =
      (Padic.unitHaar p (Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra W.pairingMatrix)))).map
        (skewAdjointPadicCoordinateEquiv W.pairingMatrix p).symm := by
  rw [← Matrix.map_skewAdjointPadicCoordinateMeasure W.pairingMatrix p,
    Measure.map_map (skewAdjointPadicCoordinateEquiv W.pairingMatrix p).symm.continuous.measurable
      (skewAdjointPadicCoordinateEquiv W.pairingMatrix p).continuous.measurable]
  have hid : ((skewAdjointPadicCoordinateEquiv W.pairingMatrix p).symm ∘
      (skewAdjointPadicCoordinateEquiv W.pairingMatrix p)) = id :=
    funext fun x ↦ (skewAdjointPadicCoordinateEquiv W.pairingMatrix p).symm_apply_apply x
  rw [hid, Measure.map_id]

set_option backward.isDefEq.respectTransparency false in
/-- The source coordinates, precomposed with the inverse lower coordinates on
the first block, are the disjoint-sum identification. -/
theorem lastCayleyProductSourceCoordinates_prodMap :
    (fun x : (Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra W.pairingMatrix)) → ℚ_[p]) ×
        (Fin n → ℚ_[p]) ↦
      W.lastCayleyProductSourceCoordinates p
        ((skewAdjointPadicCoordinateEquiv W.pairingMatrix p).symm x.1, x.2)) =
      (fun x ↦ (Sum.elim x.1 x.2 :
        Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra W.pairingMatrix)) ⊕ Fin n → ℚ_[p])) := by
  funext x k
  let b := skewAdjointScalarExtensionFinBasis (K := ℚ_[p]) W.pairingMatrix
  let c := Pi.basisFun ℚ_[p] (Fin n)
  change (b.prod c).equivFun (b.equivFun.symm x.1, x.2) k =
    (Sum.elim x.1 x.2) k
  rw [Module.Basis.equivFun_apply]
  cases k with
  | inl i =>
    rw [Module.Basis.prod_repr_inl]
    change b.repr (b.equivFun.symm x.1) i = x.1 i
    rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  | inr j =>
    rw [Module.Basis.prod_repr_inr]
    change (Pi.basisFun ℚ_[p] (Fin n)).repr x.2 j = x.2 j
    rw [Pi.basisFun_repr]

set_option backward.isDefEq.respectTransparency false in
/-- The product source measure is the repository lower skew-adjoint coordinate
measure times the unit-cube Haar on the supplied horizontal coefficients. -/
theorem lastCayleyProductSourceMeasure_eq_repository :
    W.lastCayleyProductSourceMeasure p =
      (skewAdjointPadicCoordinateMeasure W.pairingMatrix p).prod (Padic.unitHaar p (Fin n)) := by
  set eW := skewAdjointPadicCoordinateEquiv W.pairingMatrix p with heW
  set eE := W.lastCayleyProductSourceCoordinates p with heE
  rw [W.skewAdjointPadicCoordinateMeasure_eq_map_unitHaar p]
  rw [show Padic.unitHaar p (Fin n) = (Padic.unitHaar p (Fin n)).map id from (Measure.map_id).symm]
  rw [Measure.map_prod_map _ _ eW.symm.continuous.measurable measurable_id]
  rw [lastCayleyProductSourceMeasure, ← Padic.map_sumElim_prod_unitHaar p,
    ← W.lastCayleyProductSourceCoordinates_prodMap p,
    Measure.map_map (g := eE.symm)
      (f := fun x : (Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra W.pairingMatrix)) → ℚ_[p]) ×
        (Fin n → ℚ_[p]) ↦ eE (eW.symm x.1, x.2)) eE.symm.continuous.measurable
      (eE.continuous.measurable.comp (eW.symm.continuous.measurable.prodMap measurable_id))]
  congr 1
  funext x
  change eE.symm (eE (eW.symm x.1, x.2)) = (eW.symm x.1, x.2)
  rw [ContinuousLinearEquiv.symm_apply_apply]

end SourceHaar

section GroupHaarRepository

variable (a : ℚ) (ha : a ≠ 0)

local instance ghrPadicMeasurableSpace : MeasurableSpace ℚ_[p] := borel _
local instance ghrPadicBorelSpace : BorelSpace ℚ_[p] := ⟨rfl⟩
local instance ghrSkewMeasurableSpace (F : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) :
    MeasurableSpace (skewAdjointMatricesLieSubalgebra (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _
local instance ghrSkewBorelSpace (F : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) :
    BorelSpace (skewAdjointMatricesLieSubalgebra (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩
local instance ghrLowerMeasurableSpace :
    MeasurableSpace (skewAdjointMatricesLieSubalgebra (W.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _
local instance ghrLowerBorelSpace :
    BorelSpace (skewAdjointMatricesLieSubalgebra (W.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩
local instance ghrGroupMeasurableSpace (F : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) :
    MeasurableSpace (specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℚ_[p]))) :=
  borel _
local instance ghrGroupBorelSpace (F : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) :
    BorelSpace (specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℚ_[p]))) :=
  ⟨rfl⟩
local instance ghrLowerLieMeasurableSpace :
    MeasurableSpace (skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p])) :=
  borel _
local instance ghrLowerLieBorelSpace :
    BorelSpace (skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p])) :=
  ⟨rfl⟩
local instance ghrHigherLieMeasurableSpace :
    MeasurableSpace (skewAdjointMatricesLieSubalgebra
      ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p])) :=
  borel _
local instance ghrHigherLieBorelSpace :
    BorelSpace (skewAdjointMatricesLieSubalgebra
      ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p])) :=
  ⟨rfl⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℚ_[p] E]
    (S : E → Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p])
    (dS : E →L[ℚ_[p]] Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p])
    (z : E) (hSs : HasStrictFDerivAt S dS z)
    (hSO : ∀ᶠ u in 𝓝 z, S u ∈ specialOrthogonalMatrixSet
      ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p]))
    (Y : skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p]))
    (hY : Y ∈ skewAdjointPadicCayleySource W.pairingMatrix p)
    (X : skewAdjointMatricesLieSubalgebra
      ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p]))
    (hX : X ∈ skewAdjointPadicCayleySource (W.nonisotropicLastExtension a ha).pairingMatrix p)
    (hproduct : S z * fixLastBlockMatrix (skewAdjointPadicCayleyForwardMatrix W.pairingMatrix p Y) =
      skewAdjointPadicCayleyForwardMatrix (W.nonisotropicLastExtension a ha).pairingMatrix p X)
    (v : Fin n → E)
    (hs : ((W.nonisotropicLastExtension a ha).cayleyOrbitVectorEquiv p X hX
      lastCoordinateVector) (Fin.last n) ≠ 0)
    (hv : (Pi.basisFun ℚ_[p] (Fin n)).det
      (fun i j ↦ (dS (v i) *ᵥ lastCoordinateVector) j.castSucc) ≠ 0)

include hs hv in
/-- Relative fiber product on the group, both sides in repository measures: the
repository group-Haar lintegral over the Cayley image of a small exact compact
open coordinate ball equals |r| · |orbit-relative| times the lintegral against
(repository lower coordinate measure weighted by the lower Cayley density) ×
(unit-cube Haar on the supplied horizontal coefficients). -/
theorem lastCayleyProduct_exists_forall_lintegral_groupHaar_repository :
    ∃ δ > 0, ∀ r : ℝ, 0 < r → r < δ →
      W.lastCayleyProductFrameValue a ha p S z v ''
          ((W.lastCayleyProductSourceCoordinates p) ⁻¹'
            closedBall (W.lastCayleyProductSourceCoordinates p (Y,0)) r) ⊆
        skewAdjointPadicCayleySource (W.nonisotropicLastExtension a ha).pairingMatrix p ∧
      Set.InjOn (W.lastCayleyProductFrameValue a ha p S z v)
        ((W.lastCayleyProductSourceCoordinates p) ⁻¹'
          closedBall (W.lastCayleyProductSourceCoordinates p (Y,0)) r) ∧
      ∀ G : specialFormPreservingMatrixSubgroup
          ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])) → ℝ≥0∞,
        ∫⁻ x in Subtype.val '' (skewAdjointPadicCayleyTranslatedHomeomorph
              (W.nonisotropicLastExtension a ha).pairingMatrix p
              (W.nonisotropicLastExtension a ha).form_det_ne_zero 1 ''
            (Subtype.val ⁻¹' (W.lastCayleyProductFrameValue a ha p S z v ''
              ((W.lastCayleyProductSourceCoordinates p) ⁻¹'
                closedBall (W.lastCayleyProductSourceCoordinates p (Y,0)) r)))),
            G x ∂(padicCayleySpecialOrthogonalDifferentialMeasure p (n+1)
              (W.nonisotropicLastExtension a ha).pairingMatrix
              (W.nonisotropicLastExtension a ha).form_det_ne_zero) =
          (‖W.lastOrbitGaugeRatio a ha ℚ_[p]‖₊ : ℝ≥0∞) *
            (‖(W.nonisotropicLastExtension a ha).cayleyOrbitRelativeTopForm p X hX
              lastCoordinateVector
              (by rw [W.nonisotropicLastExtension_quadratic_last]; exact (map_ne_zero _).mpr ha)
              (fun j ↦ W.lastCayleyProductIntrinsicDerivative a ha p S dS z hSs.hasFDerivAt hSO
                Y hY X hX hproduct (0, v j))‖₊ : ℝ≥0∞) *
            ∫⁻ q in (W.lastCayleyProductSourceCoordinates p) ⁻¹'
                closedBall (W.lastCayleyProductSourceCoordinates p (Y,0)) r,
              skewAdjointPadicCayleyAmbientDensity p n W.pairingMatrix q.1 *
                W.lastCayleyChartPullback a ha p G (W.lastCayleyProductFrameValue a ha p S z v q)
                ∂((skewAdjointPadicCoordinateMeasure W.pairingMatrix p).prod (Padic.unitHaar p (Fin n))) := by
  rw [← W.lastCayleyProductSourceMeasure_eq_repository p]
  exact W.lastCayleyProduct_exists_forall_lintegral_groupHaar a ha p S dS z hSs hSO Y hY X hX
    hproduct v hs hv

end GroupHaarRepository

end RationalQuadraticSpaceMatrix
