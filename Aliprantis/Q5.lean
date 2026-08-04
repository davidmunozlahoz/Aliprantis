import Aliprantis.Q4
import BanLat.OrderDense

open scoped Topology

namespace Aliprantis.Question5

open UniformSpace
open Filter
open Aliprantis.Question3

/-! ## Proposition 6.2 in the concrete completion -/

/-- The continuous-function lattice reused from Section 4 of the paper. -/
abbrev Q5Space := C(ℝ, ℝ)

/-- Rational points, regarded as the complement of the irrational set, are
dense in `ℝ`. -/
theorem dense_compl_irrationalSet : Dense irrationalSetᶜ := by
  apply Rat.denseRange_cast.mono
  rintro x ⟨q, rfl⟩
  exact Rat.not_irrational q

/-- Urysohn's lemma supplies the positive bump used in Proposition 6.2.
If every member of a positive family is uniformly bounded below on one
nonempty open set, then the family has a strictly positive continuous lower
bound. -/
theorem exists_positive_bump_lowerBound
    {F : Set Q5Space} (hF_nonneg : ∀ f ∈ F, 0 ≤ f)
    {V : Set ℝ} (hV_open : IsOpen V) (hV_nonempty : V.Nonempty)
    {c : ℝ} (hc_pos : 0 < c)
    (hF_ge : ∀ f ∈ F, ∀ x ∈ V, c ≤ f x) :
    ∃ φ : Q5Space, 0 < φ ∧ φ ∈ lowerBounds F := by
  obtain ⟨t, htV⟩ := hV_nonempty
  obtain ⟨b, hb_one, hb_zero, _hb_compact, hb_range⟩ :=
    exists_continuous_one_zero_of_isCompact
      (isCompact_singleton : IsCompact ({t} : Set ℝ))
      hV_open.isClosed_compl
      (Set.disjoint_singleton_left.mpr (by simpa using htV))
  let φ : Q5Space := c • b
  have hφ_nonneg : 0 ≤ φ := by
    rw [ContinuousMap.le_def]
    intro x
    change 0 ≤ c * b x
    exact mul_nonneg hc_pos.le (hb_range x).1
  have hφ_ne : φ ≠ 0 := by
    intro hzero
    have := DFunLike.congr_fun hzero t
    simp [φ, hb_one (Set.mem_singleton t), hc_pos.ne'] at this
  refine ⟨φ, lt_of_le_of_ne hφ_nonneg (Ne.symm hφ_ne), ?_⟩
  intro f hf
  rw [ContinuousMap.le_def]
  intro x
  by_cases hxV : x ∈ V
  · change c * b x ≤ f x
    exact (mul_le_of_le_one_right hc_pos.le (hb_range x).2).trans
      (hF_ge f hf x hxV)
  · have hb0 : b x = 0 := hb_zero hxV
    simp [φ, hb0]
    exact (ContinuousMap.le_def.mp (hF_nonneg f hf)) x

/-- A strictly positive common lower bound in `Cₖ(P ⊔ Q)` forces a
strictly positive common lower bound already in `C(ℝ)`. This packages the
density argument at the heart of the regularity part of Proposition 6.2. -/
theorem exists_positive_source_lowerBound
    {F : Set Q5Space} (hF_nonneg : ∀ f ∈ F, 0 ≤ f)
    {h : IrrationalPartitionFunctions} (hh_pos : 0 < h)
    (hh_lower : h ∈
      lowerBounds (partitionRestriction irrationalSet '' F)) :
    ∃ φ : Q5Space, 0 < φ ∧ φ ∈ lowerBounds F := by
  have hexists : ∃ z : PartitionSum ℝ irrationalSet, 0 < h z := by
    by_contra hnone
    push Not at hnone
    have hle : h ≤ 0 :=
      ContinuousMap.le_def.mpr fun z => hnone z
    exact (not_lt_of_ge hle) hh_pos
  obtain ⟨z, hz_pos⟩ := hexists
  cases z with
  | inl p =>
      let c : ℝ := h (Sum.inl p) / 2
      have hc_pos : 0 < c := by
        dsimp [c]
        exact half_pos hz_pos
      have hc_lt : c < h (Sum.inl p) := by
        dsimp [c]
        exact half_lt_self_iff.mpr hz_pos
      let W : Set irrationalSet := {r | c < h (Sum.inl r)}
      have hW_open : IsOpen W :=
        isOpen_lt continuous_const (h.continuous.comp continuous_inl)
      have hpW : p ∈ W := hc_lt
      obtain ⟨V, hV_open, hWV⟩ := isOpen_induced_iff.mp hW_open
      have hpV : (p : ℝ) ∈ V := by
        have : p ∈ Subtype.val ⁻¹' V := by
          rw [hWV]
          exact hpW
        exact this
      apply exists_positive_bump_lowerBound hF_nonneg hV_open ⟨p, hpV⟩ hc_pos
      intro f hf x hxV
      apply Aliprantis.Question4.continuous_ge_of_dense_of_mem_open
        dense_irrational hV_open hxV f.continuous
      intro y hy_irr hyV
      let py : irrationalSet := ⟨y, hy_irr⟩
      have hpyW : py ∈ W := by
        rw [← hWV]
        exact hyV
      have hhf : h ≤ partitionRestriction irrationalSet f :=
        hh_lower ⟨f, hf, rfl⟩
      exact (show c < h (Sum.inl py) from hpyW).le.trans
        ((ContinuousMap.le_def.mp hhf) (Sum.inl py))
  | inr q =>
      let c : ℝ := h (Sum.inr q) / 2
      have hc_pos : 0 < c := by
        dsimp [c]
        exact half_pos hz_pos
      have hc_lt : c < h (Sum.inr q) := by
        dsimp [c]
        exact half_lt_self_iff.mpr hz_pos
      let W : Set (irrationalSetᶜ : Set ℝ) := {r | c < h (Sum.inr r)}
      have hW_open : IsOpen W :=
        isOpen_lt continuous_const (h.continuous.comp continuous_inr)
      have hqW : q ∈ W := hc_lt
      obtain ⟨V, hV_open, hWV⟩ := isOpen_induced_iff.mp hW_open
      have hqV : (q : ℝ) ∈ V := by
        have : q ∈ Subtype.val ⁻¹' V := by
          rw [hWV]
          exact hqW
        exact this
      apply exists_positive_bump_lowerBound hF_nonneg hV_open ⟨q, hqV⟩ hc_pos
      intro f hf x hxV
      apply Aliprantis.Question4.continuous_ge_of_dense_of_mem_open
        dense_compl_irrationalSet hV_open hxV f.continuous
      intro y hy_rat hyV
      let qy : (irrationalSetᶜ : Set ℝ) := ⟨y, hy_rat⟩
      have hqyW : qy ∈ W := by
        rw [← hWV]
        exact hyV
      have hhf : h ≤ partitionRestriction irrationalSet f :=
        hh_lower ⟨f, hf, rfl⟩
      exact (show c < h (Sum.inr qy) from hqyW).le.trans
        ((ContinuousMap.le_def.mp hhf) (Sum.inr qy))

/-- The zero-infimum formulation of the regularity argument in Proposition
6.2. -/
theorem irrationalRestriction_preserves_zero_glb
    {F : Set Q5Space} (hF_nonneg : ∀ f ∈ F, 0 ≤ f)
    (hF_glb : IsGLB F 0) :
    IsGLB (partitionRestriction irrationalSet '' F)
      (0 : IrrationalPartitionFunctions) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨f, hf, rfl⟩
    exact (partitionRestriction irrationalSet).map_nonneg
      (hF_nonneg f hf)
  · intro h hh_lower
    by_contra hh_not_le
    let k : IrrationalPartitionFunctions := h ⊔ 0
    have hk_nonneg : 0 ≤ k := le_sup_right
    have hk_ne : k ≠ 0 := by
      intro hk_zero
      apply hh_not_le
      calc
        h ≤ k := le_sup_left
        _ = 0 := hk_zero
    have hk_pos : 0 < k := lt_of_le_of_ne hk_nonneg (Ne.symm hk_ne)
    have hk_lower : k ∈
        lowerBounds (partitionRestriction irrationalSet '' F) := by
      rintro _ ⟨f, hf, rfl⟩
      apply sup_le
      · exact hh_lower ⟨f, hf, rfl⟩
      · exact (partitionRestriction irrationalSet).map_nonneg
          (hF_nonneg f hf)
    obtain ⟨φ, hφ_pos, hφ_lower⟩ :=
      exists_positive_source_lowerBound hF_nonneg hk_pos hk_lower
    have hφ_le : φ ≤ 0 := hF_glb.2 hφ_lower
    exact (not_lt_of_ge hφ_le) hφ_pos

/-- The restriction embedding `J : C(ℝ) → Cₖ(P ⊔ Q)` is regular. -/
theorem irrationalRestriction_rightOrdContinuous :
    RightOrdContinuous (partitionRestriction irrationalSet :
      Q5Space → IrrationalPartitionFunctions) := by
  intro s x hsx
  let F : Set Q5Space := (fun f => f - x) '' s
  have hF_nonneg : ∀ f ∈ F, 0 ≤ f := by
    rintro _ ⟨f, hf, rfl⟩
    exact sub_nonneg.mpr (hsx.1 hf)
  have hF_glb : IsGLB F 0 := by
    refine ⟨hF_nonneg, ?_⟩
    intro z hz
    have hzx_lower : z + x ∈ lowerBounds s := by
      intro f hf
      have hz_le : z ≤ f - x := hz ⟨f, hf, rfl⟩
      exact (le_sub_iff_add_le).mp hz_le
    have := hsx.2 hzx_lower
    exact (add_le_add_iff_right x).mp (by simpa [add_comm] using this)
  have hzero := irrationalRestriction_preserves_zero_glb hF_nonneg hF_glb
  refine ⟨?_, ?_⟩
  · rintro _ ⟨f, hf, rfl⟩
    exact (partitionRestriction irrationalSet).monotone (hsx.1 hf)
  · intro h hh_lower
    have hdiff_lower : h - partitionRestriction irrationalSet x ∈
        lowerBounds (partitionRestriction irrationalSet '' F) := by
      rintro _ ⟨z, ⟨f, hf, rfl⟩, rfl⟩
      have hhf : h ≤ partitionRestriction irrationalSet f :=
        hh_lower ⟨f, hf, rfl⟩
      simpa using sub_le_sub_right hhf (partitionRestriction irrationalSet x)
    have hdiff_le : h - partitionRestriction irrationalSet x ≤ 0 :=
      hzero.2 hdiff_lower
    exact sub_nonpos.mp hdiff_le

/-- No strictly positive restricted continuous function lies below the
characteristic function of the irrational component. -/
theorem no_positive_restriction_below_irrationalCharacteristic
    (f : Q5Space)
    (hf_pos : 0 < partitionRestriction irrationalSet f)
    (hf_le : partitionRestriction irrationalSet f ≤
      irrationalCharacteristic) : False := by
  have hf_nonneg : 0 ≤ f := by
    apply (partitionRestriction irrationalSet).le_of_map_le
      (partitionRestriction_injective irrationalSet)
    simpa using hf_pos.le
  have hf_rat (q : ℚ) : f (q : ℝ) = 0 := by
    let qr : (irrationalSetᶜ : Set ℝ) := ⟨q, Rat.not_irrational q⟩
    have hle := (ContinuousMap.le_def.mp hf_le) (Sum.inr qr)
    have hnonneg := (ContinuousMap.le_def.mp hf_nonneg) (q : ℝ)
    change f (q : ℝ) ≤ 0 at hle
    exact le_antisymm hle hnonneg
  have hf_zero : f = 0 := by
    ext x
    have hfun : (↑f : ℝ → ℝ) = fun _ => 0 := by
      apply Rat.denseRange_cast.equalizer f.continuous continuous_const
      funext q
      exact hf_rat q
    exact congrFun hfun x
  subst f
  simp at hf_pos

/-- The characteristic function of the irrational component is strictly
positive in the concrete completion. -/
theorem irrationalCharacteristic_pos :
    (0 : IrrationalPartitionFunctions) < irrationalCharacteristic := by
  have hchar_nonneg : (0 : IrrationalPartitionFunctions) ≤
      irrationalCharacteristic := by
    rw [ContinuousMap.le_def]
    intro z
    cases z <;> norm_num [irrationalCharacteristic]
  have hchar_ne : irrationalCharacteristic ≠
      (0 : IrrationalPartitionFunctions) := by
    intro hzero
    let p : irrationalSet := ⟨Real.sqrt 2, irrational_sqrt_two⟩
    have := DFunLike.congr_fun hzero (Sum.inl p)
    norm_num [irrationalCharacteristic] at this
  exact lt_of_le_of_ne hchar_nonneg (Ne.symm hchar_ne)

/-- The second assertion of Proposition 6.2: the range of `J` in the
concrete completion is not order dense. -/
theorem irrationalRestriction_range_not_orderDense :
    ¬ IsOrderDense
      (Set.range (partitionRestriction irrationalSet :
        Q5Space → IrrationalPartitionFunctions)) := by
  intro hdense
  obtain ⟨y, ⟨f, rfl⟩, hy_pos, hy_le⟩ :=
    hdense irrationalCharacteristic_pos
  exact no_positive_restriction_below_irrationalCharacteristic f hy_pos hy_le

/-! ## Transport to the canonical completion -/

noncomputable section CanonicalCompletion

local instance : TopologicalSpace Q5Space :=
  partitionInducedTopology irrationalSet
local instance : T2Space Q5Space :=
  partitionInduced_t2Space irrationalSet
local instance : IsLocallyConvexSolidVectorLattice Q5Space :=
  partitionInduced_isLocallyConvexSolid irrationalSet
local instance : ContinuousSMul ℝ Q5Space :=
  @IsLocallySolidVectorLattice.toContinuousSMul Q5Space _ _ _ _
    (partitionInducedTopology irrationalSet)
    (partitionInduced_isLocallyConvexSolid
      irrationalSet).toIsLocallySolidVectorLattice
local instance : UniformSpace Q5Space :=
  IsTopologicalAddGroup.rightUniformSpace Q5Space
local instance : IsUniformAddGroup Q5Space :=
  isUniformAddGroup_of_addCommGroup
local instance : UniformContinuousConstSMul ℝ Q5Space :=
  uniformContinuousConstSMul_of_continuousConstSMul ℝ Q5Space
local instance : IsLocallyConvexSolidVectorLattice
    IrrationalPartitionFunctions :=
  compactOpen_isLocallyConvexSolid _
local instance : IsUniformAddGroup IrrationalPartitionFunctions :=
  compactOpen_isUniformAddGroup _

/-- A greatest lower bound is preserved by the vector-lattice equivalence
between the concrete and canonical completions. -/
theorem irrationalCompletionVecLatEquiv_isGLB
    {s : Set IrrationalPartitionFunctions}
    {x : IrrationalPartitionFunctions} (hx : IsGLB s x) :
    IsGLB (irrationalCompletionVecLatEquiv '' s)
      (irrationalCompletionVecLatEquiv x) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact irrationalCompletionVecLatEquiv.toVecLatHom.monotone (hx.1 hy)
  · intro z hz
    have hpull : irrationalCompletionVecLatEquiv.symm z ∈ lowerBounds s := by
      intro y hy
      have hzy := hz ⟨y, hy, rfl⟩
      have := irrationalCompletionVecLatEquiv.symm.toVecLatHom.monotone hzy
      change irrationalCompletionVecLatEquiv.toLinearEquiv.symm z ≤
        irrationalCompletionVecLatEquiv.toLinearEquiv.symm
          (irrationalCompletionVecLatEquiv.toLinearEquiv y) at this
      simpa only [LinearEquiv.symm_apply_apply] using this
    have hpull_le := hx.2 hpull
    have := irrationalCompletionVecLatEquiv.toVecLatHom.monotone hpull_le
    change irrationalCompletionVecLatEquiv.toLinearEquiv
      (irrationalCompletionVecLatEquiv.toLinearEquiv.symm z) ≤
        irrationalCompletionVecLatEquiv.toLinearEquiv x at this
    simpa only [LinearEquiv.apply_symm_apply] using this

theorem irrationalCompletionVecLatEquiv_le_iff
    {x y : IrrationalPartitionFunctions} :
    irrationalCompletionVecLatEquiv x ≤
      irrationalCompletionVecLatEquiv y ↔ x ≤ y := by
  constructor
  · intro h
    have := irrationalCompletionVecLatEquiv.symm.toVecLatHom.monotone h
    change irrationalCompletionVecLatEquiv.toLinearEquiv.symm
        (irrationalCompletionVecLatEquiv.toLinearEquiv x) ≤
      irrationalCompletionVecLatEquiv.toLinearEquiv.symm
        (irrationalCompletionVecLatEquiv.toLinearEquiv y) at this
    simpa only [LinearEquiv.symm_apply_apply] using this
  · intro h
    simpa using irrationalCompletionVecLatEquiv.toVecLatHom.monotone h

theorem irrationalCompletionVecLatEquiv_lt_iff
    {x y : IrrationalPartitionFunctions} :
    irrationalCompletionVecLatEquiv x <
      irrationalCompletionVecLatEquiv y ↔ x < y := by
  constructor
  · intro h
    have hstrict :=
      irrationalCompletionVecLatEquiv.symm.toVecLatHom.monotone
        |>.strictMono_of_injective
          irrationalCompletionVecLatEquiv.symm.toLinearEquiv.injective
    have := hstrict h
    change irrationalCompletionVecLatEquiv.toLinearEquiv.symm
        (irrationalCompletionVecLatEquiv.toLinearEquiv x) <
      irrationalCompletionVecLatEquiv.toLinearEquiv.symm
        (irrationalCompletionVecLatEquiv.toLinearEquiv y) at this
    simpa only [LinearEquiv.symm_apply_apply] using this
  · intro h
    have hstrict := irrationalCompletionVecLatEquiv.toVecLatHom.monotone
      |>.strictMono_of_injective
        irrationalCompletionVecLatEquiv.toLinearEquiv.injective
    simpa using hstrict h

/-- Regularity of the concrete restriction embedding transported to the
canonical completion. -/
theorem completionEmbedding_rightOrdContinuous :
    RightOrdContinuous ((↑) : Q5Space → Completion Q5Space) := by
  intro s x hsx
  have hconcrete := irrationalRestriction_rightOrdContinuous hsx
  have hcanonical := irrationalCompletionVecLatEquiv_isGLB hconcrete
  simpa only [Set.image_image, Function.comp_apply,
    irrationalCompletionVecLatEquiv_apply,
    irrationalCompletionEquiv_partitionRestriction] using hcanonical

/-- Failure of order density transported from the concrete completion to
the canonical completion. -/
theorem completionEmbedding_range_not_orderDense :
    ¬ IsOrderDense
      (Set.range ((↑) : Q5Space → Completion Q5Space)) := by
  intro hdense
  have hz_pos : (0 : Completion Q5Space) <
      irrationalCompletionVecLatEquiv irrationalCharacteristic := by
    have h := (irrationalCompletionVecLatEquiv_lt_iff
      (x := (0 : IrrationalPartitionFunctions))
      (y := irrationalCharacteristic)).mpr irrationalCharacteristic_pos
    have hezero : irrationalCompletionVecLatEquiv
        (0 : IrrationalPartitionFunctions) = 0 := by
      change irrationalCompletionVecLatEquiv.toLinearEquiv 0 = 0
      exact irrationalCompletionVecLatEquiv.toLinearEquiv.map_zero
    rw [hezero] at h
    exact h
  obtain ⟨_, ⟨f, rfl⟩, hf_pos, hf_le⟩ := hdense hz_pos
  have hcoe : (f : Completion Q5Space) =
      irrationalCompletionVecLatEquiv
        (partitionRestriction irrationalSet f) := by
    symm
    exact irrationalCompletionEquiv_partitionRestriction f
  rw [hcoe] at hf_pos hf_le
  have hf_pos' : (0 : IrrationalPartitionFunctions) <
      partitionRestriction irrationalSet f := by
    apply irrationalCompletionVecLatEquiv_lt_iff.mp
    have hezero : irrationalCompletionVecLatEquiv
        (0 : IrrationalPartitionFunctions) = 0 := by
      change irrationalCompletionVecLatEquiv.toLinearEquiv 0 = 0
      exact irrationalCompletionVecLatEquiv.toLinearEquiv.map_zero
    rw [hezero]
    exact hf_pos
  have hf_le' : partitionRestriction irrationalSet f ≤
      irrationalCharacteristic :=
    irrationalCompletionVecLatEquiv_le_iff.mp hf_le
  exact no_positive_restriction_below_irrationalCharacteristic
    f hf_pos' hf_le'

end CanonicalCompletion

/-- Theorem 6.3: there exists a Hausdorff locally convex-solid vector
lattice whose canonical image in its topological completion is regular but
not order dense. Regularity is expressed by preservation of all existing
infima, while order density uses `IsOrderDense` from BanLat. -/
theorem theorem6_3 :
    ∃ (E : Type) (_ : AddCommGroup E) (_ : Lattice E)
      (_ : IsOrderedAddMonoid E) (_ : VectorLattice E)
      (_ : TopologicalSpace E) (_ : T2Space E)
      (_ : IsLocallyConvexSolidVectorLattice E),
      letI : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
      letI : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
      RightOrdContinuous ((↑) : E → Completion E) ∧
        ¬ IsOrderDense
          (Set.range ((↑) : E → Completion E)) := by
  letI : TopologicalSpace Q5Space :=
    partitionInducedTopology irrationalSet
  letI : T2Space Q5Space :=
    partitionInduced_t2Space irrationalSet
  letI : IsLocallyConvexSolidVectorLattice Q5Space :=
    partitionInduced_isLocallyConvexSolid irrationalSet
  letI : ContinuousSMul ℝ Q5Space :=
    @IsLocallySolidVectorLattice.toContinuousSMul Q5Space _ _ _ _
      (partitionInducedTopology irrationalSet)
      (partitionInduced_isLocallyConvexSolid
        irrationalSet).toIsLocallySolidVectorLattice
  letI : UniformSpace Q5Space :=
    IsTopologicalAddGroup.rightUniformSpace Q5Space
  letI : IsUniformAddGroup Q5Space :=
    isUniformAddGroup_of_addCommGroup
  letI : UniformContinuousConstSMul ℝ Q5Space :=
    uniformContinuousConstSMul_of_continuousConstSMul ℝ Q5Space
  refine ⟨Q5Space, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · exact completionEmbedding_rightOrdContinuous
  · exact completionEmbedding_range_not_orderDense

end Aliprantis.Question5
