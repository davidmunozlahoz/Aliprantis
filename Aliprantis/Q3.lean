import BanLat.LocallySolid.Completion
import BanLat.LocallySolid.LocallyConvexSolid
import BanLat.Examples.CofK.Basic
import Mathlib.Topology.ContinuousMap.LocallyConvex
import Mathlib.Topology.Algebra.UniformConvergence
import Mathlib.Topology.TietzeExtension
import Mathlib.Topology.Instances.Irrational
import Mathlib.Topology.UniformSpace.CompactConvergence

open scoped Topology

namespace Aliprantis.Question3

open Filter UniformSpace

section UpperElement

variable {E : Type*} [AddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]
  [VectorLattice E] [TopologicalSpace E] [T2Space E]
  [IsLocallySolidVectorLattice E]

local instance : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
local instance : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup

/-- An element of the topological completion is an upper element if it is the
limit of an increasing sequence of positive elements of the original space. -/
def IsUpperElement (x : Completion E) : Prop :=
  ∃ u : ℕ → E, Monotone u ∧ (∀ n, 0 ≤ u n) ∧
    Tendsto (fun n => (u n : Completion E)) atTop (nhds x)

end UpperElement

/-! ## Proposition 4.2 -/

/-- The disjoint union `P ⊔ (M \ P)` used in Proposition 4.2. -/
abbrev PartitionSum (M : Type*) [TopologicalSpace M] (P : Set M) :=
  P ⊕ (Pᶜ : Set M)

/-- The vector lattice `Cₖ(P ⊔ (M \ P))`, represented by continuous
real-valued functions with the compact-open topology. -/
abbrev PartitionCompactOpenFunctions (M : Type*) [TopologicalSpace M]
    (P : Set M) :=
  C(PartitionSum M P, ℝ)

/-- The canonical map from `P ⊔ (M \ P)` back to `M`. -/
def partitionToM {M : Type*} [TopologicalSpace M] (P : Set M) :
    C(PartitionSum M P, M) :=
  ⟨Sum.elim Subtype.val Subtype.val,
    continuous_subtype_val.sumElim continuous_subtype_val⟩

/-- The two pieces of the partition have disjoint images in `M`. -/
theorem partitionToM_injective {M : Type*} [TopologicalSpace M] (P : Set M) :
    Function.Injective (partitionToM P) := by
  intro x y hxy
  cases x with
  | inl x =>
      cases y with
      | inl y =>
          congr
          exact Subtype.ext hxy
      | inr y =>
          change (x : M) = (y : M) at hxy
          exact False.elim (y.2 (hxy ▸ x.2))
  | inr x =>
      cases y with
      | inl y =>
          change (x : M) = (y : M) at hxy
          exact False.elim (x.2 (hxy.symm ▸ y.2))
      | inr y =>
          congr
          exact Subtype.ext hxy

/-- The map `J` from Proposition 4.2, restricting a continuous function on
`M` to `P` and its complement and viewing the restrictions on their disjoint
union. -/
noncomputable def partitionRestriction {M : Type*} [TopologicalSpace M]
    (P : Set M) : VecLatHom C(M, ℝ) (PartitionCompactOpenFunctions M P) where
  toFun f :=
    ⟨Sum.elim (fun x : P => f x) (fun x : (Pᶜ : Set M) => f x),
      f.continuous.comp continuous_subtype_val |>.sumElim
        (f.continuous.comp continuous_subtype_val)⟩
  map_add' f g := by
    ext x
    cases x <;> rfl
  map_smul' c f := by
    ext x
    cases x <;> rfl
  map_sup' f g := by
    ext x
    cases x <;> rfl
  map_inf' f g := by
    ext x
    cases x <;> rfl

@[simp]
theorem partitionRestriction_apply_inl {M : Type*} [TopologicalSpace M]
    (P : Set M) (f : C(M, ℝ)) (x : P) :
    partitionRestriction P f (Sum.inl x) = f x :=
  rfl

@[simp]
theorem partitionRestriction_apply_inr {M : Type*} [TopologicalSpace M]
    (P : Set M) (f : C(M, ℝ)) (x : (Pᶜ : Set M)) :
    partitionRestriction P f (Sum.inr x) = f x :=
  rfl

/-- Restriction to the two complementary pieces determines a function on
`M`. -/
theorem partitionRestriction_injective {M : Type*} [TopologicalSpace M]
    (P : Set M) : Function.Injective (partitionRestriction P) := by
  intro f g hfg
  ext x
  by_cases hx : x ∈ P
  · have h := DFunLike.congr_fun hfg (Sum.inl ⟨x, hx⟩)
    exact h
  · have h := DFunLike.congr_fun hfg (Sum.inr ⟨x, hx⟩)
    exact h

/-- The restriction map has dense range in the compact-open function space.
The argument only needs `M` to be metrizable (hence normal); compactness of
`M` itself is not required. -/
theorem partitionRestriction_denseRange (M : Type*) [MetricSpace M]
    (P : Set M) : DenseRange (partitionRestriction P) := by
  intro f
  rw [mem_closure_iff_nhds]
  intro U hU
  have hb : (nhds f).HasBasis
      (fun p : Set (PartitionSum M P) × ℝ => IsCompact p.1 ∧ 0 < p.2)
      (fun p => {g | ∀ x ∈ p.1, dist (g x) (f x) < p.2}) := by
    simpa using nhds_basis_uniformity (x := f)
      ((Metric.uniformity_basis_dist (α := ℝ)).compactConvergenceUniformity
        (α := PartitionSum M P))
  obtain ⟨p, hp, hpU⟩ := hb.mem_iff.mp hU
  letI : CompactSpace p.1 := isCompact_iff_compactSpace.mp hp.1
  let e : C(p.1, M) :=
    ⟨fun x => partitionToM P x.1,
      (partitionToM P).continuous.comp continuous_subtype_val⟩
  have heInjective : Function.Injective e := by
    intro x y hxy
    exact Subtype.ext (partitionToM_injective P hxy)
  have he : Topology.IsClosedEmbedding e :=
    Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
      e.continuous heInjective e.continuous.isClosedMap
  let fK : C(p.1, ℝ) := f.restrict p.1
  obtain ⟨g, hg⟩ := fK.exists_extension he
  refine ⟨partitionRestriction P g, hpU ?_, ⟨g, rfl⟩⟩
  intro x hx
  have hagree : partitionRestriction P g x = f x := by
    have h := DFunLike.congr_fun hg ⟨x, hx⟩
    cases x <;> simpa [e, fK] using h
  simp [hagree, hp.2]

/-- The topology on `C(M)` induced by `J` from the compact-open topology on
`Cₖ(P ⊔ (M \ P))`. -/
@[implicit_reducible]
noncomputable def partitionInducedTopology {M : Type*} [TopologicalSpace M]
    (P : Set M) : TopologicalSpace C(M, ℝ) :=
  ContinuousMap.compactOpen.induced (partitionRestriction P)

/-- The compact-open topology on real-valued continuous functions is locally
convex-solid. -/
theorem compactOpen_isLocallyConvexSolid (S : Type*)
    [TopologicalSpace S] : IsLocallyConvexSolidVectorLattice C(S, ℝ) := by
  letI : IsLocallySolidVectorLattice C(S, ℝ) := by
    refine { hasBasis_solid := ?_ }
    have hb : (nhds (0 : C(S, ℝ))).HasBasis
        (fun p : Set S × ℝ => IsCompact p.1 ∧ 0 < p.2)
        (fun p => {f | ∀ x ∈ p.1, dist (f x) 0 < p.2}) := by
      simpa using nhds_basis_uniformity (x := (0 : C(S, ℝ)))
        ((Metric.uniformity_basis_dist (α := ℝ)).compactConvergenceUniformity
          (α := S))
    refine hb.to_hasBasis' ?_ ?_
    · intro i hi
      let B : Set C(S, ℝ) := {f | ∀ x ∈ i.1, dist (f x) 0 < i.2}
      refine ⟨B, ⟨hb.mem_of_mem hi, ?_⟩, Set.Subset.rfl⟩
      intro f hf g hgf x hx
      have hpoint := ContinuousMap.le_def.mp hgf x
      rw [ContinuousMap.abs_apply, ContinuousMap.abs_apply] at hpoint
      exact (by
        simpa [B, Real.dist_eq] using
          hpoint.trans_lt (by simpa [B, Real.dist_eq] using hf x hx))
    · intro i hi
      exact hi.1
  exact { }

/-- The compact-convergence uniformity on real-valued continuous functions
is compatible with the additive group structure. -/
theorem compactOpen_isUniformAddGroup (S : Type*) [TopologicalSpace S] :
    IsUniformAddGroup C(S, ℝ) := by
  constructor
  apply ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isUniformInducing
    |>.uniformContinuous_iff.mpr
  simpa [Function.comp_def] using
    (uniformContinuous_sub.comp
      (ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.uniformContinuous.prodMap
        ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.uniformContinuous))

/-- The topology induced by the restriction vector-lattice homomorphism is
locally convex-solid. -/
theorem partitionInduced_isLocallyConvexSolid {M : Type*} [TopologicalSpace M]
    (P : Set M) :
    @IsLocallyConvexSolidVectorLattice C(M, ℝ) _ _ _ _
      (partitionInducedTopology P) := by
  letI : IsLocallyConvexSolidVectorLattice
      (PartitionCompactOpenFunctions M P) :=
    compactOpen_isLocallyConvexSolid _
  letI : TopologicalSpace C(M, ℝ) := partitionInducedTopology P
  letI : IsTopologicalAddGroup C(M, ℝ) :=
    topologicalAddGroup_induced (partitionRestriction P).toAddMonoidHom
  letI : ContinuousSMul ℝ C(M, ℝ) :=
    ContinuousSMul.induced (partitionRestriction P).toLinearMap
  letI : IsLocallySolidVectorLattice C(M, ℝ) := by
    refine { hasBasis_solid := ?_ }
    have hb := IsLocallySolidVectorLattice.hasBasis_solid
      (X := PartitionCompactOpenFunctions M P)
    have hc : (nhds (0 : C(M, ℝ))).HasBasis
        (fun s : Set (PartitionCompactOpenFunctions M P) =>
          s ∈ nhds 0 ∧ LatticeOrderedAddCommGroup.IsSolid s)
        (fun s => partitionRestriction P ⁻¹' s) := by
      rw [nhds_induced]
      simpa using hb.comap (partitionRestriction P)
    refine hc.to_hasBasis' ?_ ?_
    · intro i hi
      refine ⟨partitionRestriction P ⁻¹' i, ⟨hc.mem_of_mem hi, ?_⟩, Set.Subset.rfl⟩
      intro x hx y hy
      apply hi.2 hx
      rw [← (partitionRestriction P).map_abs,
        ← (partitionRestriction P).map_abs]
      exact (partitionRestriction P).monotone hy
    · intro i hi
      exact hi.1
  exact
    { toIsLocallySolidVectorLattice := inferInstance
      toLocallyConvexSpace :=
        LocallyConvexSpace.induced (partitionRestriction P).toLinearMap }

/-- The topology induced by the injective restriction map is Hausdorff. -/
theorem partitionInduced_t2Space {M : Type*} [TopologicalSpace M] (P : Set M) :
    @T2Space C(M, ℝ) (partitionInducedTopology P) := by
  letI : TopologicalSpace C(M, ℝ) := partitionInducedTopology P
  exact T2Space.of_injective_continuous (partitionRestriction_injective P)
    continuous_induced_dom

/-- The compact-open function space and restriction map, packaged as an
abstract completion of `C(M)` with its induced topology. -/
noncomputable def partitionCompletionPackage (M : Type*) [MetricSpace M]
    (P : Set M) :
    letI : TopologicalSpace C(M, ℝ) := partitionInducedTopology P
    letI : IsLocallyConvexSolidVectorLattice C(M, ℝ) :=
      partitionInduced_isLocallyConvexSolid P
    letI : T2Space C(M, ℝ) := partitionInduced_t2Space P
    letI : UniformSpace C(M, ℝ) :=
      IsTopologicalAddGroup.rightUniformSpace C(M, ℝ)
    AbstractCompletion C(M, ℝ) := by
  letI : TopologicalSpace C(M, ℝ) := partitionInducedTopology P
  letI : IsLocallyConvexSolidVectorLattice C(M, ℝ) :=
    partitionInduced_isLocallyConvexSolid P
  letI : T2Space C(M, ℝ) := partitionInduced_t2Space P
  letI : UniformSpace C(M, ℝ) :=
    IsTopologicalAddGroup.rightUniformSpace C(M, ℝ)
  letI : IsUniformAddGroup C(M, ℝ) := isUniformAddGroup_of_addCommGroup
  letI : IsUniformAddGroup (PartitionCompactOpenFunctions M P) :=
    compactOpen_isUniformAddGroup _
  exact
    { space := PartitionCompactOpenFunctions M P
      coe := partitionRestriction P
      uniformStruct := inferInstance
      complete := inferInstance
      separation := inferInstance
      isUniformInducing := by
        apply AddMonoidHom.isUniformInducing_of_isInducing
        exact ⟨rfl⟩
      dense := partitionRestriction_denseRange M P }

/-- Proposition 4.2 (in the slightly stronger form used by the paper): if
`M` is a metric space and `P ⊆ M`, then
`C(M)`, equipped with the topology induced by restriction to
`Cₖ(P ⊔ (M \ P))`, is a Hausdorff locally convex-solid vector lattice.
Moreover, the compact-open function space, together with the restriction map,
is its topological completion. -/
theorem proposition4_2 (M : Type*) [MetricSpace M] (P : Set M) :
    ∃ (hT2 : @T2Space C(M, ℝ) (partitionInducedTopology P))
      (hLcs : @IsLocallyConvexSolidVectorLattice C(M, ℝ) _ _ _ _
        (partitionInducedTopology P)),
      letI : TopologicalSpace C(M, ℝ) := partitionInducedTopology P
      letI : T2Space C(M, ℝ) := hT2
      letI : IsLocallyConvexSolidVectorLattice C(M, ℝ) := hLcs
      letI : UniformSpace C(M, ℝ) :=
        IsTopologicalAddGroup.rightUniformSpace C(M, ℝ)
      letI : IsUniformAddGroup C(M, ℝ) := isUniformAddGroup_of_addCommGroup
      ∃ e : PartitionCompactOpenFunctions M P ≃ᵤ Completion C(M, ℝ),
        ∀ f : C(M, ℝ),
          e (partitionRestriction P f) = (f : Completion C(M, ℝ)) := by
  refine ⟨partitionInduced_t2Space P,
    partitionInduced_isLocallyConvexSolid P, ?_⟩
  letI : TopologicalSpace C(M, ℝ) := partitionInducedTopology P
  letI : T2Space C(M, ℝ) := partitionInduced_t2Space P
  letI : IsLocallyConvexSolidVectorLattice C(M, ℝ) :=
    partitionInduced_isLocallyConvexSolid P
  letI : UniformSpace C(M, ℝ) :=
    IsTopologicalAddGroup.rightUniformSpace C(M, ℝ)
  letI : IsUniformAddGroup C(M, ℝ) := isUniformAddGroup_of_addCommGroup
  let pkg := partitionCompletionPackage M P
  let e := @AbstractCompletion.compareEquiv C(M, ℝ)
    (IsTopologicalAddGroup.rightUniformSpace C(M, ℝ)) pkg
    (@Completion.cPkg C(M, ℝ)
      (IsTopologicalAddGroup.rightUniformSpace C(M, ℝ)))
  refine ⟨e, ?_⟩
  intro f
  exact @AbstractCompletion.compare_coe C(M, ℝ)
    (IsTopologicalAddGroup.rightUniformSpace C(M, ℝ)) pkg
    (@Completion.cPkg C(M, ℝ)
      (IsTopologicalAddGroup.rightUniformSpace C(M, ℝ))) f

/-! ## Lemma 4.3 -/

/-- The set `P = ℝ \ ℚ` used in Section 4.2 of the paper. -/
abbrev irrationalSet : Set ℝ := {x | Irrational x}

/-- The concrete completion `Cₖ(P ⊔ ℚ)` used in Section 4.2.  We represent
`ℚ` as the complement in `ℝ` of the set of irrational numbers. -/
abbrev IrrationalPartitionFunctions :=
  PartitionCompactOpenFunctions ℝ irrationalSet

/-- The characteristic function of the irrational component of
`P ⊔ ℚ`. -/
def irrationalCharacteristic : IrrationalPartitionFunctions :=
  ⟨Sum.elim (fun _ => 1) (fun _ => 0),
    continuous_const.sumElim continuous_const⟩

@[simp]
theorem irrationalCharacteristic_apply_inl (x : irrationalSet) :
    irrationalCharacteristic (Sum.inl x) = 1 :=
  rfl

@[simp]
theorem irrationalCharacteristic_apply_inr (x : (irrationalSetᶜ : Set ℝ)) :
    irrationalCharacteristic (Sum.inr x) = 0 :=
  rfl

/-- An upper element in the concrete completion from Proposition 4.2: it is
the compact-open limit of the restrictions of an increasing sequence of
positive functions in `C(ℝ)`. -/
def IsPartitionUpperElement (f : IrrationalPartitionFunctions) : Prop :=
  ∃ u : ℕ → C(ℝ, ℝ), Monotone u ∧ (∀ n, 0 ≤ u n) ∧
    Tendsto (fun n => partitionRestriction irrationalSet (u n)) atTop (nhds f)

/-- The open superlevel set of the pointwise supremum of a sequence. -/
def upperLevelUnion (u : ℕ → C(ℝ, ℝ)) (c : ℝ) : Set ℝ :=
  ⋃ n, (u n) ⁻¹' Set.Ioi c

theorem isOpen_upperLevelUnion (u : ℕ → C(ℝ, ℝ)) (c : ℝ) :
    IsOpen (upperLevelUnion u c) := by
  apply isOpen_iUnion
  intro n
  exact isOpen_Ioi.preimage (u n).continuous

theorem mem_upperLevelUnion_iff (u : ℕ → C(ℝ, ℝ)) (c x : ℝ) :
    x ∈ upperLevelUnion u c ↔ ∃ n, c < u n x := by
  simp [upperLevelUnion]

/-- Compact-open convergence implies convergence at every point. -/
theorem tendsto_partitionRestriction_apply
    {u : ℕ → C(ℝ, ℝ)} {f : IrrationalPartitionFunctions}
    (hu : Tendsto (fun n => partitionRestriction irrationalSet (u n))
      atTop (nhds f))
    (x : PartitionSum ℝ irrationalSet) :
    Tendsto (fun n => partitionRestriction irrationalSet (u n) x)
      atTop (nhds (f x)) :=
  (continuous_eval_const x).continuousAt.tendsto.comp hu

/-- Every term of an increasing convergent sequence is bounded above by its
limit, pointwise. -/
theorem partitionRestriction_le_limit
    {u : ℕ → C(ℝ, ℝ)} {f : IrrationalPartitionFunctions}
    (hmono : Monotone u)
    (hlim : Tendsto (fun n => partitionRestriction irrationalSet (u n))
      atTop (nhds f))
    (n : ℕ) (x : PartitionSum ℝ irrationalSet) :
    partitionRestriction irrationalSet (u n) x ≤ f x := by
  apply ge_of_tendsto (tendsto_partitionRestriction_apply hlim x)
  filter_upwards [eventually_ge_atTop n] with m hnm
  cases x with
  | inl x =>
      simpa using ContinuousMap.le_def.mp (hmono hnm) x
  | inr x =>
      simpa using ContinuousMap.le_def.mp (hmono hnm) x

/-- If the limit is strictly above `c` at an irrational point, some member of
the approximating sequence is already strictly above `c` there. -/
theorem irrational_mem_upperLevelUnion
    {u : ℕ → C(ℝ, ℝ)} {f : IrrationalPartitionFunctions}
    (hlim : Tendsto (fun n => partitionRestriction irrationalSet (u n))
      atTop (nhds f))
    {c x : ℝ} (hx : Irrational x)
    (hcx : c < f (Sum.inl ⟨x, hx⟩)) :
    x ∈ upperLevelUnion u c := by
  rw [mem_upperLevelUnion_iff]
  have heventually : ∀ᶠ n in atTop,
      c < partitionRestriction irrationalSet (u n) (Sum.inl ⟨x, hx⟩) :=
    (tendsto_partitionRestriction_apply hlim (Sum.inl ⟨x, hx⟩)).eventually
      (eventually_gt_nhds hcx)
  obtain ⟨n, hn⟩ := heventually.exists
  exact ⟨n, by simpa using hn⟩

/-- Lemma 4.3: if an upper element of `Cₖ((ℝ \ ℚ) ⊔ ℚ)` dominates the
characteristic function of the irrational component, then its value at every
rational point is at least one. -/
theorem lemma4_3 {f : IrrationalPartitionFunctions}
    (hf : IsPartitionUpperElement f)
    (hchar : irrationalCharacteristic ≤ f) :
    ∀ q : (irrationalSetᶜ : Set ℝ), 1 ≤ f (Sum.inr q) := by
  rintro q
  rcases hf with ⟨u, hmono, _hpos, hlim⟩
  by_contra hq
  have hq_lt : f (Sum.inr q) < 1 := lt_of_not_ge hq
  obtain ⟨c, hfq_lt_c, hc_lt_one⟩ := exists_between hq_lt
  let W : Set (irrationalSetᶜ : Set ℝ) :=
    {r | f (Sum.inr r) < c}
  have hW_open : IsOpen W := by
    exact isOpen_lt (f.continuous.comp continuous_inr) continuous_const
  have hqW : q ∈ W := hfq_lt_c
  rcases isOpen_induced_iff.mp hW_open with ⟨V, hV_open, hV_eq⟩
  have hqV : (q : ℝ) ∈ V := by
    have : q ∈ Subtype.val ⁻¹' V := by
      rw [hV_eq]
      exact hqW
    exact this
  obtain ⟨x, hx_irr, hxV⟩ :=
    dense_irrational.exists_mem_open hV_open ⟨q, hqV⟩
  have hx_level : x ∈ upperLevelUnion u c := by
    apply irrational_mem_upperLevelUnion hlim hx_irr
    exact hc_lt_one.trans_le
      (ContinuousMap.le_def.mp hchar (Sum.inl ⟨x, hx_irr⟩))
  obtain ⟨r, hr⟩ := Rat.denseRange_cast.exists_mem_open
    (hV_open.inter (isOpen_upperLevelUnion u c))
    ⟨x, hxV, hx_level⟩
  have hrV : (r : ℝ) ∈ V := hr.1
  have hr_level : (r : ℝ) ∈ upperLevelUnion u c := hr.2
  let qr : (irrationalSetᶜ : Set ℝ) := ⟨r, Rat.not_irrational r⟩
  have hfr_lt_c : f (Sum.inr qr) < c := by
    have hqrW : qr ∈ W := by
      rw [← hV_eq]
      exact hrV
    exact hqrW
  rcases (mem_upperLevelUnion_iff u c r).mp hr_level with ⟨n, hn⟩
  have hn_le : u n r ≤ f (Sum.inr qr) := by
    simpa [qr] using
      partitionRestriction_le_limit hmono hlim n (Sum.inr qr)
  linarith

/-! ### Identifying the concrete and canonical completions -/

noncomputable section IrrationalCompletion

local instance : TopologicalSpace C(ℝ, ℝ) :=
  partitionInducedTopology irrationalSet
local instance : T2Space C(ℝ, ℝ) :=
  partitionInduced_t2Space irrationalSet
local instance : IsLocallyConvexSolidVectorLattice C(ℝ, ℝ) :=
  partitionInduced_isLocallyConvexSolid irrationalSet
local instance : ContinuousSMul ℝ C(ℝ, ℝ) :=
  @IsLocallySolidVectorLattice.toContinuousSMul C(ℝ, ℝ) _ _ _ _
    (partitionInducedTopology irrationalSet)
    (partitionInduced_isLocallyConvexSolid irrationalSet).toIsLocallySolidVectorLattice
local instance : UniformSpace C(ℝ, ℝ) :=
  IsTopologicalAddGroup.rightUniformSpace C(ℝ, ℝ)
local instance : IsUniformAddGroup C(ℝ, ℝ) :=
  isUniformAddGroup_of_addCommGroup
local instance : UniformContinuousConstSMul ℝ C(ℝ, ℝ) :=
  uniformContinuousConstSMul_of_continuousConstSMul ℝ C(ℝ, ℝ)
local instance : IsLocallyConvexSolidVectorLattice
    IrrationalPartitionFunctions :=
  compactOpen_isLocallyConvexSolid _
local instance : IsUniformAddGroup IrrationalPartitionFunctions :=
  compactOpen_isUniformAddGroup _

/-- The canonical uniform equivalence from the concrete function-space
completion in the paper to Lean's canonical uniform completion. -/
noncomputable def irrationalCompletionEquiv :
    IrrationalPartitionFunctions ≃ᵤ Completion C(ℝ, ℝ) :=
  let pkg := partitionCompletionPackage ℝ irrationalSet
  @AbstractCompletion.compareEquiv C(ℝ, ℝ)
    (IsTopologicalAddGroup.rightUniformSpace C(ℝ, ℝ)) pkg
    (@Completion.cPkg C(ℝ, ℝ)
      (IsTopologicalAddGroup.rightUniformSpace C(ℝ, ℝ)))

@[simp]
theorem irrationalCompletionEquiv_partitionRestriction (f : C(ℝ, ℝ)) :
    irrationalCompletionEquiv (partitionRestriction irrationalSet f) =
      (f : Completion C(ℝ, ℝ)) := by
  exact @AbstractCompletion.compare_coe C(ℝ, ℝ)
    (IsTopologicalAddGroup.rightUniformSpace C(ℝ, ℝ))
    (partitionCompletionPackage ℝ irrationalSet)
    (@Completion.cPkg C(ℝ, ℝ)
      (IsTopologicalAddGroup.rightUniformSpace C(ℝ, ℝ))) f

theorem irrationalCompletionEquiv_map_add
    (x y : IrrationalPartitionFunctions) :
    irrationalCompletionEquiv (x + y) =
      irrationalCompletionEquiv x + irrationalCompletionEquiv y := by
  have hdense_left (a : C(ℝ, ℝ)) :
      irrationalCompletionEquiv
          (partitionRestriction irrationalSet a + y) =
        (a : Completion C(ℝ, ℝ)) + irrationalCompletionEquiv y := by
    have hfun :
        (fun z => irrationalCompletionEquiv
            (partitionRestriction irrationalSet a + z)) =
          (fun z => (a : Completion C(ℝ, ℝ)) +
            irrationalCompletionEquiv z) := by
      apply (partitionRestriction_denseRange ℝ irrationalSet).equalizer
      · exact irrationalCompletionEquiv.continuous.comp
          (continuous_const.add continuous_id)
      · exact continuous_const.add irrationalCompletionEquiv.continuous
      · funext b
        change irrationalCompletionEquiv
            (partitionRestriction irrationalSet a +
              partitionRestriction irrationalSet b) =
          (a : Completion C(ℝ, ℝ)) +
            irrationalCompletionEquiv (partitionRestriction irrationalSet b)
        rw [← map_add, irrationalCompletionEquiv_partitionRestriction,
          irrationalCompletionEquiv_partitionRestriction, Completion.coe_add]
    exact congrFun hfun y
  have hfun :
      (fun z => irrationalCompletionEquiv (z + y)) =
        (fun z => irrationalCompletionEquiv z +
          irrationalCompletionEquiv y) := by
    apply (partitionRestriction_denseRange ℝ irrationalSet).equalizer
    · exact irrationalCompletionEquiv.continuous.comp
        (continuous_id.add continuous_const)
    · exact irrationalCompletionEquiv.continuous.add continuous_const
    · funext a
      change irrationalCompletionEquiv
          (partitionRestriction irrationalSet a + y) =
        irrationalCompletionEquiv (partitionRestriction irrationalSet a) +
          irrationalCompletionEquiv y
      simpa using hdense_left a
  exact congrFun hfun x

theorem irrationalCompletionEquiv_map_smul (r : ℝ)
    (x : IrrationalPartitionFunctions) :
    irrationalCompletionEquiv (r • x) =
      r • irrationalCompletionEquiv x := by
  have hfun :
      (fun z => irrationalCompletionEquiv (r • z)) =
        (fun z => r • irrationalCompletionEquiv z) := by
    apply (partitionRestriction_denseRange ℝ irrationalSet).equalizer
    · exact irrationalCompletionEquiv.continuous.comp
        (continuous_const_smul r)
    · exact (continuous_const_smul r).comp
        irrationalCompletionEquiv.continuous
    · funext a
      change irrationalCompletionEquiv
          (r • partitionRestriction irrationalSet a) =
        r • irrationalCompletionEquiv
          (partitionRestriction irrationalSet a)
      rw [← map_smul, irrationalCompletionEquiv_partitionRestriction,
        irrationalCompletionEquiv_partitionRestriction, Completion.coe_smul]
  exact congrFun hfun x

theorem irrationalCompletionEquiv_map_sup
    (x y : IrrationalPartitionFunctions) :
    irrationalCompletionEquiv (x ⊔ y) =
      irrationalCompletionEquiv x ⊔ irrationalCompletionEquiv y := by
  have hcont_source : Continuous
      (fun p : IrrationalPartitionFunctions × IrrationalPartitionFunctions =>
        p.1 ⊔ p.2) :=
    ((isLocallySolidVectorLattice_iff_uniformContinuous_sup
      (E := IrrationalPartitionFunctions)).mp inferInstance).continuous
  have hcont_target : Continuous
      (fun p : Completion C(ℝ, ℝ) × Completion C(ℝ, ℝ) => p.1 ⊔ p.2) :=
    Completion.continuous_map₂ continuous_fst continuous_snd
  have hdense_left (a : C(ℝ, ℝ)) :
      irrationalCompletionEquiv
          (partitionRestriction irrationalSet a ⊔ y) =
        (a : Completion C(ℝ, ℝ)) ⊔ irrationalCompletionEquiv y := by
    have hfun :
        (fun z => irrationalCompletionEquiv
            (partitionRestriction irrationalSet a ⊔ z)) =
          (fun z => (a : Completion C(ℝ, ℝ)) ⊔
            irrationalCompletionEquiv z) := by
      apply (partitionRestriction_denseRange ℝ irrationalSet).equalizer
      · exact irrationalCompletionEquiv.continuous.comp
          (hcont_source.comp (continuous_const.prodMk continuous_id))
      · exact hcont_target.comp
          (continuous_const.prodMk irrationalCompletionEquiv.continuous)
      · funext b
        change irrationalCompletionEquiv
            (partitionRestriction irrationalSet a ⊔
              partitionRestriction irrationalSet b) =
          (a : Completion C(ℝ, ℝ)) ⊔
            irrationalCompletionEquiv (partitionRestriction irrationalSet b)
        rw [irrationalCompletionEquiv_partitionRestriction]
        calc
          irrationalCompletionEquiv
              (partitionRestriction irrationalSet a ⊔
                partitionRestriction irrationalSet b) =
              irrationalCompletionEquiv
                (partitionRestriction irrationalSet (a ⊔ b)) :=
            congrArg irrationalCompletionEquiv
              ((partitionRestriction irrationalSet).map_sup' a b).symm
          _ = ((a ⊔ b : C(ℝ, ℝ)) : Completion C(ℝ, ℝ)) :=
            irrationalCompletionEquiv_partitionRestriction _
          _ = (a : Completion C(ℝ, ℝ)) ⊔
              (b : Completion C(ℝ, ℝ)) :=
            IsLocallySolidVectorLattice.toCompletionVecLatHom.map_sup' a b
    exact congrFun hfun y
  have hfun :
      (fun z => irrationalCompletionEquiv (z ⊔ y)) =
        (fun z => irrationalCompletionEquiv z ⊔
          irrationalCompletionEquiv y) := by
    apply (partitionRestriction_denseRange ℝ irrationalSet).equalizer
    · exact irrationalCompletionEquiv.continuous.comp
        (hcont_source.comp (continuous_id.prodMk continuous_const))
    · exact hcont_target.comp
        (irrationalCompletionEquiv.continuous.prodMk continuous_const)
    · funext a
      change irrationalCompletionEquiv
          (partitionRestriction irrationalSet a ⊔ y) =
        irrationalCompletionEquiv (partitionRestriction irrationalSet a) ⊔
          irrationalCompletionEquiv y
      simpa using hdense_left a
  exact congrFun hfun x

/-- The comparison of completions is also a vector-lattice equivalence. -/
noncomputable def irrationalCompletionVecLatEquiv :
    VecLatEquiv IrrationalPartitionFunctions (Completion C(ℝ, ℝ)) := by
  let e : IrrationalPartitionFunctions ≃ₗ[ℝ] Completion C(ℝ, ℝ) :=
    { irrationalCompletionEquiv.toEquiv with
      map_add' := irrationalCompletionEquiv_map_add
      map_smul' := irrationalCompletionEquiv_map_smul }
  have habs : ∀ x, e |x| = |e x| := by
    intro x
    change irrationalCompletionEquiv |x| = |irrationalCompletionEquiv x|
    rw [abs, abs, irrationalCompletionEquiv_map_sup,
      show -x = (-1 : ℝ) • x by simp,
      irrationalCompletionEquiv_map_smul, neg_one_smul]
  let hVecLatHom := VecLatHom.of_abs e.toLinearMap habs
  exact
    { e with
      map_sup' := hVecLatHom.map_sup'
      map_inf' := hVecLatHom.map_inf' }

@[simp]
theorem irrationalCompletionVecLatEquiv_apply
    (f : IrrationalPartitionFunctions) :
    irrationalCompletionVecLatEquiv f = irrationalCompletionEquiv f :=
  rfl

@[simp]
theorem irrationalCompletionVecLatEquiv_symm_apply
    (x : Completion C(ℝ, ℝ)) :
    irrationalCompletionVecLatEquiv.symm x =
      irrationalCompletionEquiv.symm x :=
  rfl

/-- Upper elements in the canonical completion pull back to upper elements
in the concrete function-space completion. -/
theorem isPartitionUpperElement_symm
    {x : Completion C(ℝ, ℝ)} (hx : IsUpperElement x) :
    IsPartitionUpperElement (irrationalCompletionEquiv.symm x) := by
  rcases hx with ⟨u, hmono, hpos, hlim⟩
  refine ⟨u, hmono, hpos, ?_⟩
  have hpull : Tendsto
      (fun n => irrationalCompletionEquiv.symm (u n : Completion C(ℝ, ℝ)))
      atTop (nhds (irrationalCompletionEquiv.symm x)) :=
    irrationalCompletionEquiv.symm.continuous.continuousAt.tendsto.comp hlim
  convert hpull using 1
  funext n
  rw [← irrationalCompletionEquiv_partitionRestriction,
    irrationalCompletionEquiv.symm_apply_apply]

end IrrationalCompletion

/-- Theorem 4.4: there exists a Hausdorff locally convex-solid vector lattice
whose topological completion contains a positive element that is not the
limit of a decreasing sequence of upper elements. -/
theorem theorem4_4 :
    ∃ (E : Type) (_ : AddCommGroup E) (_ : Lattice E)
      (_ : IsOrderedAddMonoid E) (_ : VectorLattice E)
      (_ : TopologicalSpace E) (_ : T2Space E)
      (_ : IsLocallyConvexSolidVectorLattice E),
      letI : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
      letI : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
      ∃ x : Completion E, 0 ≤ x ∧
        ¬ ∃ u : ℕ → Completion E,
          Antitone u ∧ (∀ n, IsUpperElement (u n)) ∧
            Tendsto u atTop (nhds x) := by
  letI : TopologicalSpace C(ℝ, ℝ) :=
    partitionInducedTopology irrationalSet
  letI : T2Space C(ℝ, ℝ) :=
    partitionInduced_t2Space irrationalSet
  letI : IsLocallyConvexSolidVectorLattice C(ℝ, ℝ) :=
    partitionInduced_isLocallyConvexSolid irrationalSet
  letI : ContinuousSMul ℝ C(ℝ, ℝ) :=
    @IsLocallySolidVectorLattice.toContinuousSMul C(ℝ, ℝ) _ _ _ _
      (partitionInducedTopology irrationalSet)
      (partitionInduced_isLocallyConvexSolid
        irrationalSet).toIsLocallySolidVectorLattice
  letI : UniformSpace C(ℝ, ℝ) :=
    IsTopologicalAddGroup.rightUniformSpace C(ℝ, ℝ)
  letI : IsUniformAddGroup C(ℝ, ℝ) :=
    isUniformAddGroup_of_addCommGroup
  letI : UniformContinuousConstSMul ℝ C(ℝ, ℝ) :=
    uniformContinuousConstSMul_of_continuousConstSMul ℝ C(ℝ, ℝ)
  refine ⟨C(ℝ, ℝ), inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  refine ⟨irrationalCompletionEquiv irrationalCharacteristic, ?_, ?_⟩
  · change 0 ≤ irrationalCompletionVecLatEquiv irrationalCharacteristic
    apply irrationalCompletionVecLatEquiv.toVecLatHom.map_nonneg
    rw [ContinuousMap.le_def]
    intro x
    cases x <;> norm_num [irrationalCharacteristic]
  · rintro ⟨v, hv_anti, hv_upper, hv_lim⟩
    let f : ℕ → IrrationalPartitionFunctions :=
      fun n => irrationalCompletionEquiv.symm (v n)
    have hf_upper (n : ℕ) : IsPartitionUpperElement (f n) := by
      simpa [f] using isPartitionUpperElement_symm (hv_upper n)
    have hchar (n : ℕ) : irrationalCharacteristic ≤ f n := by
      have hneg_mono : Monotone (fun n => -v n) := by
        intro i j hij
        exact neg_le_neg (hv_anti hij)
      have hneg_lim : Tendsto (fun n => -v n) atTop
          (nhds (-irrationalCompletionEquiv irrationalCharacteristic)) :=
        hv_lim.neg
      have hLUB :=
        isLUB_of_monotone_tendsto_of_t2_locallySolidVectorLattice
          hneg_mono hneg_lim
      have hx_le : irrationalCompletionVecLatEquiv irrationalCharacteristic ≤
          v n := by
        exact neg_le_neg_iff.mp (hLUB.1 ⟨n, rfl⟩)
      have hpull :=
        irrationalCompletionVecLatEquiv.symm.toVecLatHom.monotone hx_le
      change irrationalCompletionVecLatEquiv.symm
          (irrationalCompletionVecLatEquiv irrationalCharacteristic) ≤
        irrationalCompletionVecLatEquiv.symm (v n) at hpull
      have hleft : irrationalCompletionVecLatEquiv.symm
          (irrationalCompletionVecLatEquiv irrationalCharacteristic) =
          irrationalCharacteristic := by
        exact irrationalCompletionVecLatEquiv.toLinearEquiv.symm_apply_apply _
      rw [hleft] at hpull
      simpa [f] using hpull
    let q0 : (irrationalSetᶜ : Set ℝ) :=
      ⟨0, by
        change ¬Irrational (0 : ℝ)
        simp⟩
    have hf_q0 (n : ℕ) : 1 ≤ f n (Sum.inr q0) :=
      lemma4_3 (hf_upper n) (hchar n) q0
    have hf_lim : Tendsto f atTop (nhds irrationalCharacteristic) := by
      have hpull :=
        irrationalCompletionEquiv.symm.continuous.continuousAt.tendsto.comp hv_lim
      simpa [f] using hpull
    have hq0_lim :
        Tendsto (fun n => f n (Sum.inr q0)) atTop
          (nhds (irrationalCharacteristic (Sum.inr q0))) :=
      (continuous_eval_const (Sum.inr q0)).continuousAt.tendsto.comp hf_lim
    have hone : 1 ≤ irrationalCharacteristic (Sum.inr q0) :=
      ge_of_tendsto hq0_lim (Eventually.of_forall hf_q0)
    norm_num at hone

end Aliprantis.Question3
