import Aliprantis.Q3
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.Topology.UrysohnsLemma

open scoped Topology

namespace Aliprantis.Question4

open Filter UniformSpace
open Aliprantis.Question3

variable (E : Type*) [AddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]
  [VectorLattice E] [TopologicalSpace E] [IsLocallySolidVectorLattice E]

/-- A locally solid vector lattice has the generalized `(A, 0)` property if
every positive, antitone, topologically Cauchy net with greatest lower bound
zero converges topologically to zero. Cauchyness is taken with respect to the
canonical uniformity induced by the topological additive group. -/
class genA0 : Prop where
  tendsto_zero_of_cauchy_antitone_isGLB :
    ∀ {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
      {u : ι → E}, Antitone u → (∀ i, 0 ≤ u i) →
      IsGLB (Set.range u) 0 →
      letI : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
      Cauchy (Filter.map u Filter.atTop) →
      Tendsto u atTop (nhds 0)

/-! ## The Cantor-space model of the example -/

/-- A standard compact metric Cantor space, used as an ambient-space
substitute for `[0,1]` in the paper's existential construction. -/
abbrev CantorAmbient := ℕ → Bool

/-- A closed nowhere-dense copy of the Cantor set: all even coordinates are
fixed to `false`, while the odd coordinates are free. -/
def smallCantorSet : Set CantorAmbient :=
  {x | ∀ n, x (2 * n) = false}

/-- The dense half `P` of `smallCantorSet`, consisting of the points that are
eventually `false`. Its complement inside `smallCantorSet` is also dense. -/
def cantorPartition : Set CantorAmbient :=
  {x | x ∈ smallCantorSet ∧ ∀ᶠ n in atTop, x n = false}

theorem cantorPartition_subset_smallCantorSet :
    cantorPartition ⊆ smallCantorSet := fun _ hx => hx.1

/-- Truncate a Boolean sequence after `N`. -/
def truncateBool (x : CantorAmbient) (N : ℕ) : CantorAmbient :=
  fun n => if n < N then x n else false

theorem truncateBool_mem_smallCantorSet {x : CantorAmbient}
    (hx : x ∈ smallCantorSet) (N : ℕ) :
    truncateBool x N ∈ smallCantorSet := by
  intro n
  by_cases h : 2 * n < N
  · simp [truncateBool, h, hx n]
  · simp [truncateBool, h]

theorem truncateBool_mem_cantorPartition {x : CantorAmbient}
    (hx : x ∈ smallCantorSet) (N : ℕ) :
    truncateBool x N ∈ cantorPartition := by
  refine ⟨truncateBool_mem_smallCantorSet hx N, ?_⟩
  filter_upwards [eventually_ge_atTop N] with n hn
  simp [truncateBool, not_lt.mpr hn]

theorem tendsto_truncateBool (x : CantorAmbient) :
    Tendsto (truncateBool x) atTop (nhds x) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop i] with N hN
  simp [truncateBool, hN]

theorem dense_cantorPartition_in_smallCantorSet :
    Dense {x : smallCantorSet | (x : CantorAmbient) ∈ cantorPartition} := by
  intro x
  let u : ℕ → smallCantorSet := fun N =>
    ⟨truncateBool x N, truncateBool_mem_smallCantorSet x.2 N⟩
  apply mem_closure_of_tendsto (f := u) (b := atTop)
  · rw [tendsto_subtype_rng]
    exact tendsto_truncateBool x
  · exact Eventually.of_forall fun N => truncateBool_mem_cantorPartition x.2 N

/-- Keep the first `N` coordinates and then alternate `false, true`. -/
def oddTailBool (x : CantorAmbient) (N : ℕ) : CantorAmbient :=
  fun n => if n < N then x n else if n % 2 = 0 then false else true

theorem oddTailBool_mem_smallCantorSet {x : CantorAmbient}
    (hx : x ∈ smallCantorSet) (N : ℕ) :
    oddTailBool x N ∈ smallCantorSet := by
  intro n
  by_cases h : 2 * n < N
  · simp [oddTailBool, h, hx n]
  · simp [oddTailBool, h]

theorem oddTailBool_not_eventually_false (x : CantorAmbient) (N : ℕ) :
    ¬ ∀ᶠ n in atTop, oddTailBool x N n = false := by
  intro h
  rcases (mem_atTop_sets.mp h) with ⟨k, hk⟩
  let j := 2 * max N k + 1
  have hjN : ¬ j < N := by
    dsimp [j]
    omega
  have hjk : k ≤ j := by
    dsimp [j]
    omega
  have hjmod : j % 2 ≠ 0 := by
    dsimp [j]
    omega
  have := hk j hjk
  simp [oddTailBool, hjN, hjmod] at this

theorem tendsto_oddTailBool (x : CantorAmbient) :
    Tendsto (oddTailBool x) atTop (nhds x) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop i] with N hN
  simp [oddTailBool, hN]

theorem dense_compl_cantorPartition_in_smallCantorSet :
    Dense {x : smallCantorSet | (x : CantorAmbient) ∉ cantorPartition} := by
  intro x
  let u : ℕ → smallCantorSet := fun N =>
    ⟨oddTailBool x N, oddTailBool_mem_smallCantorSet x.2 N⟩
  apply mem_closure_of_tendsto (f := u) (b := atTop)
  · rw [tendsto_subtype_rng]
    exact tendsto_oddTailBool x
  · refine Eventually.of_forall fun N hmem => ?_
    exact oddTailBool_not_eventually_false x N hmem.2

theorem isClosed_smallCantorSet : IsClosed smallCantorSet := by
  rw [show smallCantorSet = ⋂ n : ℕ,
      (fun x : CantorAmbient => x (2 * n)) ⁻¹' ({false} : Set Bool) by
    ext x
    simp [smallCantorSet]]
  exact isClosed_iInter fun n =>
    isClosed_singleton.preimage (continuous_apply (2 * n))

/-- Change one remote even coordinate to leave `smallCantorSet`. -/
def punctureSmallCantor (x : CantorAmbient) (N : ℕ) : CantorAmbient :=
  Function.update x (2 * N) true

theorem punctureSmallCantor_not_mem (x : CantorAmbient) (N : ℕ) :
    punctureSmallCantor x N ∉ smallCantorSet := by
  intro h
  have := h N
  simp [punctureSmallCantor] at this

theorem tendsto_punctureSmallCantor (x : CantorAmbient) :
    Tendsto (punctureSmallCantor x) atTop (nhds x) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop i] with N hN
  have hne : i ≠ 2 * N := by omega
  simp [punctureSmallCantor, hne]

theorem dense_compl_smallCantorSet : Dense smallCantorSetᶜ := by
  intro x
  by_cases hx : x ∈ smallCantorSet
  · apply mem_closure_of_tendsto (f := punctureSmallCantor x) (b := atTop)
    · exact tendsto_punctureSmallCantor x
    · exact Eventually.of_forall fun N => punctureSmallCantor_not_mem x N
  · exact subset_closure hx

/-! ## Lemma 5.2: failure of regularity -/

/-- The vector lattice `C(M)` in the counterexample. -/
abbrev Q4Space := C(CantorAmbient, ℝ)

/-- Its concrete completion `Cₖ(P ⊔ Q)`. -/
abbrev Q4ConcreteCompletion :=
  PartitionCompactOpenFunctions CantorAmbient cantorPartition

/-- The set `D` from Lemma 5.2: positive continuous functions that dominate
the characteristic function of `smallCantorSet`. -/
def dominatingFunctions : Set Q4Space :=
  {f | 0 ≤ f ∧ ∀ x ∈ smallCantorSet, 1 ≤ f x}

/-- The characteristic function of `P` on the disjoint union `P ⊔ Q`. -/
def cantorPartitionCharacteristic : Q4ConcreteCompletion :=
  ⟨Sum.elim (fun _ => 1) (fun _ => 0),
    continuous_const.sumElim continuous_const⟩

@[simp]
theorem cantorPartitionCharacteristic_apply_inl (x : cantorPartition) :
    cantorPartitionCharacteristic (Sum.inl x) = 1 := rfl

@[simp]
theorem cantorPartitionCharacteristic_apply_inr
    (x : (cantorPartitionᶜ : Set CantorAmbient)) :
    cantorPartitionCharacteristic (Sum.inr x) = 0 := rfl

/-- Outside the small Cantor set there is a member of `D` vanishing at the
prescribed point. This is the Urysohn-lemma step in Lemma 5.2. -/
theorem exists_dominatingFunction_eq_zero {t : CantorAmbient}
    (ht : t ∉ smallCantorSet) :
    ∃ f ∈ dominatingFunctions, f t = 0 := by
  obtain ⟨f, hfone, hfzero, _hcompact, hfrange⟩ :=
    exists_continuous_one_zero_of_isCompact
      isClosed_smallCantorSet.isCompact isClosed_singleton
      (Set.disjoint_singleton_right.mpr ht)
  refine ⟨f, ?_, hfzero (Set.mem_singleton t)⟩
  refine ⟨ContinuousMap.le_def.mpr fun x => (hfrange x).1, ?_⟩
  intro x hx
  exact le_of_eq (hfone hx).symm

/-- In the original continuous-function lattice, the family `D` has
greatest lower bound zero. -/
theorem dominatingFunctions_isGLB_zero :
    IsGLB dominatingFunctions (0 : Q4Space) := by
  refine ⟨?_, ?_⟩
  · intro f hf
    exact hf.1
  · intro g hg
    rw [ContinuousMap.le_def]
    intro t
    have hclosed : IsClosed {x : CantorAmbient | g x ≤ 0} :=
      isClosed_le g.continuous continuous_const
    have hsubset : smallCantorSetᶜ ⊆ {x : CantorAmbient | g x ≤ 0} := by
      intro x hx
      obtain ⟨f, hfD, hfx⟩ := exists_dominatingFunction_eq_zero hx
      exact (hg hfD : g ≤ f) x |>.trans_eq hfx
    have hall : Set.univ ⊆ {x : CantorAmbient | g x ≤ 0} := by
      rw [← dense_compl_smallCantorSet.closure_eq]
      exact closure_minimal hsubset hclosed
    exact hall (Set.mem_univ t)

/-- The characteristic function of `P` is a lower bound after restriction
to the disjoint union `P ⊔ Pᶜ`. -/
theorem cantorPartitionCharacteristic_le_restriction
    {f : Q4Space} (hf : f ∈ dominatingFunctions) :
    cantorPartitionCharacteristic ≤ partitionRestriction cantorPartition f := by
  rw [ContinuousMap.le_def]
  intro x
  cases x with
  | inl x =>
      exact hf.2 x (cantorPartition_subset_smallCantorSet x.2)
  | inr x =>
      exact (ContinuousMap.le_def.mp hf.1) x

/-- The image of `D` in the concrete completion does not have zero as its
greatest lower bound. This is the conclusion of Lemma 5.2. -/
theorem restricted_dominatingFunctions_not_isGLB_zero :
    ¬ IsGLB (partitionRestriction cantorPartition '' dominatingFunctions)
        (0 : Q4ConcreteCompletion) := by
  intro hglb
  have hchar_lb : cantorPartitionCharacteristic ∈
      lowerBounds (partitionRestriction cantorPartition '' dominatingFunctions) := by
    rintro y ⟨f, hf, rfl⟩
    exact cantorPartitionCharacteristic_le_restriction hf
  have hchar_le : cantorPartitionCharacteristic ≤
      (0 : Q4ConcreteCompletion) := hglb.2 hchar_lb
  let p : cantorPartition :=
    ⟨fun _ => false, by
      refine ⟨?_, ?_⟩
      · intro n
        rfl
      · exact Eventually.of_forall fun _ => rfl⟩
  have := (ContinuousMap.le_def.mp hchar_le) (Sum.inl p)
  norm_num at this

/-! ## Lemma 5.3: Cauchy decreasing nets -/

/-- Convergence in the concrete compact-open completion implies pointwise
convergence on each side of the partition. -/
theorem tendsto_partitionRestriction_apply_general
    {I : Type*} {l : Filter I} {u : I → Q4Space}
    {g : Q4ConcreteCompletion}
    (hlim : Tendsto (fun i => partitionRestriction cantorPartition (u i))
      l (nhds g)) (x : PartitionSum CantorAmbient cantorPartition) :
    Tendsto (fun i => partitionRestriction cantorPartition (u i) x)
      l (nhds (g x)) :=
  (continuous_eval_const x).continuousAt.tendsto.comp hlim

/-- A pointwise limit of positive functions is positive. -/
theorem concrete_limit_nonnegative
    {I : Type*} {l : Filter I} [l.NeBot] {u : I → Q4Space}
    {g : Q4ConcreteCompletion} (hu : ∀ i, 0 ≤ u i)
    (hlim : Tendsto (fun i => partitionRestriction cantorPartition (u i))
      l (nhds g)) :
    0 ≤ g := by
  rw [ContinuousMap.le_def]
  intro x
  apply ge_of_tendsto (tendsto_partitionRestriction_apply_general hlim x)
  exact Eventually.of_forall fun i => by
    cases x with
    | inl x => exact (ContinuousMap.le_def.mp (hu i)) x
    | inr x => exact (ContinuousMap.le_def.mp (hu i)) x

/-- The limit of an antitone net is below every term, pointwise. -/
theorem concrete_limit_le_term
    {I : Type*} [Preorder I] [IsDirected I (fun x y => x ≤ y)]
    [Nonempty I] {u : I → Q4Space} {g : Q4ConcreteCompletion}
    (hu : Antitone u)
    (hlim : Tendsto (fun i => partitionRestriction cantorPartition (u i))
      atTop (nhds g)) (i : I)
    (x : PartitionSum CantorAmbient cantorPartition) :
    g x ≤ u i (partitionToM cantorPartition x) := by
  apply le_of_tendsto (tendsto_partitionRestriction_apply_general hlim x)
  filter_upwards [eventually_ge_atTop i] with j hij
  cases x with
  | inl x => exact (ContinuousMap.le_def.mp (hu hij)) x
  | inr x => exact (ContinuousMap.le_def.mp (hu hij)) x

/-- The first half of the proof of Lemma 5.3: the concrete limit vanishes
on the complementary component `Pᶜ`. The bump-function contradiction is
the same one used in the paper. -/
theorem concrete_limit_eq_zero_on_complement
    {I : Type*} [Preorder I] [IsDirected I (fun x y => x ≤ y)]
    [Nonempty I] {u : I → Q4Space} {g : Q4ConcreteCompletion}
    (hu_anti : Antitone u) (hu_nonneg : ∀ i, 0 ≤ u i)
    (hu_glb : IsGLB (Set.range u) 0)
    (hlim : Tendsto (fun i => partitionRestriction cantorPartition (u i))
      atTop (nhds g)) :
    ∀ q : (cantorPartitionᶜ : Set CantorAmbient), g (Sum.inr q) = 0 := by
  intro q
  have hg_nonneg := concrete_limit_nonnegative hu_nonneg hlim
  have hgq_nonneg : 0 ≤ g (Sum.inr q) :=
    (ContinuousMap.le_def.mp hg_nonneg) (Sum.inr q)
  by_contra hq_ne
  have hgq_pos : 0 < g (Sum.inr q) :=
    lt_of_le_of_ne hgq_nonneg (Ne.symm hq_ne)
  let c : ℝ := g (Sum.inr q) / 2
  have hc_pos : 0 < c := by
    dsimp [c]
    linarith
  have hc_lt : c < g (Sum.inr q) := by
    dsimp [c]
    linarith
  let W : Set (cantorPartitionᶜ : Set CantorAmbient) :=
    {r | c < g (Sum.inr r)}
  have hW_open : IsOpen W :=
    isOpen_lt continuous_const (g.continuous.comp continuous_inr)
  have hqW : q ∈ W := hc_lt
  obtain ⟨U, hU_open, hWU⟩ := isOpen_induced_iff.mp hW_open
  have hqU : (q : CantorAmbient) ∈ U := by
    have : q ∈ Subtype.val ⁻¹' U := by
      rw [hWU]
      exact hqW
    exact this
  obtain ⟨t, htC, htU⟩ :=
    dense_compl_smallCantorSet.exists_mem_open hU_open ⟨q, hqU⟩
  let V : Set CantorAmbient := U ∩ smallCantorSetᶜ
  have hV_open : IsOpen V :=
    hU_open.inter isClosed_smallCantorSet.isOpen_compl
  have htV : t ∈ V := ⟨htU, htC⟩
  obtain ⟨b, hb_one, hb_zero, _hb_compact, hb_range⟩ :=
    exists_continuous_one_zero_of_isCompact
      (isCompact_singleton : IsCompact ({t} : Set CantorAmbient))
      hV_open.isClosed_compl
      (Set.disjoint_singleton_left.mpr (by simpa using htV))
  let a : Q4Space := c • b
  have ha_nonzero : 0 < a t := by
    simp [a, hb_one (Set.mem_singleton t), hc_pos]
  have ha_lower : a ∈ lowerBounds (Set.range u) := by
    rintro _ ⟨i, rfl⟩
    rw [ContinuousMap.le_def]
    intro x
    by_cases hxV : x ∈ V
    · let qx : (cantorPartitionᶜ : Set CantorAmbient) :=
        ⟨x, fun hxP => hxV.2 (cantorPartition_subset_smallCantorSet hxP)⟩
      have hqxW : qx ∈ W := by
        rw [← hWU]
        exact hxV.1
      have hg_le : g (Sum.inr qx) ≤ u i x := by
        simpa [qx] using concrete_limit_le_term hu_anti hlim i (Sum.inr qx)
      have hb_le : b x ≤ 1 := (hb_range x).2
      change c * b x ≤ u i x
      exact (mul_le_of_le_one_right hc_pos.le hb_le).trans
        ((show c < g (Sum.inr qx) from hqxW).le.trans hg_le)
    · have hb0 : b x = 0 := hb_zero hxV
      simp [a, hb0]
      exact (ContinuousMap.le_def.mp (hu_nonneg i)) x
  have ha_le_zero : a ≤ 0 := hu_glb.2 ha_lower
  have := (ContinuousMap.le_def.mp ha_le_zero) t
  change a t ≤ 0 at this
  exact (not_lt_of_ge this) ha_nonzero

/-- A continuous inequality holding on a dense subset of an open
neighborhood also holds at every point of that neighborhood. -/
theorem continuous_ge_of_dense_of_mem_open
    {X : Type*} [TopologicalSpace X] {D : Set X} (hD : Dense D)
    {U : Set X} (hU : IsOpen U) {s : X} (hsU : s ∈ U)
    {f : X → ℝ} (hf : Continuous f) {c : ℝ}
    (hge : ∀ x ∈ D, x ∈ U → c ≤ f x) :
    c ≤ f s := by
  by_contra h
  have hslt : f s < c := lt_of_not_ge h
  let O : Set X := U ∩ f ⁻¹' Set.Iio c
  have hO_open : IsOpen O := hU.inter (isOpen_Iio.preimage hf)
  have hsO : s ∈ O := ⟨hsU, hslt⟩
  obtain ⟨x, hxD, hxO⟩ := hD.exists_mem_open hO_open ⟨s, hsO⟩
  exact (not_lt_of_ge (hge x hxD hxO.1)) hxO.2

/-- The second half of Lemma 5.3: The second half of the proof of Lemma 5.3: the concrete limit vanishes on the component `P`.-/
theorem concrete_limit_eq_zero_on_partition
    {I : Type*} [Preorder I] [IsDirected I (fun x y => x ≤ y)]
    [Nonempty I] {u : I → Q4Space} {g : Q4ConcreteCompletion}
    (hu_anti : Antitone u) (hu_nonneg : ∀ i, 0 ≤ u i)
    (hlim : Tendsto (fun i => partitionRestriction cantorPartition (u i))
      atTop (nhds g))
    (hg_compl : ∀ q : (cantorPartitionᶜ : Set CantorAmbient),
      g (Sum.inr q) = 0) :
    ∀ p : cantorPartition, g (Sum.inl p) = 0 := by
  intro p
  have hg_nonneg := concrete_limit_nonnegative hu_nonneg hlim
  have hgp_nonneg : 0 ≤ g (Sum.inl p) :=
    (ContinuousMap.le_def.mp hg_nonneg) (Sum.inl p)
  by_contra hp_ne
  have hgp_pos : 0 < g (Sum.inl p) :=
    lt_of_le_of_ne hgp_nonneg (Ne.symm hp_ne)
  let c : ℝ := g (Sum.inl p) / 2
  have hc_pos : 0 < c := by
    dsimp [c]
    linarith
  have hc_lt : c < g (Sum.inl p) := by
    dsimp [c]
    linarith
  let W : Set cantorPartition := {r | c < g (Sum.inl r)}
  have hW_open : IsOpen W :=
    isOpen_lt continuous_const (g.continuous.comp continuous_inl)
  have hpW : p ∈ W := hc_lt
  obtain ⟨U, hU_open, hWU⟩ := isOpen_induced_iff.mp hW_open
  have hpU : (p : CantorAmbient) ∈ U := by
    have : p ∈ Subtype.val ⁻¹' U := by
      rw [hWU]
      exact hpW
    exact this
  have hU_small_open : IsOpen (Subtype.val ⁻¹' U : Set smallCantorSet) :=
    hU_open.preimage continuous_subtype_val
  let pC : smallCantorSet :=
    ⟨p, cantorPartition_subset_smallCantorSet p.2⟩
  have hpC_U : pC ∈ Subtype.val ⁻¹' U := hpU
  obtain ⟨s, hs_notP, hsU⟩ :=
    dense_compl_cantorPartition_in_smallCantorSet.exists_mem_open
      hU_small_open ⟨pC, hpC_U⟩
  have hu_ge (i : I) : c ≤ u i s := by
    apply continuous_ge_of_dense_of_mem_open
      dense_cantorPartition_in_smallCantorSet hU_small_open hsU
      ((u i).continuous.comp continuous_subtype_val)
    intro x hxP hxU
    let px : cantorPartition := ⟨x, hxP⟩
    have hpxW : px ∈ W := by
      rw [← hWU]
      exact hxU
    have hg_le : g (Sum.inl px) ≤ u i x := by
      simpa [px] using concrete_limit_le_term hu_anti hlim i (Sum.inl px)
    exact (show c < g (Sum.inl px) from hpxW).le.trans hg_le
  let qs : (cantorPartitionᶜ : Set CantorAmbient) := ⟨s, hs_notP⟩
  have hg_ge : c ≤ g (Sum.inr qs) := by
    apply ge_of_tendsto
      (tendsto_partitionRestriction_apply_general hlim (Sum.inr qs))
    exact Eventually.of_forall fun i => by simpa [qs] using hu_ge i
  rw [hg_compl qs] at hg_ge
  linarith

/-- Lemma 5.3 in its concrete form: any positive antitone net with infimum
zero can only converge to zero in `Cₖ(P ⊔ Pᶜ)`. -/
theorem lemma5_3_concrete
    {I : Type*} [Preorder I] [IsDirected I (fun x y => x ≤ y)]
    [Nonempty I] {u : I → Q4Space} {g : Q4ConcreteCompletion}
    (hu_anti : Antitone u) (hu_nonneg : ∀ i, 0 ≤ u i)
    (hu_glb : IsGLB (Set.range u) 0)
    (hlim : Tendsto (fun i => partitionRestriction cantorPartition (u i))
      atTop (nhds g)) :
    g = 0 := by
  have hg_compl := concrete_limit_eq_zero_on_complement
    hu_anti hu_nonneg hu_glb hlim
  have hg_part := concrete_limit_eq_zero_on_partition
    hu_anti hu_nonneg hlim hg_compl
  ext x
  cases x with
  | inl p => simpa using hg_part p
  | inr q => simpa using hg_compl q

noncomputable section Q4Topology

local instance : MetricSpace CantorAmbient := PiNat.metricSpace
local instance : TopologicalSpace Q4Space :=
  partitionInducedTopology cantorPartition
local instance : T2Space Q4Space :=
  partitionInduced_t2Space cantorPartition
local instance : IsLocallyConvexSolidVectorLattice Q4Space :=
  partitionInduced_isLocallyConvexSolid cantorPartition
local instance : ContinuousSMul ℝ Q4Space :=
  @IsLocallySolidVectorLattice.toContinuousSMul Q4Space _ _ _ _
    (partitionInducedTopology cantorPartition)
    (partitionInduced_isLocallyConvexSolid
      cantorPartition).toIsLocallySolidVectorLattice
local instance : UniformSpace Q4Space :=
  IsTopologicalAddGroup.rightUniformSpace Q4Space
local instance : IsUniformAddGroup Q4Space :=
  isUniformAddGroup_of_addCommGroup
local instance : UniformContinuousConstSMul ℝ Q4Space :=
  uniformContinuousConstSMul_of_continuousConstSMul ℝ Q4Space
local instance : IsLocallyConvexSolidVectorLattice Q4ConcreteCompletion :=
  compactOpen_isLocallyConvexSolid _
local instance : IsUniformAddGroup Q4ConcreteCompletion :=
  compactOpen_isUniformAddGroup _

/-- Lemma 5.3: the induced locally convex-solid topology has the generalized
`(A, 0)` property. Completeness first supplies a concrete compact-open limit;
`lemma5_3_concrete` identifies it with zero. -/
theorem lemma5_3 : genA0 Q4Space := by
  constructor
  intro I _ _ _ u hu_anti hu_nonneg hu_glb hu_cauchy
  let pkg := partitionCompletionPackage CantorAmbient cantorPartition
  letI : UniformSpace pkg.space := pkg.uniformStruct
  letI : CompleteSpace pkg.space := pkg.complete
  letI : T0Space pkg.space := pkg.separation
  have hconcrete_cauchy : Cauchy
      (Filter.map (partitionRestriction cantorPartition)
        (Filter.map u atTop)) :=
    hu_cauchy.map pkg.isUniformInducing.uniformContinuous
  rw [Filter.map_map] at hconcrete_cauchy
  obtain ⟨g, hg⟩ := CompleteSpace.complete hconcrete_cauchy
  have hlim : Tendsto
      (fun i => partitionRestriction cantorPartition (u i))
      atTop (nhds g) := by
    simpa [Tendsto, Function.comp_def] using hg
  have hg_zero : g = 0 :=
    lemma5_3_concrete hu_anti hu_nonneg hu_glb hlim
  apply pkg.isUniformInducing.isInducing.tendsto_nhds_iff.mpr
  change Tendsto
    (fun i => partitionRestriction cantorPartition (u i)) atTop
      (nhds (partitionRestriction cantorPartition (0 : Q4Space)))
  simpa [Function.comp_def, hg_zero] using hlim

end Q4Topology

/-! ## Comparing the concrete and canonical completions -/

noncomputable section Q4Completion

local instance : MetricSpace CantorAmbient := PiNat.metricSpace
local instance : TopologicalSpace Q4Space :=
  partitionInducedTopology cantorPartition
local instance : T2Space Q4Space :=
  partitionInduced_t2Space cantorPartition
local instance : IsLocallyConvexSolidVectorLattice Q4Space :=
  partitionInduced_isLocallyConvexSolid cantorPartition
local instance : ContinuousSMul ℝ Q4Space :=
  @IsLocallySolidVectorLattice.toContinuousSMul Q4Space _ _ _ _
    (partitionInducedTopology cantorPartition)
    (partitionInduced_isLocallyConvexSolid
      cantorPartition).toIsLocallySolidVectorLattice
local instance : UniformSpace Q4Space :=
  IsTopologicalAddGroup.rightUniformSpace Q4Space
local instance : IsUniformAddGroup Q4Space :=
  isUniformAddGroup_of_addCommGroup
local instance : UniformContinuousConstSMul ℝ Q4Space :=
  uniformContinuousConstSMul_of_continuousConstSMul ℝ Q4Space
local instance : IsLocallyConvexSolidVectorLattice Q4ConcreteCompletion :=
  compactOpen_isLocallyConvexSolid _
local instance : IsUniformAddGroup Q4ConcreteCompletion :=
  compactOpen_isUniformAddGroup _

/-- The canonical uniform equivalence from the paper's concrete completion
to Lean's canonical completion. -/
noncomputable def q4CompletionEquiv :
    Q4ConcreteCompletion ≃ᵤ Completion Q4Space :=
  let pkg := partitionCompletionPackage CantorAmbient cantorPartition
  @AbstractCompletion.compareEquiv Q4Space
    (IsTopologicalAddGroup.rightUniformSpace Q4Space) pkg
    (@Completion.cPkg Q4Space
      (IsTopologicalAddGroup.rightUniformSpace Q4Space))

@[simp]
theorem q4CompletionEquiv_partitionRestriction (f : Q4Space) :
    q4CompletionEquiv (partitionRestriction cantorPartition f) =
      (f : Completion Q4Space) := by
  exact @AbstractCompletion.compare_coe Q4Space
    (IsTopologicalAddGroup.rightUniformSpace Q4Space)
    (partitionCompletionPackage CantorAmbient cantorPartition)
    (@Completion.cPkg Q4Space
      (IsTopologicalAddGroup.rightUniformSpace Q4Space)) f

/-- The comparison equivalence preserves binary suprema. This is proved by
continuity and density of the original restriction map. -/
theorem q4CompletionEquiv_map_sup (x y : Q4ConcreteCompletion) :
    q4CompletionEquiv (x ⊔ y) = q4CompletionEquiv x ⊔ q4CompletionEquiv y := by
  have hcont_source : Continuous
      (fun p : Q4ConcreteCompletion × Q4ConcreteCompletion => p.1 ⊔ p.2) :=
    ((isLocallySolidVectorLattice_iff_uniformContinuous_sup
      (E := Q4ConcreteCompletion)).mp inferInstance).continuous
  have hcont_target : Continuous
      (fun p : Completion Q4Space × Completion Q4Space => p.1 ⊔ p.2) :=
    Completion.continuous_map₂ continuous_fst continuous_snd
  have hdense_left (a : Q4Space) :
      q4CompletionEquiv (partitionRestriction cantorPartition a ⊔ y) =
        (a : Completion Q4Space) ⊔ q4CompletionEquiv y := by
    have hfun :
        (fun z => q4CompletionEquiv
            (partitionRestriction cantorPartition a ⊔ z)) =
          (fun z => (a : Completion Q4Space) ⊔ q4CompletionEquiv z) := by
      apply (partitionRestriction_denseRange CantorAmbient
        cantorPartition).equalizer
      · exact q4CompletionEquiv.continuous.comp
          (hcont_source.comp (continuous_const.prodMk continuous_id))
      · exact hcont_target.comp
          (continuous_const.prodMk q4CompletionEquiv.continuous)
      · funext b
        change q4CompletionEquiv
            (partitionRestriction cantorPartition a ⊔
              partitionRestriction cantorPartition b) =
          (a : Completion Q4Space) ⊔
            q4CompletionEquiv (partitionRestriction cantorPartition b)
        rw [q4CompletionEquiv_partitionRestriction]
        calc
          q4CompletionEquiv
              (partitionRestriction cantorPartition a ⊔
                partitionRestriction cantorPartition b) =
              q4CompletionEquiv
                (partitionRestriction cantorPartition (a ⊔ b)) :=
            congrArg q4CompletionEquiv
              ((partitionRestriction cantorPartition).map_sup' a b).symm
          _ = ((a ⊔ b : Q4Space) : Completion Q4Space) :=
            q4CompletionEquiv_partitionRestriction _
          _ = (a : Completion Q4Space) ⊔ (b : Completion Q4Space) :=
            IsLocallySolidVectorLattice.toCompletionVecLatHom.map_sup' a b
    exact congrFun hfun y
  have hfun :
      (fun z => q4CompletionEquiv (z ⊔ y)) =
        (fun z => q4CompletionEquiv z ⊔ q4CompletionEquiv y) := by
    apply (partitionRestriction_denseRange CantorAmbient
      cantorPartition).equalizer
    · exact q4CompletionEquiv.continuous.comp
        (hcont_source.comp (continuous_id.prodMk continuous_const))
    · exact hcont_target.comp
        (q4CompletionEquiv.continuous.prodMk continuous_const)
    · funext a
      change q4CompletionEquiv
          (partitionRestriction cantorPartition a ⊔ y) =
        q4CompletionEquiv (partitionRestriction cantorPartition a) ⊔
          q4CompletionEquiv y
      simpa using hdense_left a
  exact congrFun hfun x

/-- Consequently, the comparison map is monotone. -/
theorem q4CompletionEquiv_monotone : Monotone q4CompletionEquiv := by
  intro x y hxy
  apply sup_eq_right.mp
  rw [← q4CompletionEquiv_map_sup, sup_eq_right.mpr hxy]

/-- Lemma 5.2 transported to the canonical completion: its embedding is not
right order-continuous, hence its image is not a regular sublattice. -/
theorem q4_completion_not_rightOrdContinuous :
    ¬ RightOrdContinuous ((↑) : Q4Space → Completion Q4Space) := by
  intro hregular
  have hcompletion_glb := hregular dominatingFunctions_isGLB_zero
  let z : Completion Q4Space :=
    q4CompletionEquiv cantorPartitionCharacteristic
  have hz_lower : z ∈ lowerBounds
      (((↑) : Q4Space → Completion Q4Space) '' dominatingFunctions) := by
    rintro _ ⟨f, hf, rfl⟩
    change q4CompletionEquiv cantorPartitionCharacteristic ≤
      (f : Completion Q4Space)
    rw [← q4CompletionEquiv_partitionRestriction f]
    exact q4CompletionEquiv_monotone
      (cantorPartitionCharacteristic_le_restriction hf)
  have hz_le_zero : z ≤ (0 : Completion Q4Space) :=
    hcompletion_glb.2 hz_lower
  have he_zero : q4CompletionEquiv (0 : Q4ConcreteCompletion) =
      (0 : Completion Q4Space) := by
    simpa using q4CompletionEquiv_partitionRestriction (0 : Q4Space)
  have hz_nonneg : (0 : Completion Q4Space) ≤ z := by
    rw [← he_zero]
    exact q4CompletionEquiv_monotone
      (ContinuousMap.le_def.mpr fun x => by cases x <;> simp)
  have hz_zero : z = 0 := le_antisymm hz_le_zero hz_nonneg
  have hchar_zero : cantorPartitionCharacteristic =
      (0 : Q4ConcreteCompletion) := by
    apply q4CompletionEquiv.injective
    simpa [z, he_zero] using hz_zero
  let p : cantorPartition :=
    ⟨fun _ => false, by
      refine ⟨?_, ?_⟩
      · intro n
        rfl
      · exact Eventually.of_forall fun _ => rfl⟩
  have := DFunLike.congr_fun hchar_zero (Sum.inl p)
  norm_num at this

end Q4Completion

/-- Theorem 5.4: there exists a Hausdorff locally convex-solid vector
lattice satisfying the generalized `(A, 0)` property whose canonical image
in its topological completion is not a regular vector sublattice. Regularity
is expressed as right order-continuity of the canonical embedding, i.e. as
preservation of all existing infima. -/
theorem theorem5_4 :
    ∃ (E : Type) (_ : AddCommGroup E) (_ : Lattice E)
      (_ : IsOrderedAddMonoid E) (_ : VectorLattice E)
      (_ : TopologicalSpace E) (_ : T2Space E)
      (_ : IsLocallyConvexSolidVectorLattice E) (_ : genA0 E),
      letI : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
      letI : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
      ¬ RightOrdContinuous ((↑) : E → Completion E) := by
  letI : MetricSpace CantorAmbient := PiNat.metricSpace
  letI : TopologicalSpace Q4Space :=
    partitionInducedTopology cantorPartition
  letI : T2Space Q4Space :=
    partitionInduced_t2Space cantorPartition
  letI : IsLocallyConvexSolidVectorLattice Q4Space :=
    partitionInduced_isLocallyConvexSolid cantorPartition
  letI : ContinuousSMul ℝ Q4Space :=
    @IsLocallySolidVectorLattice.toContinuousSMul Q4Space _ _ _ _
      (partitionInducedTopology cantorPartition)
      (partitionInduced_isLocallyConvexSolid
        cantorPartition).toIsLocallySolidVectorLattice
  letI : UniformSpace Q4Space :=
    IsTopologicalAddGroup.rightUniformSpace Q4Space
  letI : IsUniformAddGroup Q4Space :=
    isUniformAddGroup_of_addCommGroup
  letI : UniformContinuousConstSMul ℝ Q4Space :=
    uniformContinuousConstSMul_of_continuousConstSMul ℝ Q4Space
  have hgen : genA0 Q4Space := lemma5_3
  refine ⟨Q4Space, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, hgen, ?_⟩
  exact q4_completion_not_rightOrdContinuous

end Aliprantis.Question4
