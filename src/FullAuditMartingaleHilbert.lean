import FullAuditMartingaleCompletion

open MeasureTheory Set Filter
open scoped ENNReal Topology InnerProductSpace
set_option maxHeartbeats 800000
namespace Asakura.FullAudit
open Asakura.Chapter1Written Asakura.Chapter2Written

/-- Actual process conditions, before quotienting by indistinguishability. -/
structure ContinuousM2Witness {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (X : ClosedTime T → Ω → ℝ) : Prop where
  adapted : ∀ t, Measurable[F t] (X t)
  moment : ∀ t, MemLp (X t) 2 P
  path : ∀ ω, Continuous (fun t => X t ω)
  martingale : ∀ s t, s ≤ t → P[X t | F s] =ᵐ[P] X s
  initial : X ⊥ =ᵐ[P] 0

theorem ContinuousM2Witness.zero {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω) :
    ContinuousM2Witness P F (fun _ => 0) := by
  constructor
  · exact fun _ => measurable_const
  · exact fun _ => MemLp.zero
  · exact fun _ => continuous_const
  · intro s t hst; simp
  · exact EventuallyEq.rfl

theorem ContinuousM2Witness.add {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    {X Y : ClosedTime T → Ω → ℝ} (hX : ContinuousM2Witness P F X) (hY : ContinuousM2Witness P F Y) :
    ContinuousM2Witness P F (fun t => X t+Y t) := by
  refine ⟨fun t => (hX.adapted t).add (hY.adapted t),fun t => (hX.moment t).add (hY.moment t),
    fun ω => (hX.path ω).add (hY.path ω),?_,?_⟩
  · intro s t hst
    exact (condExp_add ((hX.moment t).integrable (by norm_num)) ((hY.moment t).integrable (by norm_num)) (F s)).trans
      ((hX.martingale s t hst).add (hY.martingale s t hst))
  · simpa using hX.initial.add hY.initial

theorem ContinuousM2Witness.smul {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    {X : ClosedTime T → Ω → ℝ} (hX : ContinuousM2Witness P F X) (c : ℝ) :
    ContinuousM2Witness P F (fun t => c • X t) := by
  refine ⟨fun t => (hX.adapted t).const_smul c,fun t => (hX.moment t).const_smul c,
    fun ω => (hX.path ω).const_smul c,?_,?_⟩
  · intro s t hst
    exact (condExp_smul c (X t) (F s)).trans ((hX.martingale s t hst).const_smul c)
  · simpa using hX.initial.const_smul c

/-- Terminal values of precisely the manuscript's continuous L2 martingales. -/
noncomputable def continuousM2Terminal {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) : Submodule ℝ (Lp ℝ 2 P) where
  carrier := {v | ∃ X, ContinuousM2Witness P F X ∧ X ⊤ =ᵐ[P] v}
  zero_mem' := ⟨fun _ => 0,ContinuousM2Witness.zero P F,(Lp.coeFn_zero ℝ 2 P).symm⟩
  add_mem' := by
    rintro f g ⟨X,hX,hf⟩ ⟨Y,hY,hg⟩
    exact ⟨fun t => X t+Y t,hX.add P F hY,(hf.add hg).trans (Lp.coeFn_add f g).symm⟩
  smul_mem' := by
    rintro c f ⟨X,hX,hf⟩
    exact ⟨fun t => c • X t,hX.smul P F c,(hf.const_smul c).trans (Lp.coeFn_smul c f).symm⟩

/-- Completeness is established by the manuscript's Cauchy-sequence construction,
 not assumed as a property of the martingale space. -/
theorem continuous_m2_terminal_closed {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N) :
    IsClosed (continuousM2Terminal P F : Set (Lp ℝ 2 P)) := by
  apply IsSeqClosed.isClosed
  intro f v hf hfv
  choose X hX hterm using hf
  have he (n : ℕ) : ((hX n).moment ⊤).toLp (X n ⊤) = f n := by
    apply Lp.ext
    exact ((hX n).moment ⊤).coeFn_toLp.trans (hterm n)
  have hC : CauchySeq (fun n => ((hX n).moment ⊤).toLp (X n ⊤)) := by
    simp only [he]
    exact hfv.cauchySeq
  obtain ⟨Y,hm,h2,hc,hM,hz,hconv⟩ := continuous_martingale_cauchy_completion P F hF hle hnull X
    (fun n => (hX n).adapted) (fun n => (hX n).moment) (fun n => (hX n).path)
    (fun n => (hX n).martingale) (fun n => (hX n).initial) hC
  have hYLp := (current_lp_tendsto_Lp_iff_tendsto_eLpNorm_prime_prime (fun n => X n ⊤)
    (fun n => (hX n).moment ⊤) (Y ⊤) (h2 ⊤)).mpr hconv
  simp only [he] at hYLp
  have hv : (h2 ⊤).toLp (Y ⊤) = v := tendsto_nhds_unique hYLp hfv
  refine ⟨Y,⟨hm,h2,hc,hM,hz⟩,?_⟩
  rw [← hv]
  exact (h2 ⊤).coeFn_toLp.symm

theorem continuous_m2_hilbert_complete {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N) :
    CompleteSpace (continuousM2Terminal P F) :=
  (continuous_m2_terminal_closed P F hF hle hnull).isComplete.completeSpace_coe

/-- The inherited inner product is exactly the one printed in the manuscript. -/
theorem continuous_m2_inner_product {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (x y : continuousM2Terminal P F)
    (X Y : ClosedTime T → Ω → ℝ) (hx : X ⊤ =ᵐ[P] (x : Lp ℝ 2 P))
    (hy : Y ⊤ =ᵐ[P] (y : Lp ℝ 2 P)) :
    ⟪x,y⟫_ℝ = ∫ ω, X ⊤ ω * Y ⊤ ω ∂P := by
  change ⟪(x : Lp ℝ 2 P),(y : Lp ℝ 2 P)⟫_ℝ = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hx,hy] with ω hx hy
  rw [← hx,← hy]
  change Y ⊤ ω * X ⊤ ω = X ⊤ ω * Y ⊤ ω
  exact mul_comm _ _

/-- Equality of terminal values gives equality of complete continuous paths
 outside one null set. Thus the terminal realization identifies exactly the
 manuscript's quotient by indistinguishability. -/
theorem continuous_m2_terminal_injective {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (X Y : ClosedTime T → Ω → ℝ) (hX : ContinuousM2Witness P F X) (hY : ContinuousM2Witness P F Y)
    (he : X ⊤ =ᵐ[P] Y ⊤) : ∀ᵐ ω ∂P, ∀ t, X t ω = Y t ω := by
  have hfixed (t : ClosedTime T) : X t =ᵐ[P] Y t :=
    (hX.martingale t ⊤ le_top).symm.trans
      ((condExp_congr_ae he).trans (hY.martingale t ⊤ le_top))
  let D := ⋃ n : ℕ, range (gridTime (T := T) n)
  have hD : D.Countable := countable_iUnion fun n => (gridTime_finite_range T n).countable
  have hcommon : ∀ᵐ ω ∂P, ∀ t ∈ D, X t ω = Y t ω :=
    (ae_ball_iff hD).mpr (fun t _ => hfixed t)
  filter_upwards [hcommon] with ω hω
  intro t
  have hxt := gridTime_path_limit t (fun s => X s ω) (hX.path ω).continuousAt.continuousWithinAt
  have hyt := gridTime_path_limit t (fun s => Y s ω) (hY.path ω).continuousAt.continuousWithinAt
  have heq (n : ℕ) : X (gridTime n t) ω = Y (gridTime n t) ω :=
    hω _ (mem_iUnion.mpr ⟨n,mem_range_self t⟩)
  exact tendsto_nhds_unique (hxt.congr heq) hyt

end Asakura.FullAudit
