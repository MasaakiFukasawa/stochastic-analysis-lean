import Chapter2ArbitraryTimeMetric
import Chapter2LocalCompleteness

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter2Written
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- Transfer the two-index Cauchy condition using convergence for arbitrary
pairs of subsequences. No metric-space structure is assumed in this lemma. -/
theorem cauchy_of_pairwise_zero_limits (d e : ℕ → ℕ → ℝ)
    (hd : ∀ n m, 0 ≤ d n m)
    (transfer : ∀ a b : ℕ → ℕ,
      Tendsto (fun n => d (a n) (b n)) atTop (𝓝 0) →
      Tendsto (fun n => e (a n) (b n)) atTop (𝓝 0))
    (hc : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ m ≥ N, d n m < ε) :
    ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ m ≥ N, e n m < ε := by
  classical
  by_contra h
  push_neg at h
  obtain ⟨ε,hε,hbad⟩ := h
  choose a ha b hb he using hbad
  have hl : Tendsto (fun n => d (a n) (b n)) atTop (𝓝 0) := by
    apply tendsto_order.mpr
    constructor
    · intro r hr
      exact Eventually.of_forall (fun n => hr.trans_le (hd _ _))
    · intro r hr
      obtain ⟨N,hN⟩ := hc r hr
      exact eventually_atTop.mpr ⟨N,fun n hn => hN _ (hn.trans (ha n)) _ (hn.trans (hb n))⟩
  have hz : ε ≤ 0 := ge_of_tendsto (transfer a b hl) (Eventually.of_forall he)
  exact (not_le_of_gt hε) hz

theorem interval_path_distance_eq_coordinate
    {T : EReal} [Fact (0 ≤ T)] (u : ℕ → ClosedTime T)
    (hu : StrictMono u) (hut : ∀ n, u n < ⊤)
    (hc : ∀ t, t < ⊤ → ∃ n, t < u n)
    (f g : C(Iio (⊤ : ClosedTime T),ℝ)) :
    pathDistance (intervalTimeExhaustion u hu hut hc) f g =
      coordinateMetric (fun j (_ : Unit) => finiteTimeStageDist (u j) (hut j) f g) () := rfl

/-- Completeness for exactly the manuscript's arbitrary horizon sequence,
including nonmonotone sequences. The limit is an actual local martingale. -/
theorem arbitrary_time_local_martingale_cauchy_limit
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (u : ℕ → ClosedTime T) (hu : ∀ n, u n < ⊤) (huc : ⨆ n, u n = ⊤)
    (X : ℕ → Ω → C(Iio (⊤ : ClosedTime T),ℝ))
    (hX : ∀ n, LocalMProcessWitness P F (fun t ω => extendOpenPath (X n ω) t))
    (hc : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ k ≥ N,
      (∫ ω, coordinateMetric (fun j => fun ω => finiteTimeStageDist (u j) (hu j) (X n ω) (X k ω)) ω ∂P) < ε) :
    ∃ Y : Ω → C(Iio (⊤ : ClosedTime T),ℝ),
      LocalMProcessWitness P F (fun t ω => extendOpenPath (Y ω) t) ∧
      Tendsto (fun n => ∫ ω, coordinateMetric
        (fun j => fun ω => finiteTimeStageDist (u j) (hu j) (X n ω) (Y ω)) ω ∂P) atTop (𝓝 0) := by
  obtain ⟨v,hv,hvt,hvc⟩ := exists_strict_time_exhaustion hT
  have hvs : ⨆ n, v n = ⊤ := by
    apply eq_top_iff.mpr
    by_contra h
    obtain ⟨n,hn⟩ := hvc _ (lt_of_not_ge h)
    exact (not_lt_of_ge (le_iSup v n)) hn
  have hm n := local_martingale_path_measurable P F hle (X n) (hX n)
  let K := intervalTimeExhaustion v hv hvt hvc
  have hcK : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ k ≥ N,
      (∫ ω, pathDistance K (X n ω) (X k ω) ∂P) < ε := by
    apply cauchy_of_pairwise_zero_limits
      (fun n k => ∫ ω, coordinateMetric (fun j => fun ω => finiteTimeStageDist (u j) (hu j) (X n ω) (X k ω)) ω ∂P)
      (fun n k => ∫ ω, pathDistance K (X n ω) (X k ω) ∂P)
    · intro n k
      exact integral_nonneg (fun ω => (coordinate_metric_bounds _
        (fun j ω => finite_time_stage_nonneg _ _ _ _) ω).1)
    · intro a b hl
      exact (arbitrary_time_metric_equivalence P u v hu hvt huc hvs
        (fun n => X (a n)) (fun n => X (b n)) (fun n => hm (a n)) (fun n => hm (b n))).mp hl
    · exact hc
  obtain ⟨Y,hY,hlim⟩ := local_martingale_cauchy_limit P hT F hF hle hnull K X hX hcK
  refine ⟨Y,hY,?_⟩
  exact (arbitrary_time_metric_equivalence P u v hu hvt huc hvs X (fun _ => Y)
    hm (fun _ => local_martingale_path_measurable P F hle Y hY)).mpr hlim

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.arbitrary_time_local_martingale_cauchy_limit
