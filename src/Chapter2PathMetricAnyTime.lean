import Chapter2PathMetricProbability

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter2Written
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

theorem stopped_sup_le_interval_stage_distance_of_le
    {T : EReal} [Fact (0 ≤ T)]
    (u : ℕ → ClosedTime T) (hu : StrictMono u) (hut : ∀ n, u n < ⊤)
    (huc : ∀ t, t < ⊤ → ∃ n, t < u n)
    (f g : C(Iio (⊤ : ClosedTime T),ℝ)) (j : ℕ)
    (v : ClosedTime T) (hv : v ≤ u j) :
    (⨆ t, |extendOpenPath f (min v t)-extendOpenPath g (min v t)|) ≤
      compactStageDist (intervalTimeExhaustion u hu hut huc) j f g := by
  let K := intervalTimeExhaustion u hu hut huc
  letI : CompactSpace (K j) := isCompact_iff_compactSpace.1 (K.isCompact j)
  apply ciSup_le
  intro t
  let s : Iio (⊤ : ClosedTime T) := ⟨min v t,((min_le_left _ _).trans hv).trans_lt (hut j)⟩
  let r : K j := ⟨s,by change min v t ≤ u j; exact (min_le_left _ _).trans hv⟩
  have h := ContinuousMap.norm_coe_le_norm (f.restrict (K j)-g.restrict (K j)) r
  change |f s-g s| ≤ ‖f.restrict (K j)-g.restrict (K j)‖ at h
  change _ ≤ dist (f.restrict (K j)) (g.restrict (K j))
  rw [dist_eq_norm]
  have htt : min v t < ⊤ := ((min_le_left _ _).trans hv).trans_lt (hut j)
  dsimp only [extendOpenPath]
  rw [dif_pos htt,dif_pos htt]
  exact h

/-- The constructed Ito limit converges uniformly in probability up to
any fixed time strictly below T, not merely at the exhaustion times. -/
theorem stopped_probability_limit_of_path_metric_at_time
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)]
    (u : ℕ → ClosedTime T) (hu : StrictMono u) (hut : ∀ n, u n < ⊤)
    (huc : ∀ t, t < ⊤ → ∃ n, t < u n)
    (X Y : ℕ → Ω → C(Iio (⊤ : ClosedTime T),ℝ))
    (hX : ∀ n, Measurable (X n)) (hY : ∀ n, Measurable (Y n))
    (hp : Tendsto (fun n => ∫ ω, pathDistance (intervalTimeExhaustion u hu hut huc)
      (X n ω) (Y n ω) ∂P) atTop (𝓝 0))
    (v : ClosedTime T) (hv : v < ⊤) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => P {ω | ε ≤ ⨆ t,
      |extendOpenPath (X n ω) (min v t)-extendOpenPath (Y n ω) (min v t)|}) atTop (𝓝 0) := by
  letI : LocallyCompactSpace (Iio (⊤ : ClosedTime T)) := isOpen_Iio.locallyCompactSpace
  obtain ⟨j,hj⟩ := huc v hv
  have h := stage_probability_limit_of_path_metric P (intervalTimeExhaustion u hu hut huc) X Y hX hY hp j ε hε
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => bot_le)
  intro n
  exact measure_mono (fun ω hω => hω.trans (stopped_sup_le_interval_stage_distance_of_le u hu hut huc (X n ω) (Y n ω) j v hj.le))

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.stopped_sup_le_interval_stage_distance_of_le
#print axioms Asakura.Chapter2Complete.stopped_probability_limit_of_path_metric_at_time
