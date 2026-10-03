import Chapter2PathMetricSubsequence
import Chapter2QuadraticCauchyLimit

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter2Written
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

theorem stage_probability_limit_of_path_metric
    {Ω D : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    [TopologicalSpace D] [T2Space D] [LocallyCompactSpace D] [SecondCountableTopology D]
    (K : CompactExhaustion D) (X Y : ℕ → Ω → C(D,ℝ))
    (hX : ∀ n, Measurable (X n)) (hY : ∀ n, Measurable (Y n))
    (hp : Tendsto (fun n => ∫ ω, pathDistance K (X n ω) (Y n ω) ∂P) atTop (𝓝 0))
    (j : ℕ) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => P {ω | ε ≤ compactStageDist K j (X n ω) (Y n ω)}) atTop (𝓝 0) := by
  let δ := min (ε/2) 1
  have hδ : 0 < δ := lt_min (half_pos hε) zero_lt_one
  have hδε : δ < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
  have hb n := path_distance_stage_probability P K (X n) (Y n) (hX n) (hY n) j δ hδ (min_le_right _ _)
  have hl := ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hp.div_const ((1/2:ℝ)^(j+1)*δ))
  simp only [zero_div,ENNReal.ofReal_zero] at hl
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hl (fun _ => bot_le)
  intro n
  exact (measure_mono (fun ω hω => hδε.trans_le hω)).trans (hb n)

theorem stopped_sup_le_interval_stage_distance
    {T : EReal} [Fact (0 ≤ T)]
    (u : ℕ → ClosedTime T) (hu : StrictMono u) (hut : ∀ n, u n < ⊤)
    (huc : ∀ t, t < ⊤ → ∃ n, t < u n)
    (f g : C(Iio (⊤ : ClosedTime T),ℝ)) (j : ℕ) :
    (⨆ t, |extendOpenPath f (min (u j) t)-extendOpenPath g (min (u j) t)|) ≤
      compactStageDist (intervalTimeExhaustion u hu hut huc) j f g := by
  let K := intervalTimeExhaustion u hu hut huc
  letI : CompactSpace (K j) := isCompact_iff_compactSpace.1 (K.isCompact j)
  apply ciSup_le
  intro t
  let s : Iio (⊤ : ClosedTime T) := ⟨min (u j) t,(min_le_left _ _).trans_lt (hut j)⟩
  let r : K j := ⟨s,by change min (u j) t ≤ u j; exact min_le_left _ _⟩
  have h := ContinuousMap.norm_coe_le_norm (f.restrict (K j)-g.restrict (K j)) r
  change |f s-g s| ≤ ‖f.restrict (K j)-g.restrict (K j)‖ at h
  change _ ≤ dist (f.restrict (K j)) (g.restrict (K j))
  rw [dist_eq_norm]
  have htt : min (u j) t < ⊤ := (min_le_left _ _).trans_lt (hut j)
  dsimp only [extendOpenPath]
  rw [dif_pos htt,dif_pos htt]
  exact h

/-- The topology used in constructing the Ito integral implies precisely
the stopped uniform probability convergence needed by Lenglart. -/
theorem stopped_probability_limit_of_path_metric
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)]
    (u : ℕ → ClosedTime T) (hu : StrictMono u) (hut : ∀ n, u n < ⊤)
    (huc : ∀ t, t < ⊤ → ∃ n, t < u n)
    (X Y : ℕ → Ω → C(Iio (⊤ : ClosedTime T),ℝ))
    (hX : ∀ n, Measurable (X n)) (hY : ∀ n, Measurable (Y n))
    (hp : Tendsto (fun n => ∫ ω, pathDistance (intervalTimeExhaustion u hu hut huc)
      (X n ω) (Y n ω) ∂P) atTop (𝓝 0))
    (j : ℕ) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => P {ω | ε ≤ ⨆ t,
      |extendOpenPath (X n ω) (min (u j) t)-extendOpenPath (Y n ω) (min (u j) t)|}) atTop (𝓝 0) := by
  letI : LocallyCompactSpace (Iio (⊤ : ClosedTime T)) := isOpen_Iio.locallyCompactSpace
  have h := stage_probability_limit_of_path_metric P (intervalTimeExhaustion u hu hut huc) X Y hX hY hp j ε hε
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => bot_le)
  intro n
  exact measure_mono (fun ω hω => hω.trans (stopped_sup_le_interval_stage_distance u hu hut huc (X n ω) (Y n ω) j))

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.stage_probability_limit_of_path_metric
#print axioms Asakura.Chapter2Complete.stopped_sup_le_interval_stage_distance
#print axioms Asakura.Chapter2Complete.stopped_probability_limit_of_path_metric
