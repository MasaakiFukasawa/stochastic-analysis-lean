import Chapter2PathProbabilityMetric
import Chapter2TimeExhaustion
import Chapter2LocalCompleteness
import Chapter2LenglartConvergence

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem interval_stage_distance_le_stopped_sup
    {T : EReal} [Fact (0 ≤ T)]
    (u : ℕ → ClosedTime T) (hu : StrictMono u) (hut : ∀ n, u n < ⊤)
    (huc : ∀ t, t < ⊤ → ∃ n, t < u n)
    (f g : C(Iio (⊤ : ClosedTime T),ℝ)) (j : ℕ) :
    compactStageDist (intervalTimeExhaustion u hu hut huc) j f g ≤
      ⨆ t, |extendOpenPath f (min (u j) t)-extendOpenPath g (min (u j) t)| := by
  let K := intervalTimeExhaustion u hu hut huc
  letI : CompactSpace (K j) := isCompact_iff_compactSpace.1 (K.isCompact j)
  let D : C(ClosedTime T,ℝ) := ⟨fun t => extendOpenPath f (min (u j) t)-extendOpenPath g (min (u j) t),by
    apply continuous_iff_continuousAt.2
    intro t
    exact ((extendOpenPath_continuousAt f _ ((min_le_left _ _).trans_lt (hut j))).sub
      (extendOpenPath_continuousAt g _ ((min_le_left _ _).trans_lt (hut j)))).comp
        (continuous_const.min continuous_id).continuousAt⟩
  have he : ‖D‖ = ⨆ t, |extendOpenPath f (min (u j) t)-extendOpenPath g (min (u j) t)| := by
    rw [ContinuousMap.norm_eq_iSup_norm]
    rfl
  rw [← he]
  change dist (f.restrict (K j)) (g.restrict (K j)) ≤ ‖D‖
  rw [dist_eq_norm]
  apply (ContinuousMap.norm_le _ (norm_nonneg D)).2
  intro t
  have ht : t.val.val ≤ u j := t.property
  have h := D.norm_coe_le_norm t.val.val
  change ‖extendOpenPath f (min (u j) t.val.val)-extendOpenPath g (min (u j) t.val.val)‖ ≤ ‖D‖ at h
  rw [min_eq_right ht] at h
  have htt : t.val.val < ⊤ := t.val.property
  dsimp only [extendOpenPath] at h
  rw [dif_pos htt,dif_pos htt] at h
  exact h

/-- A quadratic-variation Cauchy criterion yields an actual local
martingale limit. It combines the proved Lenglart bounds, the printed
expectation metric, and the constructed completeness of M_loc. -/
theorem local_martingale_limit_of_quadratic_cauchy
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (u : ℕ → ClosedTime T) (hu : StrictMono u) (hut : ∀ n, u n < ⊤)
    (huc : ∀ t, t < ⊤ → ∃ n, t < u n)
    (X : ℕ → Ω → C(Iio (⊤ : ClosedTime T),ℝ))
    (hX : ∀ n, LocalMProcessWitness P F (fun t ω => extendOpenPath (X n ω) t))
    (Q : ℕ → ℕ → ClosedTime T → Ω → ℝ)
    (hQ : ∀ n k, LocalCovarianceWitness P F
      (fun t ω => extendOpenPath (X n ω) t-extendOpenPath (X k ω) t)
      (fun t ω => extendOpenPath (X n ω) t-extendOpenPath (X k ω) t) (Q n k))
    (hsmall : ∀ a b : ℕ → ℕ, (∀ n, n ≤ a n) → (∀ n, n ≤ b n) →
      ∀ j (δ : ℝ), 0 < δ → Tendsto (fun n => P {ω | δ ≤ Q (a n) (b n) (u j) ω}) atTop (𝓝 0)) :
    ∃ Y : Ω → C(Iio (⊤ : ClosedTime T),ℝ),
      LocalMProcessWitness P F (fun t ω => extendOpenPath (Y ω) t) ∧
      Tendsto (fun n => ∫ ω, pathDistance (intervalTimeExhaustion u hu hut huc) (X n ω) (Y ω) ∂P) atTop (𝓝 0) := by
  let K := intervalTimeExhaustion u hu hut huc
  letI : LocallyCompactSpace (Iio (⊤ : ClosedTime T)) := isOpen_Iio.locallyCompactSpace
  have hm n := local_martingale_path_measurable P F hle (X n) (hX n)
  apply local_martingale_cauchy_limit P hT F hF hle hnull K X hX
  apply cauchy_bound_of_all_tail_sequences
  intro a b ha hb
  apply path_metric_limit_of_probability P K (fun n => X (a n)) (fun n => X (b n))
    (fun n => hm (a n)) (fun n => hm (b n))
  intro j ε hε
  let Z := fun n t ω => extendOpenPath (X (a n) ω) t-extendOpenPath (X (b n) ω) t
  have hZ n : LocalMProcessWitness P F (Z n) := by
    have h := (hX (a n)).add P F hF hle ((hX (b n)).smul P F (-1))
    convert h using 1
    funext t ω
    change _-_ = _+(-1)*_
    ring
  have hσ t : MeasurableSet[F t] {ω : Ω | u j ≤ t} := by
    by_cases ht : u j ≤ t <;> simp [ht]
  have hl := local_martingale_probability_of_quadratic_variation P F hF hle hnull Z
    (fun n => Q (a n) (b n)) hZ (fun n => hQ (a n) (b n)) (fun _ => u j) hσ (fun _ => hut j)
    (hsmall a b ha hb j) ε hε
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hl (fun _ => bot_le)
  intro n
  apply measure_mono
  intro ω hω
  exact hω.trans (interval_stage_distance_le_stopped_sup u hu hut huc (X (a n) ω) (X (b n) ω) j)

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.interval_stage_distance_le_stopped_sup
#print axioms Asakura.Chapter2Complete.local_martingale_limit_of_quadratic_cauchy
