import Chapter7ClockHalfTime
import Chapter7NullEventTransfer
import Chapter7RightClockStopping

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- Right continuity of the original filtration identifies the sigma algebra
at a decreasing limit of stopping times. -/
theorem stopped_space_decreasing_limit
    {Ω : Type*} (m : MeasurableSpace Ω)
    {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F)
    (hright : ∀ t,t < ⊤ → F t = ⨅ s : Ioi t,F s.val)
    (τ : ℕ → Ω → ClosedTime T) (σ : Ω → ClosedTime T)
    (hτ : ∀ n t,MeasurableSet[F t] {w | τ n w ≤ t})
    (hσ : ∀ t,MeasurableSet[F t] {w | σ w ≤ t})
    (hle : ∀ n w,σ w ≤ τ n w)
    (hlim : ∀ w,Tendsto (fun n => τ n w) atTop (𝓝 (σ w))) :
    writtenStoppedSpace m F σ hσ = ⨅ n,writtenStoppedSpace m F (τ n) (hτ n) := by
  apply le_antisymm
  · apply le_iInf
    intro n
    exact written_stoppedSpace_mono m F σ (τ n) hσ (hτ n) (hle n)
  · intro E hE
    have hEn n := (MeasurableSpace.measurableSet_iInf.mp hE) n
    refine ⟨(hEn 0).1,?_⟩
    intro t
    by_cases ht : t < ⊤
    · rw [hright t ht]
      apply MeasurableSpace.measurableSet_iInf.mpr
      intro s
      have hu : MeasurableSet[F s.val] (⋃ n,E ∩ {w | τ n w ≤ s.val}) :=
        MeasurableSet.iUnion (fun n => (hEn n).2 s.val)
      have he : E ∩ {w | σ w ≤ t} = (⋃ n,E ∩ {w | τ n w ≤ s.val}) ∩ {w | σ w ≤ t} := by
        ext w
        simp only [mem_inter_iff,mem_setOf_eq,mem_iUnion]
        constructor
        · rintro ⟨hew,hw⟩
          have hs : σ w < s.val := hw.trans_lt s.property
          have hev := (tendsto_order.mp (hlim w)).2 s.val hs
          obtain ⟨n,hn⟩ := hev.exists
          exact ⟨⟨n,hew,hn.le⟩,hw⟩
        · rintro ⟨⟨n,hew,_⟩,hw⟩
          exact ⟨hew,hw⟩
      rw [he]
      exact hu.inter (hF s.property.le _ (hσ t))
    · have he : t = ⊤ := top_le_iff.mp (le_of_not_gt ht)
      subst t
      simpa only [Set.setOf_true,Set.inter_univ,le_top] using (hEn 0).2 ⊤

/-- A continuous increasing change of stopping times preserves right
continuity of the filtration. -/
theorem stopped_clock_right_continuous
    {Ω : Type*} (m : MeasurableSpace Ω)
    {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F)
    (hright : ∀ t,t < ⊤ → F t = ⨅ s : Ioi t,F s.val)
    (τ : ℝ → Ω → ClosedTime T)
    (hτ : ∀ r t,MeasurableSet[F t] {w | τ r w ≤ t})
    (hm : ∀ w,Monotone (fun r => τ r w))
    (hc : ∀ w,Continuous (fun r => τ r w)) (r : ℝ) :
    writtenStoppedSpace m F (τ r) (hτ r) =
      ⨅ s : Ioi r,writtenStoppedSpace m F (τ s.val) (hτ s.val) := by
  let u := fun n : ℕ => r+1/(n+1:ℝ)
  have hu n : r < u n := lt_add_of_pos_right r (by positivity)
  have hl : Tendsto u atTop (𝓝 r) := by
    simpa only [add_zero] using (tendsto_const_nhds (x := r)).add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hH : Monotone (fun r => writtenStoppedSpace m F (τ r) (hτ r)) :=
    fun a b hab => written_stoppedSpace_mono m F (τ a) (τ b) (hτ a) (hτ b) (fun w => hm w hab)
  rw [← right_filtration_countable_intersection _ hH r u hu hl]
  exact stopped_space_decreasing_limit m F hF hright (fun n => τ (u n)) (τ r)
    (fun n => hτ (u n)) (hτ r) (fun n w => hm w (hu n).le)
    (fun w => (hc w).continuousAt.tendsto.comp hl)

end Asakura.Chapter7
