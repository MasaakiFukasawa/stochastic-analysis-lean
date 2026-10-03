import FullAuditConditionalLimit

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter10
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- Almost-sure limits of history-measurable variables remain measurable
when the history contains all ambient null events. -/
theorem completed_ae_limit_measurable {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) (G : MeasurableSpace Ω) (hG : G≤m)
    (hnull : ∀ E,MeasurableSet[m] E → P E=0 → MeasurableSet[G] E)
    (f : ℕ → Ω → ℝ) (Z : Ω → ℝ) (hf : ∀ n,Measurable[G] (f n))
    (hZ : Measurable[m] Z) (hl : ∀ᵐ w ∂P,Tendsto (fun n => f n w) atTop (𝓝 (Z w))) :
    Measurable[G] Z := by
  letI : MeasurableSpace Ω := m
  obtain ⟨E,hE,hm,h0⟩ := exists_measurable_superset_of_null (ae_iff.mp hl)
  have hEG := hnull E hm h0
  let g := Eᶜ.indicator Z
  have hg : Measurable[G] g := by
    letI : MeasurableSpace Ω := G
    apply measurable_of_tendsto_metrizable (fun n => (hf n).indicator hEG.compl)
    apply tendsto_pi_nhds.mpr
    intro w
    by_cases hw : w∈E
    · simpa only [Set.indicator_of_notMem (show w∉Eᶜ from by simpa only [mem_compl_iff,not_not] using hw),g] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))
    · have hc : Tendsto (fun n => f n w) atTop (𝓝 (Z w)) := by
        by_contra h
        exact hw (hE h)
      simpa only [Set.indicator_of_mem (show w∈Eᶜ from hw),g] using hc
  apply Asakura.FullAudit.measurable_of_augmented_ae P hG hnull Z g hZ hg
  filter_upwards [show ∀ᵐ w ∂P,w∉E from ae_iff.mpr (by simpa only [not_not,Set.ofPred_mem_eq] using h0)] with w hw
  simp only [g,Set.indicator_of_mem (show w∈Eᶜ from hw)]

end Asakura.Chapter10
