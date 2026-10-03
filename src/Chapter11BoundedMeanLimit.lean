import Chapter11BoundedStoppedExpectation

open MeasureTheory Filter
open scoped Topology
namespace Asakura.Chapter11

/-- Dominated convergence preserves a fixed expectation; the limit's
 measurability and integrability are consequences, not additional assumptions. -/
theorem bounded_fixed_mean_limit {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : ℕ → Ω → ℝ) (Y : Ω → ℝ)
    (a K : ℝ) (hi : ∀ n,Integrable (Z n) P)
    (he : ∀ n,(∫ w,Z n w ∂P)=a)
    (hb : ∀ n,∀ᵐ w ∂P,|Z n w|≤K)
    (hc : ∀ᵐ w ∂P,Tendsto (fun n => Z n w) atTop (𝓝 (Y w))) :
    Integrable Y P ∧ (∫ w,Y w ∂P)=a := by
  have hm := aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hi n).aestronglyMeasurable) hc
  have hyb : ∀ᵐ w ∂P,|Y w|≤K := by
    filter_upwards [hc,ae_all_iff.mpr hb] with w hw hb
    exact le_of_tendsto hw.abs (Eventually.of_forall hb)
  have hyi : Integrable Y P := Integrable.of_bound hm K
    (hyb.mono fun w hw => by simpa only [Real.norm_eq_abs] using hw)
  have hl := tendsto_integral_of_dominated_convergence (fun _ : Ω => K)
    (fun n => (hi n).aestronglyMeasurable) (integrable_const K)
    (fun n => (hb n).mono fun w hw => by simpa only [Real.norm_eq_abs] using hw) hc
  refine ⟨hyi,tendsto_nhds_unique hl ?_⟩
  simpa only [he] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => a) atTop (𝓝 a))

end Asakura.Chapter11
