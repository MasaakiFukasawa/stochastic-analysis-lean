import Chapter11SignedStepCumulative

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter2Complete
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- The same L1 error controls every cutoff of the actual signed integral. -/
theorem signed_cumulative_difference_bound (ν : SignedMeasure ℝ) (μ : Measure ℝ)
    (hμ : ν.totalVariation≤μ) (f g : ℝ → ℝ) (hf : Integrable f μ) (hg : Integrable g μ) (d : ℝ) :
    |signedCumulative ν f d-signedCumulative ν g d|≤∫ r,|f r-g r| ∂μ := by
  have hfi := hf.mono_measure hμ
  have hgi := hg.mono_measure hμ
  have hi := (hfi.sub hgi).indicator (measurableSet_Iic (a:=d))
  have he : (fun r => (Iic d).indicator f r-(Iic d).indicator g r)=(Iic d).indicator (fun r => f r-g r) := by
    funext r
    by_cases hr : r∈Iic d <;> simp [hr]
  have h := signed_integral_absolute_bound ν ((Iic d).indicator (fun r => f r-g r)) hi
  rw [←he,signed_integral_sub ν _ _ (hfi.indicator measurableSet_Iic) (hgi.indicator measurableSet_Iic)] at h
  apply h.trans
  rw [he]
  apply le_trans (integral_mono (hi.abs) ((hfi.sub hgi).abs) ?_)
    (integral_mono_measure hμ (ae_of_all _ fun r => abs_nonneg _) ((hf.sub hg).abs))
  intro r
  by_cases hr : r∈Iic d <;> simp [he,hr,abs_nonneg]

/-- Probability convergence of the variation component follows from its
 pathwise L1 error; no expectation of the total-variation mass is required. -/
theorem signed_cumulative_probability_limit {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (ν : Ω → SignedMeasure ℝ) (μ : Ω → Measure ℝ)
    (hμ : ∀ᵐ w ∂P,(ν w).totalVariation≤μ w)
    (J : ℕ → Ω → ℝ → ℝ) (H : Ω → ℝ → ℝ)
    (hJ : ∀ n,∀ᵐ w ∂P,Integrable (J n w) (μ w)) (hH : ∀ᵐ w ∂P,Integrable (H w) (μ w))
    (hp : ∀ ε>0,Tendsto (fun n => P {w | ε≤∫ r,|J n w r-H w r| ∂μ w}) atTop (𝓝 0))
    (d : Ω → ℝ) :
    ∀ ε>0,Tendsto (fun n => P {w | ε≤|signedCumulative (ν w) (J n w) (d w)-signedCumulative (ν w) (H w) (d w)|}) atTop (𝓝 0) := by
  intro ε hε
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hp ε hε) (fun _ => bot_le)
  intro n
  apply measure_mono_ae
  filter_upwards [hμ,hJ n,hH] with w hm hj hh
  intro hw
  exact hw.trans (signed_cumulative_difference_bound (ν w) (μ w) hm (J n w) (H w) hj hh (d w))

end Asakura.Chapter11
