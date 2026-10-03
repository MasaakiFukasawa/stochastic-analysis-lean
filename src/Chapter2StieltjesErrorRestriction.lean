import Chapter2StieltjesRestriction
import Chapter2ProbabilityErrorSum

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- Convergence of the nonnegative approximation energy on a finite
horizon implies convergence on every smaller horizon, for the actual
Stieltjes measures. -/
theorem stieltjes_error_probability_restriction
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (b d : ℝ) (hd : 0 ≤ d) (hdb : d ≤ b)
    (A : Ω → ℝ → ℝ)
    (hAb : ∀ ω, MonotoneOn (A ω) (Icc 0 b))
    (hAd : ∀ ω, MonotoneOn (A ω) (Icc 0 d))
    (hrb : ∀ ω r, r ∈ Icc 0 b → ContinuousWithinAt (A ω) (Icc 0 b ∩ Ici r) r)
    (hrd : ∀ ω r, r ∈ Icc 0 d → ContinuousWithinAt (A ω) (Icc 0 d ∩ Ici r) r)
    (R : ℕ → Ω → ℝ → ℝ)
    (hi : ∀ n, ∀ᵐ ω ∂P, Integrable (R n ω)
      (intervalStieltjes 0 b (hd.trans hdb) (A ω) (hAb ω) (hrb ω)).measure)
    (hn : ∀ n ω r, 0 ≤ R n ω r)
    (hp : ∀ ε > 0, Tendsto (fun n => P {ω | ε ≤ ∫ r, R n ω r
      ∂(intervalStieltjes 0 b (hd.trans hdb) (A ω) (hAb ω) (hrb ω)).measure}) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => P {ω | ε ≤ ∫ r, R n ω r
      ∂(intervalStieltjes 0 d hd (A ω) (hAd ω) (hrd ω)).measure}) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hp ε hε) (fun _ => bot_le)
  intro n
  apply measure_mono_ae
  filter_upwards [hi n] with ω hiω
  intro hω
  have he := interval_stieltjes_restrict_Iic 0 b d hd hdb (A ω) (hAb ω) (hrb ω) (hAd ω) (hrd ω)
  rw [he] at hω
  exact hω.trans (setIntegral_le_integral hiω (.of_forall (hn n ω)))

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.stieltjes_error_probability_restriction
