import Chapter2IntegrableTerminalVariation
import Chapter2EnergyNorm

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- L2 continuity at every time, including the terminal time, follows
from continuous paths and the proved L2 Doob bound. -/
theorem continuous_m2_time_l2_continuity
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (X : ClosedTime T → Ω → ℝ) (hX : ContinuousM2Witness P F X) (s : ClosedTime T) :
    Tendsto (fun t => eLpNorm (X t-X s) 2 P) (𝓝 s) (𝓝 0) := by
  let R := continuousPath X hX.path
  have hR := continuous_martingale_path_memLp P F hF hle X hX.adapted hX.moment hX.path hX.martingale
  have hRi := (memLp_two_iff_integrable_sq_norm hR.aestronglyMeasurable).1 hR
  have hbound t : ∀ᵐ ω ∂P, ‖(X t ω-X s ω)^2‖ ≤ 4*‖R ω‖^2 := by
    apply ae_of_all
    intro ω
    have ht := (R ω).norm_coe_le_norm t
    have hs := (R ω).norm_coe_le_norm s
    have hd := norm_sub_le (X t ω) (X s ω)
    change ‖X t ω‖ ≤ ‖R ω‖ at ht
    change ‖X s ω‖ ≤ ‖R ω‖ at hs
    have hle' : ‖X t ω-X s ω‖ ≤ 2*‖R ω‖ := by linarith
    have hh := pow_le_pow_left₀ (norm_nonneg _) hle' 2
    simpa only [norm_pow,mul_pow,show (2:ℝ)^2 = 4 by norm_num] using hh
  have hp := tendsto_integral_filter_of_dominated_convergence (μ := P) (fun ω => 4*‖R ω‖^2)
    (F := fun t ω => (X t ω-X s ω)^2) (f := fun _ => (0:ℝ))
    (.of_forall fun t => ((((hX.adapted t).mono (hle t) le_rfl).sub ((hX.adapted s).mono (hle s) le_rfl)).pow_const 2).aestronglyMeasurable)
    (.of_forall hbound) (hRi.const_mul 4) (.of_forall fun ω => by
      have h := (((hX.path ω).tendsto s).sub_const (X s ω)).pow 2
      simpa only [sub_self,zero_pow (by norm_num : (2:ℕ) ≠ 0)] using h)
  simp only [integral_zero] at hp
  have he := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hp
  have hr := (ENNReal.continuous_rpow_const (y := 1/(2:ℝ))).continuousAt.tendsto.comp he
  simp only [Function.comp_def,ENNReal.ofReal_zero,ENNReal.zero_rpow_of_pos (by norm_num : (0:ℝ) < 1/2)] at hr
  have hnorm t := real_eLpNorm_two_energy P (X t-X s) ((hX.moment t).sub (hX.moment s))
  simpa only [hnorm,Pi.sub_apply] using hr

/-- Once the terminal M2 extension is constructed, the L2 limit holds
along all times approaching T from below, not only along the chosen sequence. -/
theorem terminal_l2_limit_all_times
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (X Y : ClosedTime T → Ω → ℝ) (hY : ContinuousM2Witness P F Y)
    (he : ∀ t, t < ⊤ → Y t =ᵐ[P] X t) :
    Tendsto (fun t => eLpNorm (X t-Y ⊤) 2 P) (𝓝[<] (⊤ : ClosedTime T)) (𝓝 0) := by
  have h : Tendsto (fun t => eLpNorm (Y t-Y ⊤) 2 P) (𝓝[<] (⊤ : ClosedTime T)) (𝓝 0) :=
    (continuous_m2_time_l2_continuity P F hF hle Y hY ⊤).mono_left nhdsWithin_le_nhds
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact eLpNorm_congr_ae ((he t ht).sub (.rfl))

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.continuous_m2_time_l2_continuity
#print axioms Asakura.Chapter2Complete.terminal_l2_limit_all_times
