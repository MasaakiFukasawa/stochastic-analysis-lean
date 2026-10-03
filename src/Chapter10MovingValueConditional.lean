import Chapter10NoiseMartingale

open MeasureTheory Set Filter
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- In the moving-value exercise the future dividend may be replaced by
the present value when conditioning on the market's smaller information.
The value martingale is obtained from its actual Brownian integral. -/
theorem moving_value_conditional_reduction {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ} (B : BrownianSystem P n)
    (j : Fin n) (γ : ℝ → ℝ) (hγ : Continuous γ)
    (N : HalfClosedTime → Ω → ℝ) (hN : LocalMProcessWitness P B.F N)
    (hNI : ItoCovarianceFormula P B.F (B.W j) (fun z => γ z.2) N)
    (V0 : Ω → ℝ) (hV0 : Measurable[B.F ⊥] V0) (hV2 : MemLp V0 2 P)
    (s t : ℝ) (hs : 0≤s) (hst : s≤t)
    (H : MeasurableSpace Ω) (hH : H≤B.F (realTimeClamp s)) :
    P[(fun w => V0 w+N (realTimeClamp t) w)|H]=ᵐ[P]
      P[(fun w => V0 w+N (realTimeClamp s) w)|H] := by
  letI : MeasurableSpace Ω := m
  have hM := deterministic_noise_martingale P B j γ hγ N hN hNI t (hs.trans hst)
  have hinc : P[N (realTimeClamp t)|B.F (realTimeClamp s)]=ᵐ[P] N (realTimeClamp s) := by
    simpa only [min_self,min_eq_right (real_time_clamp_mono hst)] using
      hM.martingale (realTimeClamp s) (realTimeClamp t) (real_time_clamp_mono hst)
  have hNt : Integrable (N (realTimeClamp t)) P := by
    simpa only [min_self] using (hM.moment (realTimeClamp t)).integrable (by norm_num)
  have hself := condExp_of_stronglyMeasurable (B.le (realTimeClamp s))
    ((hV0.mono (B.mono bot_le) le_rfl).stronglyMeasurable) (hV2.integrable (by norm_num))
  have hadd := condExp_add (hV2.integrable (by norm_num)) hNt (B.F (realTimeClamp s))
  have he : P[(fun w => V0 w+N (realTimeClamp t) w)|B.F (realTimeClamp s)]=ᵐ[P]
      (fun w => V0 w+N (realTimeClamp s) w) := by
    filter_upwards [hadd,hinc] with w hw hn
    simpa only [Pi.add_apply,hself,hn] using! hw
  exact (condExp_condExp_of_le hH (B.le _)).symm.trans (condExp_congr_ae he)

end Asakura.Chapter10
