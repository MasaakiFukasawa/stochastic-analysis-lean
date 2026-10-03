import Chapter10NoiseMartingale
import FullAuditUnboundedPullout

open MeasureTheory Set Filter
open scoped ENNReal
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- Square-integrable martingale increments are orthogonal to every
square-integrable variable measurable at the earlier time. -/
theorem square_martingale_past_orthogonal {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : HalfClosedTime → MeasurableSpace Ω) (hle : ∀ t,F t≤m)
    (N : HalfClosedTime → Ω → ℝ) (hN : ContinuousMpWitness P F 2 N)
    (s t : HalfClosedTime) (hst : s≤t)
    (η : Ω → ℝ) (hη : Measurable[F s] η) (hη2 : MemLp η 2 P) :
    (∫ w,η w*N t w ∂P)=(∫ w,η w*N s w ∂P) := by
  letI : MeasurableSpace Ω := m
  have hi : Integrable (η*N t) P := hη2.integrable_mul (hN.moment t)
  have hp := unbounded_pullout_by_restriction P (hle s) η (N t) hη.stronglyMeasurable hi
    ((hN.moment t).integrable (by norm_num))
  have he : P[η*N t|F s]=ᵐ[P] fun w => η w*N s w := by
    filter_upwards [hp,hN.martingale s t hst] with w hw hc
    simpa only [Pi.mul_apply,hc] using hw
  have hh := integral_congr_ae he
  rw [integral_condExp (hle s)] at hh
  exact hh

/-- The future part of the actual deterministic Brownian integral is
orthogonal to the full earlier information, not just to earlier noise values. -/
theorem deterministic_noise_past_orthogonal {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ} (B : BrownianSystem P n)
    (j : Fin n) (g : ℝ → ℝ) (hg : Continuous g)
    (N : HalfClosedTime → Ω → ℝ) (hN : LocalMProcessWitness P B.F N)
    (hNI : ItoCovarianceFormula P B.F (B.W j) (fun z => g z.2) N)
    (s t : ℝ) (hs : 0≤s) (hst : s≤t)
    (η : Ω → ℝ) (hη : Measurable[B.F (realTimeClamp s)] η) (hη2 : MemLp η 2 P) :
    (∫ w,η w*N (realTimeClamp t) w ∂P)=(∫ w,η w*N (realTimeClamp s) w ∂P) := by
  letI : MeasurableSpace Ω := m
  have hM := deterministic_noise_martingale P B j g hg N hN hNI t (hs.trans hst)
  have hh := square_martingale_past_orthogonal P B.F B.le _ hM
    (realTimeClamp s) (realTimeClamp t) (real_time_clamp_mono hst) η hη hη2
  simpa only [min_self,min_eq_right (real_time_clamp_mono hst)] using hh

end Asakura.Chapter10
