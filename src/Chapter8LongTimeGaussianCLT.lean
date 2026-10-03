import Chapter8LongTimeScalarCLT
import Chapter7DistributionLawTransfer

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
namespace Asakura.Chapter8
set_option backward.isDefEq.respectTransparency false
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
  Asakura.Chapter4 Asakura.Chapter7

/-- Identify the Brownian terminal variable produced by the time-change
proof with the canonical normal law of variance c. -/
theorem long_time_scalar_gaussian_clt {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t ≤ m)
    (M C : HalfClosedTime → Ω → ℝ)
    (hM : LocalMProcessWitness P F M) (hC : LocalCovarianceWitness P F M M C)
    (c : ℝ) (hc : 0 < c)
    (havg : TendstoInMeasure P (fun T ω => C (realTimeClamp T) ω/T) atTop (fun _ => c))
    (T : ℕ → ℝ) (hT : ∀ n,0 < T n) (hTlim : Tendsto T atTop atTop) :
    TendstoInDistribution (fun n ω => M (realTimeClamp (T n)) ω/Real.sqrt (T n)) atTop
      id (fun _ => P) (gaussianReal 0 ⟨c,hc.le⟩) := by
  obtain ⟨Γ,q,Q,hQ,B,hd⟩ := long_time_scalar_clt P F hF hle M C hM hC c hc havg T hT hTlim
  letI := q
  letI := hQ
  have hl := scaled_brownian_gaussian_law (P.prod Q) B c 1 hc.le zero_le_one
  have hl' : HasLaw (fun z => Real.sqrt c*B.W 0 (realTimeClamp 1) z)
      (gaussianReal 0 ⟨c,hc.le⟩) (P.prod Q) := by simpa only [mul_one] using hl
  exact distribution_limit_same_law P (P.prod Q) (gaussianReal 0 ⟨c,hc.le⟩) hd hl'
    ⟨measurable_id.aemeasurable,Measure.map_id⟩

end Asakura.Chapter8
