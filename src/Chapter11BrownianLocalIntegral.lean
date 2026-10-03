import Chapter5LocalPathBrownianIntegral
import Chapter4BrownianSystem

open MeasureTheory Set
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5
set_option maxHeartbeats 3000000

/-- The actual locally square-integrable Brownian integral, with the
 auxiliary exhaustion constructed internally. -/
theorem brownian_local_integral {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (H : Ω × ℝ → ℝ) (hm : Measurable H)
    (hp : ∀ d,0<d → @Measurable _ _
      (progressiveSpace (fun t : Icc (0:ℝ) d => B.F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) d => H (z.1,z.2.val)))
    (hi : ∀ d,0≤d → ∀ᵐ w ∂P,IntervalIntegrable (fun r => H (w,r)^2) volume 0 d) :
    ∃ N : HalfClosedTime → Ω → ℝ,LocalMProcessWitness P B.F N ∧ ItoCovarianceFormula P B.F (B.W 0) H N := by
  have hT : (0:EReal)<⊤ := by simp
  obtain ⟨c,hc,hcm,hcT,hct,hcut,hcc⟩ := positive_real_time_exhaustion hT
  exact brownian_local_path_energy_integral_constructed P hT B.F B.mono B.le B.null
    (B.W 0) (B.C 0 0) (B.martingale 0) (B.cov 0 0) c hc hcm hcT hct hcut hcc
    (fun _ w r hr => B.diagonal_clock 0 w r hr.1) H hm (fun n => hp (c n) (hc n))
    (fun n => hi (c n) (hc n).le)

end Asakura.Chapter11
