import Chapter4RealBorelCoefficientDomain
import Chapter4BrownianSystem

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- Jointly Borel time-dependent coefficients evaluated along a continuous
adapted process are progressive; no continuity of the coefficients is used. -/
theorem time_borel_coefficient_progressive
    {Ω : Type*} [MeasurableSpace Ω] {dim : ℕ}
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F)
    (X : ℝ → Ω → Fin dim → ℝ) (hm : ∀ r,Measurable (X r))
    (hc : ∀ w,Continuous (fun r => X r w))
    (ha : ∀ r,0≤r → Measurable[F (realTimeClamp r)] (X r))
    (b : (Fin dim → ℝ) × ℝ → ℝ) (hb : Measurable b) :
    Measurable (fun z : Ω × ℝ => b (X z.2 z.1,z.2)) ∧
    (∀ c,0≤c → @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) c => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) c => b (X z.2.val z.1,z.2.val))) := by
  refine ⟨hb.comp (((measurable_uncurry_of_continuous_of_measurable hc hm).comp measurable_swap).prodMk measurable_snd),?_⟩
  intro c hc0
  letI : MeasurableSpace (Ω × Icc (0:ℝ) c) := progressiveSpace (fun t : Icc (0:ℝ) c => F (realTimeClamp t.val))
  apply hb.comp
  apply Measurable.prodMk
  · apply measurable_pi_iff.mpr
    intro i
    exact continuous_adapted_real_progressive F hF (fun z => X z.2 z.1 i) c hc0
      (fun r hr => (measurable_pi_apply i).comp (ha r hr.1))
      (fun w => ((continuous_apply i).comp (hc w)).continuousOn)
  · exact continuous_adapted_real_progressive F hF (fun z : Ω × ℝ => z.2) c hc0
      (fun _ _ => measurable_const) (fun _ => continuous_id.continuousOn)

end Asakura.Chapter6
