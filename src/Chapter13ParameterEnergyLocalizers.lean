import Chapter13ParameterEnergy
import Chapter13BoundedParameterEnergy

open MeasureTheory Set
namespace Asakura.Chapter13
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- HJM localization from the original joint coefficient and pathwise bound.
No expected bound on the original volatility is assumed. -/
theorem parameter_energy_localizers {Ω E:Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (F:HalfClosedTime → MeasurableSpace Ω) (hF:Monotone F)
    (μ:Measure E) [IsFiniteMeasure μ] (R:ℝ) (hR:0≤R) (H:E × (Ω × ℝ) → ℝ) (hm:Measurable H)
    (hp:@Measurable _ _
      ((inferInstance : MeasurableSpace E).prod (progressiveSpace (fun t:Icc (0:ℝ) R => F (realTimeClamp t.val)))) inferInstance
      (fun z:E × (Ω × Icc (0:ℝ) R) => H (z.1,(z.2.1,z.2.2.val))))
    (hb:∀w,∃K:ℝ,0≤K ∧ ∀x r,r∈Icc 0 R → |H (x,(w,r))|≤K) :
    ∃(C:HalfClosedTime → Ω → ℝ) (τ:ℕ → Ω → HalfClosedTime),
      (∀t w,C t w=∫r in 0..(finitePrefixTime R hR t).val,∫x,H (x,(w,r))^2∂μ) ∧
      (∀n t,MeasurableSet[F t] {w | τ n w≤t}) ∧
      (∀w,Monotone (fun n => τ n w)) ∧
      (∀n w t,C (min (τ n w) t) w≤(n:ℝ)+1) ∧
      (∀w,∃N:ℕ,∀n,N≤n → τ n w=⊤) := by
  have hi w:Integrable (fun z:E × ℝ => H (z.1,(w,z.2))^2) (μ.prod (volume.restrict (Ioc 0 R))) := by
    obtain ⟨K,hK,hb⟩:=hb w
    exact bounded_parameter_time_energy μ R _
      (hm.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))) K hK hb
  obtain ⟨C,hCm,hCc,hC0,hCb,hCe⟩:=parameter_energy_constructed F hF μ R hR H hp hi
  have hh:=bounded_energy_localizers F hF C hCm hCc hC0
    (fun w => ∫r in 0..R,∫x,H (x,(w,r))^2∂μ) hCb
  exact ⟨C,_,hCe,hh⟩
end Asakura.Chapter13
#print axioms Asakura.Chapter13.parameter_energy_localizers
