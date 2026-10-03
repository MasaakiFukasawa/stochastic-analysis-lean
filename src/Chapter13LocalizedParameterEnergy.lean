import Chapter13ParameterEnergyLocalizers
import Chapter13ParameterStoppedEnergy

open MeasureTheory Set
namespace Asakura.Chapter13
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- The stopped energy bound used by HJM Fubini follows from the original
pathwise local bound, with no expectation hypothesis on the unstopped field. -/
theorem localized_parameter_energy {Ω E:Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (F:HalfClosedTime → MeasurableSpace Ω) (hF:Monotone F)
    (μ:Measure E) [IsFiniteMeasure μ] (R:ℝ) (hR:0≤R) (H:E × (Ω × ℝ) → ℝ) (hm:Measurable H)
    (hp:@Measurable _ _
      ((inferInstance : MeasurableSpace E).prod (progressiveSpace (fun t:Icc (0:ℝ) R => F (realTimeClamp t.val)))) inferInstance
      (fun z:E × (Ω × Icc (0:ℝ) R) => H (z.1,(z.2.1,z.2.2.val))))
    (hb:∀w,∃K:ℝ,0≤K ∧ ∀x r,r∈Icc 0 R → |H (x,(w,r))|≤K) :
    ∃τ:ℕ → Ω → HalfClosedTime,
      (∀n t,MeasurableSet[F t] {w | τ n w≤t}) ∧
      (∀w,∃N:ℕ,∀n,N≤n → τ n w=⊤) ∧
      ∀n w,
        let q := (finitePrefixTime R hR (τ n w)).val
        let K := fun z:E × ℝ => (Ioc 0 q).indicator (fun r => H (z.1,(w,r))) z.2
        Integrable (fun z => K z^2) (μ.prod (volume.restrict (Ioi 0))) ∧
        (∫z,K z^2∂μ.prod (volume.restrict (Ioi 0)))≤(n:ℝ)+1 := by
  obtain ⟨C,τ,hCe,hτ,hmono,hbound,htop⟩ := parameter_energy_localizers F hF μ R hR H hm hp hb
  refine ⟨τ,hτ,htop,?_⟩
  intro n w q K
  obtain ⟨a,ha,hwa⟩ := hb w
  have hi := bounded_parameter_time_energy μ R (fun z:E × ℝ => H (z.1,(w,z.2)))
    (hm.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))) a ha hwa
  obtain ⟨hki,hke⟩ := parameter_stopped_energy μ R q (finitePrefixTime R hR (τ n w)).property _ hi
  refine ⟨hki,?_⟩
  change (∫z,((Ioc 0 q).indicator (fun r => H (z.1,(w,r))) z.2)^2∂μ.prod (volume.restrict (Ioi 0)))≤_
  rw [hke,←hCe]
  simpa using hbound n w ⊤
end Asakura.Chapter13
#print axioms Asakura.Chapter13.localized_parameter_energy
