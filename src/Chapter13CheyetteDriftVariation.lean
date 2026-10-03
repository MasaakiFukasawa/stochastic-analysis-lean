import Chapter5ProgressiveDriftVariation
import Chapter2ContinuousIntegrand
import Chapter12ConditionalTensor

open MeasureTheory Set
namespace Asakura.Chapter13
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter5
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- The second time integral in the Cheyette state is an actual adapted
continuous finite-variation process, derived from the original drivers. -/
theorem cheyette_double_primitive_variation {Ω:Type*}
    (F:HalfClosedTime → MeasurableSpace Ω) (hF:Monotone F)
    (R:ℝ) (hR:0≤R) (A:Ω × ℝ → ℝ)
    (hp:@Measurable _ _ (progressiveSpace (fun t:Icc (0:ℝ) R => F (realTimeClamp t.val))) inferInstance
      (fun z:Ω × Icc (0:ℝ) R => A (z.1,z.2.val)))
    (hi:∀w,IntervalIntegrable (fun r => A (w,r)) volume 0 R)
    (g:ℝ → ℝ) (hgm:Measurable g) (hgi:IntervalIntegrable g volume 0 R) :
    ∃D:HalfClosedTime → Ω → ℝ,AdaptedLocalVariationWitness F D ∧
      (∀w,Continuous (fun t => D t w)) ∧
      ∀t w,D t w=∫r in 0..(finitePrefixTime R hR t).val,(∫s in 0..r,A (w,s))*g r := by
  have hcont w:ContinuousOn (fun r => ∫s in 0..r,A (w,s)) (Icc 0 R) := by
    simpa only [uIcc_of_le hR] using
      ((hi w).absolutelyContinuousOnInterval_intervalIntegral (c:=0) left_mem_uIcc).continuousOn
  have hprog:=continuous_adapted_real_progressive F hF (fun z => ∫s in 0..z.2,A (z.1,s)) R hR
    (fun r hr => progressive_time_primitive_adapted R hR _ A hp ⟨r,hr⟩) hcont
  have hgprog:=Asakura.Chapter12.deterministic_time_progressive
    (fun t:Icc (0:ℝ) R => F (realTimeClamp t.val)) (fun t => g t.val)
    (hgm.comp measurable_subtype_coe)
  have hd:∀w,Integrable (fun r => (∫s in 0..r,A (w,s))*g r) (volume.restrict (Ioc 0 R)) := by
    intro w
    have hh:=hgi.continuousOn_mul (by simpa only [uIcc_of_le hR] using hcont w)
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hR).mp hh
  exact progressive_integrable_drift_variation (by simp : (0:EReal)<⊤) F hF R hR le_top
    (fun z => (∫s in 0..z.2,A (z.1,s))*g z.2) (hprog.mul hgprog) hd
end Asakura.Chapter13
#print axioms Asakura.Chapter13.cheyette_double_primitive_variation
