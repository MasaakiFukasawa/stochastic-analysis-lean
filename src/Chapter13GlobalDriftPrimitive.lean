import Chapter13FiniteDriftVariation
import Chapter4BrownianSystem

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter13
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter4
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

/-- Construct the global local finite-variation primitive from local
pathwise integrability and progressiveness on each finite time interval. -/
theorem global_drift_primitive {Ω:Type*}
    (F:HalfClosedTime → MeasurableSpace Ω) (hF:Monotone F)
    (b:Ω × ℝ → ℝ)
    (hp:∀R,0<R → @Measurable _ _ (progressiveSpace (fun t:Icc (0:ℝ) R => F (realTimeClamp t.val))) inferInstance
      (fun z:Ω × Icc (0:ℝ) R => b (z.1,z.2.val)))
    (hi:∀w R,0≤R → IntervalIntegrable (fun r => b (w,r)) volume 0 R) :
    ∃A:HalfClosedTime → Ω → ℝ,AdaptedLocalVariationWitness F A ∧
      (∀w t,t<⊤ → ContinuousAt (fun s => A s w) t) ∧
      (∀w,A ⊥ w=0) ∧
      ∀w r,0≤r → A (realTimeClamp r) w=∫s in 0..r,b (w,s) := by
  have hT:(0:EReal)<⊤ := by simp
  obtain ⟨c,hc,hcm,hcT,hct,hcut,hcc⟩:=positive_real_time_exhaustion hT
  have hex n:=progressive_integrable_drift_global_variation hT F hF (c n) (hc n).le le_top b
    (hp (c n) (hc n)) (fun w => (intervalIntegrable_iff_integrableOn_Ioc_of_le (hc n).le).mp (hi w (c n) (hc n).le))
  choose D hD hDc hDe using hex
  let A:=fun (t:HalfClosedTime) w => ∫r in 0..(t:EReal).toReal,b (w,r)
  have he n t w:D n t w=A (min (realTimeClamp (c n)) t) w := by
    rw [hDe]
    dsimp only [A,finitePrefixTime]
    congr 1
    change (min (t:EReal) (c n:EReal)).toReal=(min (realTimeClamp (c n):EReal) (t:EReal)).toReal
    rw [real_time_clamp_eq (c n) (hc n).le le_top,min_comm]
  have hv:AdaptedLocalVariationWitness F A := by
    refine ⟨fun n _ => realTimeClamp (c n),?_,fun _ => hct.monotone,fun n _ => hcut n,fun _ => hcc,?_⟩
    · intro n t
      by_cases h:realTimeClamp (T:=(⊤:EReal)) (c n)≤t <;> simp [h]
    · intro n
      convert hD n using 1
      funext t w
      exact (he n t w).symm
  refine ⟨A,hv,?_,?_,?_⟩
  · intro w t ht
    obtain ⟨n,hn⟩:=hcc t ht
    apply (hDc n w).continuousAt.congr_of_eventuallyEq
    filter_upwards [gt_mem_nhds hn] with s hs
    rw [he,min_eq_right hs.le]
  · intro w
    simp [A]
  · intro w r hr
    dsimp only [A]
    rw [real_time_clamp_eq r hr le_top,EReal.toReal_coe]
end Asakura.Chapter13
#print axioms Asakura.Chapter13.global_drift_primitive
