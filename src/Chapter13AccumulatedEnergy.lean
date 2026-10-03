import Chapter4FinitePathLift
import Chapter13EnergyLocalization
import Chapter5ProgressiveDriftVariation

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter13
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter5
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- Construct the accumulated stopped energy from a nonnegative progressive
driver, rather than assuming continuity and adaptedness of its primitive. -/
theorem accumulated_energy_constructed {Ω:Type*}
    (F:HalfClosedTime → MeasurableSpace Ω) (hF:Monotone F)
    (R:ℝ) (hR:0≤R) (G:Ω × ℝ → ℝ)
    (hp:@Measurable _ _ (progressiveSpace (fun t:Icc (0:ℝ) R => F (realTimeClamp t.val))) inferInstance
      (fun z:Ω × Icc (0:ℝ) R => G (z.1,z.2.val)))
    (hi:∀w,Integrable (fun r => G (w,r)) (volume.restrict (Ioc 0 R)))
    (hpos:∀w r,0≤G (w,r)) :
    ∃C:HalfClosedTime → Ω → ℝ,
      (∀t,Measurable[F t] (C t)) ∧ (∀w,Continuous (fun t => C t w)) ∧
      (∀w,C ⊥ w=0) ∧ (∀t w,C t w≤∫r in 0..R,G (w,r)) ∧
      ∀t w,C t w=∫r in 0..(finitePrefixTime R hR t).val,G (w,r) := by
  obtain ⟨C,hCv,hCc,he⟩:=progressive_integrable_drift_variation (by simp : (0:EReal)<⊤) F hF R hR le_top G hp hi
  have htop:∀w,C ⊤ w=C (realTimeClamp R) w := by
    intro w
    rw [he,he]
    rw [finite_prefix_time_of_real R R hR ⟨hR,le_rfl⟩ le_top]
    simp [finitePrefixTime]
  refine ⟨C,?_,hCc,?_,?_,he⟩
  · intro t
    by_cases ht:t<⊤
    · exact hCv.adapted t ht
    · have heq:t=⊤ := eq_top_iff.mpr (le_of_not_gt ht)
      subst t
      have hh:C ⊤=C (realTimeClamp R) := funext htop
      rw [hh]
      exact (hCv.adapted _ (Asakura.Chapter4.real_time_below R hR (EReal.coe_lt_top R))).mono (hF le_top) le_rfl
  · intro w
    rw [he]
    have hz:(finitePrefixTime (T:=(⊤:EReal)) R hR ⊥).val=0 := by simp [finitePrefixTime,min_eq_left (show (0:EReal)≤R from by exact_mod_cast hR)]
    rw [hz,intervalIntegral.integral_same]
  · intro t w
    rw [he,intervalIntegral.integral_of_le (finitePrefixTime R hR t).property.1,
      intervalIntegral.integral_of_le hR]
    exact setIntegral_mono_set (hi w) (ae_of_all _ (hpos w))
      (ae_of_all _ fun r hr => ⟨hr.1,hr.2.trans (finitePrefixTime R hR t).property.2⟩)
end Asakura.Chapter13
#print axioms Asakura.Chapter13.accumulated_energy_constructed
