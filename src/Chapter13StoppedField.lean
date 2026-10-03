import Chapter13ParameterStopping
import Chapter13LocalizedParameterEnergy

open MeasureTheory Set
namespace Asakura.Chapter13
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

theorem stopped_field_indicator (R:ℝ) (hR:0≤R) (τ:HalfClosedTime) (r a:ℝ) :
    (Ioc (0:ℝ) (finitePrefixTime R hR τ).val).indicator (fun _ => a) r =
      (Ioc (⊥:HalfClosedTime) (min (realTimeClamp R) τ)).indicator (fun _ => a) (realTimeClamp r) := by
  have he : r∈Ioc (0:ℝ) (finitePrefixTime R hR τ).val ↔
      realTimeClamp r ∈ Ioc (⊥:HalfClosedTime) (min (realTimeClamp R) τ) := by
    rw [←finite_prefix_time_clamp R hR (show (R:EReal)≤⊤ from le_top)]
    by_cases hr:0≤r
    · have hc:=real_time_clamp_eq (T:=(⊤:EReal)) r hr le_top
      have hq:=real_time_clamp_eq (T:=(⊤:EReal)) (finitePrefixTime R hR τ).val
        (finitePrefixTime R hR τ).property.1 le_top
      change (0<r ∧ r≤_) ↔ ((0:EReal)<(realTimeClamp r:EReal) ∧ (realTimeClamp r:EReal)≤_)
      rw [hc,hq]
      norm_cast
    · have hz:realTimeClamp (T:=(⊤:EReal)) r=⊥ := by
        apply Subtype.ext
        simp [realTimeClamp, projIcc_of_le_left _ (show (r:EReal)≤0 by exact_mod_cast le_of_not_ge hr)]
      simp [hz,show ¬0<r by linarith]
  simp only [indicator_apply]
  split_ifs with h h' h' <;> simp_all
/-- Both kinds of measurability of the stopped parameter field are derived
from stopping-time measurability and joint progressiveness. -/
theorem stopped_field_measurable {Ω E:Type*} {m:MeasurableSpace Ω} [MeasurableSpace E]
    (F:HalfClosedTime → MeasurableSpace Ω) (hF:Monotone F) (hle:∀t,F t≤m)
    (R:ℝ) (hR:0≤R) (τ:Ω → HalfClosedTime)
    (hτ:∀t,MeasurableSet[F t] {w | τ w≤t})
    (H:E × (Ω × ℝ) → ℝ) (hm:Measurable H)
    (hp:∀b,0<b → @Measurable _ _
      ((inferInstance : MeasurableSpace E).prod (progressiveSpace (fun t:Icc (0:ℝ) b => F (realTimeClamp t.val)))) inferInstance
      (fun z:E × (Ω × Icc (0:ℝ) b) => H (z.1,(z.2.1,z.2.2.val)))) :
    let K := fun z:E × (Ω × ℝ) =>
      (Ioc (0:ℝ) (finitePrefixTime R hR (τ z.2.1)).val).indicator (fun r => H (z.1,(z.2.1,r))) z.2.2
    Measurable K ∧ ∀b,0<b → @Measurable _ _
      ((inferInstance : MeasurableSpace E).prod (progressiveSpace (fun t:Icc (0:ℝ) b => F (realTimeClamp t.val)))) inferInstance
      (fun z:E × (Ω × Icc (0:ℝ) b) => K (z.1,(z.2.1,z.2.2.val))) := by
  intro K
  have htm:Measurable τ := measurable_of_Iic (fun t => hle t _ (hτ t))
  have hq:Measurable (fun w => (finitePrefixTime R hR (τ w)).val) :=
    measurable_subtype_coe.comp ((finite_prefix_time_continuous R hR).measurable.comp htm)
  constructor
  · have hs:MeasurableSet {z:E × (Ω × ℝ) | 0<z.2.2 ∧ z.2.2≤(finitePrefixTime R hR (τ z.2.1)).val} :=
      (measurableSet_lt measurable_const (measurable_snd.comp measurable_snd)).inter
        (measurableSet_le (measurable_snd.comp measurable_snd) (hq.comp (measurable_fst.comp measurable_snd)))
    convert hm.indicator hs using 1
    funext z
    simp only [K,indicator_apply,mem_Ioc,mem_setOf_eq]
  · intro b hb
    have ht:∀t,MeasurableSet[F t] {w | min (realTimeClamp R) (τ w)≤t} := by
      intro t
      by_cases h:realTimeClamp R≤t
      · simp [min_le_iff,h]
      · simpa only [min_le_iff,h,false_or] using hτ t
    have hh:=parameter_stopping_progressive F hF (fun w => min (realTimeClamp R) (τ w)) ht b H (hp b hb)
    convert hh using 1
    funext z
    exact stopped_field_indicator R hR (τ z.2.1) z.2.2.val _

end Asakura.Chapter13
#print axioms Asakura.Chapter13.stopped_field_indicator

#print axioms Asakura.Chapter13.stopped_field_measurable
