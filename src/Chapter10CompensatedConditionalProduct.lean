import Chapter10ConditionalProductAssembly

open MeasureTheory
namespace Asakura.Chapter10
set_option backward.isDefEq.respectTransparency false

lemma compensated_conditional_product {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (H : MeasurableSpace Ω) (hH : H≤m)
    (U V : Ω → ℝ) (hU : Integrable U P) (hV : Integrable V P) (hm : Measurable[H] V)
    (s t : ℝ) (he : P[(fun w => U w-V w)|H]=ᵐ[P] (fun _ => t-s)) :
    P[(fun w => U w-t)|H]=ᵐ[P] (fun w => V w-s) := by
  have hcV := condExp_of_stronglyMeasurable hH hm.stronglyMeasurable hV
  have hct := condExp_const (μ := P) hH t
  filter_upwards [condExp_sub hU hV H,condExp_sub hU (integrable_const t) H,he] with w h1 h2 he
  change P[(fun w => U w-V w)|H] w=P[U|H] w-P[V|H] w at h1
  change P[(fun w => U w-t)|H] w=P[U|H] w-P[(fun _ => t)|H] w at h2
  rw [hcV] at h1
  rw [hct] at h2
  change P[(fun w => U w-t)|H] w=V w-s
  linarith

end Asakura.Chapter10
