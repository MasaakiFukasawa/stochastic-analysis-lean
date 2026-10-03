import FullAuditTransportFlow
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

open MeasureTheory Set
namespace Asakura.Chapter8
open Asakura.FullAudit
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- Integrate the actual propagated law using its jointly measurable flow. -/
theorem integral_flow_law {E Ω : Type*} [MeasurableSpace E] [MeasurableSpace Ω]
    (μ : Measure E) (P : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    (F : E → Ω → E) (hF : Measurable (Function.uncurry F))
    (f : E → ℝ) (hf : Measurable f) (K : ℝ) (hK : ∀ x,‖f x‖≤K) :
    (∫ x,f x ∂flowLaw μ P F)=∫ x,(∫ w,f (F x w) ∂P) ∂μ := by
  have hi : Integrable (fun z : E × Ω => f (F z.1 z.2)) (μ.prod P) :=
    Integrable.of_bound (hf.comp hF).aestronglyMeasurable K (ae_of_all _ fun z => hK _)
  rw [flowLaw,integral_map hF.aemeasurable hf.aestronglyMeasurable]
  exact integral_prod _ hi

/-- A pointwise commuting transition identity gives the required equality
of propagated probability measures, by Fubini and smooth measure tests. -/
theorem flow_law_commutes {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) (P : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    (F G : E → Ω → E)
    (hF : Measurable (Function.uncurry F)) (hG : Measurable (Function.uncurry G))
    (hcomm : ∀ f : E → ℝ,Measurable f → ∀ K : ℝ,(∀ x,‖f x‖≤K) →
      ∀ x,(∫ w,(∫ z,f (F (G x w) z) ∂P) ∂P)=
        ∫ w,(∫ z,f (G (F x w) z) ∂P) ∂P) :
    flowLaw (flowLaw μ P G) P F=flowLaw (flowLaw μ P F) P G := by
  have hprob (H : E → Ω → E)
      (hH : Measurable (Function.uncurry H)) (ν : Measure E) [IsProbabilityMeasure ν] :
      IsProbabilityMeasure (flowLaw ν P H) :=
    (Measure.isProbabilityMeasure_map_iff hH.aemeasurable).mpr inferInstance
  haveI := hprob F hF μ
  haveI := hprob G hG μ
  haveI := hprob F hF (flowLaw μ P G)
  haveI := hprob G hG (flowLaw μ P F)
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  let K := ‖f‖
  have hK x : ‖f x‖≤K := f.norm_coe_le_norm x
  have hm (H : E → Ω → E)
      (hH : Measurable (Function.uncurry H)) : Measurable (fun x => ∫ w,f (H x w) ∂P) := by
    have hh : StronglyMeasurable (Function.uncurry (fun x w => f (H x w))) :=
      (f.continuous.measurable.comp hH).stronglyMeasurable
    exact hh.integral_prod_right.measurable
  have hb (H : E → Ω → E) x : ‖∫ w,f (H x w) ∂P‖≤K := by
    simpa only [probReal_univ,mul_one] using
      norm_integral_le_of_norm_le_const (μ := P) (ae_of_all _ fun w => hK (H x w))
  rw [integral_flow_law _ P F hF f f.continuous.measurable K hK,
    integral_flow_law _ P G hG f f.continuous.measurable K hK,
    integral_flow_law μ P G hG _ (hm F hF) K (hb F),
    integral_flow_law μ P F hF _ (hm G hG) K (hb G)]
  exact integral_congr_ae (ae_of_all _ fun x => hcomm f f.continuous.measurable K hK x)

end Asakura.Chapter8
