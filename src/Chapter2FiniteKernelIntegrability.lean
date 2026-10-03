import Chapter2FiniteKernelIntegral
import Chapter2GlobalEnergyIdentity

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal Classical
namespace Asakura.Chapter2Complete
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

theorem finite_kernel_integrable_set_measurable
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (κ : Kernel Ω S) (hκ : ∀ ω, IsFiniteMeasure (κ ω))
    (f : Ω × S → ℝ) (hf : Measurable f) :
    MeasurableSet {ω | Integrable (fun r => f (ω,r)) (κ ω)} := by
  have hm ω : AEStronglyMeasurable (fun r => f (ω,r)) (κ ω) :=
    (hf.comp measurable_prodMk_left).aestronglyMeasurable
  simp only [Integrable,hm,true_and,HasFiniteIntegral]
  exact measurableSet_lt (finite_kernel_lintegral_measurable κ hκ _ hf.enorm) measurable_const

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.finite_kernel_integrable_set_measurable
