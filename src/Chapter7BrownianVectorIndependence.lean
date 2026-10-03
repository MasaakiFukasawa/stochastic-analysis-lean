import Chapter7BrownianProjectionLaw
import Chapter4ConditionalCharacteristicLaw

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter3Complete
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

lemma brownian_vector_increment_independent {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
    Indep (MeasurableSpace.comap (fun w i => B.W i (realTimeClamp t) w-B.W i (realTimeClamp s) w) inferInstance)
      (B.F (realTimeClamp s)) P := by
  let Z := fun w i => B.W i (realTimeClamp t) w-B.W i (realTimeClamp s) w
  have hm : Measurable Z := by
    apply measurable_pi_iff.mpr
    intro i
    exact (((B.martingale i).adapted P B.F _ (real_time_below t (hs.trans hst) (EReal.coe_lt_top _))).mono (B.le _) le_rfl).sub
      (((B.martingale i).adapted P B.F _ (real_time_below s hs (EReal.coe_lt_top _))).mono (B.le _) le_rfl)
  apply (independence_of_constant_conditional_characteristic P _ (B.le _) Z hm
    (fun L => Complex.exp (-((t-s:ℝ):ℂ)*((∑ i,(L (Pi.single i 1))^2:ℝ):ℂ)/2)) ?_).2
  intro L
  have he (w : Ω) : L (Z w)=∑ i,L (Pi.single i 1)*Z w i := dual_coordinate_expansion L (Z w)
  simp only [he,Z]
  exact vector_levy_conditional_characteristic P (show (0:EReal)<⊤ by simp)
    B.F B.mono B.le B.null B.W B.C B.martingale B.cov
    (fun i j w r hr _ => B.clock i j w r hr) t (hs.trans hst) (EReal.coe_lt_top _)
    s ⟨hs,hst⟩ (fun i => L (Pi.single i 1))

lemma independent_measurable_transform {Ω E V : Type*} [m : MeasurableSpace Ω]
    [MeasurableSpace E] [MeasurableSpace V] (P : Measure Ω)
    (F : MeasurableSpace Ω) (Z : Ω → E) (f : E → V)
    (hi : Indep (MeasurableSpace.comap Z inferInstance) F P) (hf : Measurable f) :
    Indep (MeasurableSpace.comap (f ∘ Z) inferInstance) F P := by
  apply indep_of_indep_of_le_left hi
  letI : MeasurableSpace Ω := MeasurableSpace.comap Z inferInstance
  exact (hf.comp (Measurable.of_comap_le le_rfl)).comap_le

end Asakura.Chapter7
