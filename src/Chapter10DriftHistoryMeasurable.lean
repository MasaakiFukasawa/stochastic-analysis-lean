import Chapter10LinearReconstructionMeasurable
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory Set
namespace Asakura.Chapter10
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- Integrating a continuous path against a deterministic continuous matrix
does not enlarge the information carried by that path. -/
theorem drift_history_measurable {Ω : Type*} [MeasurableSpace Ω]
    {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    (G : MeasurableSpace Ω) (T : ℝ) (hT : 0≤T)
    (A : ℝ → E →L[ℝ] V) (hA : Continuous A)
    (X : Ω → C(Icc (0:ℝ) T,E)) (hX : Measurable[G] X) (t : Icc (0:ℝ) T) :
    Measurable[G] (fun w => ∫ s in 0..t.val,A s (X w (projIcc 0 T hT s))) := by
  letI : MeasurableSpace Ω := G
  have hc : Continuous (fun z : C(Icc (0:ℝ) T,E) × ℝ =>
      A z.2 (z.1 (projIcc 0 T hT z.2))) := by
    exact (hA.comp continuous_snd).clm_apply
      (continuous_eval.comp (continuous_fst.prodMk ((show Continuous (projIcc 0 T hT) from continuous_projIcc).comp continuous_snd)))
  have hm : Measurable (fun z : Ω × ℝ => A z.2 (X z.1 (projIcc 0 T hT z.2))) :=
    hc.measurable.comp ((hX.comp measurable_fst).prodMk measurable_snd)
  simp_rw [intervalIntegral.integral_of_le t.property.1]
  exact hm.stronglyMeasurable.integral_prod_right.measurable

end Asakura.Chapter10
