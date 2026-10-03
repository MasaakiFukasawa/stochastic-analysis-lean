import Chapter8AugmentedDerivative

open MeasureTheory
namespace Asakura.Chapter8
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false

 theorem interval_integral_pair {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (f : ℝ → E) (g : ℝ → F) (a b : ℝ)
    (hf : Continuous f) (hg : Continuous g) :
    (∫ s in a..b,(f s,g s))=(∫ s in a..b,f s,∫ s in a..b,g s) := by
  apply Prod.ext
  · exact ((ContinuousLinearMap.fst ℝ E F).intervalIntegral_comp_comm
      ((hf.prodMk hg).intervalIntegrable (μ := volume) a b)).symm
  · exact ((ContinuousLinearMap.snd ℝ E F).intervalIntegral_comp_comm
      ((hf.prodMk hg).intervalIntegrable (μ := volume) a b)).symm

end Asakura.Chapter8
