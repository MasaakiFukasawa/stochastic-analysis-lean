import Chapter5BSDEFiniteEnergyData
import Chapter5TimeSpaceIntegrand

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

lemma BSDEFiniteEnergyData.progressiveY
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F)
    (W : ClosedTime T → Ω → ℝ) (c : ℕ → ℝ) (R : ℝ) (hR : 0≤R) (hRT : (R:EReal)<T)
    (u : BSDEFiniteEnergyData P F W c R) :
    @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) R => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) R => u.Y (realTimeClamp z.2.val) z.1) :=
  borel_diffusion_progressive P F hF u.Y u.V u.M u.decomposition R hR hRT (fun p => p.2) measurable_snd

end Asakura.Chapter5
