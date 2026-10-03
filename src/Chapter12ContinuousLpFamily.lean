import Chapter12DominatedLpLimit

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

/-- A common Lp envelope converts pathwise continuity into continuity of
the Lp-valued family. This supplies time regularity at every finite exponent. -/
theorem continuous_Lp_family_of_dominated_paths
    {α Ω E : Type*} [TopologicalSpace α] [FirstCountableTopology α]
    [MeasurableSpace Ω] [NormedAddCommGroup E]
    (P : Measure Ω) [IsFiniteMeasure P] (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (F : α → Ω → E) (hF : ∀ t, MemLp (F t) p P)
    (hc : ∀ᵐ w ∂P, Continuous (fun t => F t w))
    (G : Ω → E) (hG : MemLp G p P)
    (hb : ∀ t, ∀ᵐ w ∂P, ‖F t w‖ ≤ ‖G w‖) :
    Continuous (fun t => (hF t).toLp (F t)) := by
  apply continuous_iff_seqContinuous.mpr
  intro u t hut
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ (fun n => hF (u n)) _ (hF t)).mpr
  apply dominated_Lp_limit P p (Fact.out : 1 ≤ p) hp (fun n => F (u n)) (F t) G hG
    (fun n => (hF (u n)).aestronglyMeasurable) (hF t) (fun n => hb (u n))
  filter_upwards [hc] with w hw
  exact (hw.tendsto t).comp hut

end Asakura.Chapter12
