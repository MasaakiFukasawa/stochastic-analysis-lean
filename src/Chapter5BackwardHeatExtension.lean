import Chapter5SubspaceHeatEquation
import Chapter5SmoothExtension

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators
namespace Asakura.Chapter5
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- Before the final observation time, the backwards Gaussian average
has an actual global C² extension agreeing near the entire time strip.
Thus the global Ito theorem introduces no extra regularity assumption. -/
theorem backward_heat_C2_extension
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (ν : Measure E) [IsProbabilityMeasure ν] (hi : MemLp (fun z : E => z) 2 ν)
    (f : E → ℝ) (D : E → E →L[ℝ] ℝ) (DD : E → E →L[ℝ] E →L[ℝ] ℝ)
    (hd : ∀ x,HasFDerivAt f (D x) x) (hdd : ∀ x,HasFDerivAt D (DD x) x)
    (hDc : Continuous D) (hDDc : Continuous DD)
    (C K : ℝ≥0) (hD : ∀ x,‖D x‖≤C) (hDD : ∀ x,‖DD x‖≤K)
    (b S : ℝ) (hb : b<S) :
    ∃ g : E × ℝ → ℝ,ContDiff ℝ 2 g ∧
      ∀ p : E × ℝ,p.2≤b →
        g =ᶠ[𝓝 p] (fun q => ∫ z,f (q.1+Real.sqrt (S-q.2) • z) ∂ν) := by
  let U := {p : E × ℝ | p.2<S}
  let A := fun q : E × ℝ => ∫ z,f (q.1+Real.sqrt q.2 • z) ∂ν
  have hA p (hp : 0<p.2) : ContDiffAt ℝ 2 A p :=
    joint_heat_average_C2_lipschitz ν hi f D DD hd hdd hDc hDDc C K hD hDD p hp
  have hback : ContDiffOn ℝ 2 (fun q : E × ℝ => A (q.1,S-q.2)) U := by
    intro p hp
    exact ((hA (p.1,S-p.2) (sub_pos.mpr hp)).comp p
      (contDiffAt_fst.prodMk (contDiffAt_const.sub contDiffAt_snd))).contDiffWithinAt
  exact closed_set_contDiff_extension {p : E × ℝ | p.2≤b} U
    (isClosed_le continuous_snd continuous_const) (isOpen_lt continuous_snd continuous_const)
    (fun p hp => hp.trans_lt hb) _ hback

end Asakura.Chapter5
