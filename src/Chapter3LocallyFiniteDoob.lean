import Chapter3OrthogonalSum
import FullAuditLpComplete

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/-- The Fatou--Doob step of prop:qcv for a locally finite series of M2
processes. Continuity and measurable path norms of the sum are constructed
from stabilization; no measurable-supremum hypothesis is left implicit.
The finite terminal bound remains an explicit input. -/
theorem locally_finite_m2_sum_maximal_bound
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (Z : ℕ → ClosedTime T → Ω → ℝ) (hZ : ∀ n, ContinuousM2Witness P F (Z n))
    (Y : ClosedTime T → Ω → ℝ)
    (hstab : ∀ ω, ∃ N, ∀ n, N ≤ n → ∀ t, Z n t ω = Y t ω)
    (C : ℝ≥0∞) (hC : ∀ n, eLpNorm (Z n ⊤) 2 P ≤ C) :
    ∃ hc : ∀ ω, Continuous (fun t => Y t ω),
      AEStronglyMeasurable (continuousPath Y hc) P ∧
      eLpNorm (continuousPath Y hc) 2 P ≤ 2*C := by
  have hc (ω) : Continuous (fun t => Y t ω) := by
    obtain ⟨N,hN⟩ := hstab ω
    have he : (fun t => Y t ω) = (fun t => Z N t ω) := funext fun t => (hN N le_rfl t).symm
    rw [he]
    exact (hZ N).path ω
  have hm (n) := continuous_path_measurable (Z n) (hZ n).path
    (fun t => ((hZ n).adapted t).mono (hle t) le_rfl)
  have ht : ∀ᵐ ω ∂P, Tendsto (fun n => continuousPath (Z n) (hZ n).path ω)
      atTop (𝓝 (continuousPath Y hc ω)) := by
    apply Filter.Eventually.of_forall
    intro ω
    obtain ⟨N,hN⟩ := hstab ω
    apply tendsto_const_nhds.congr'
    refine eventually_atTop.mpr ⟨N,?_⟩
    intro n hn
    apply ContinuousMap.ext
    intro t
    exact (hN n hn t).symm
  have hYm := aestronglyMeasurable_of_tendsto_ae _ (fun n => (hm n).aestronglyMeasurable) ht
  refine ⟨hc,hYm,?_⟩
  apply current_lp_eLpNorm_le_of_ae_tendsto _ (fun n => (hm n).aestronglyMeasurable) hYm ht
  exact .of_forall fun n => (continuous_martingale_path_norm P F hF hle (Z n)
    (hZ n).adapted (hZ n).moment (hZ n).path (hZ n).martingale).trans
      (mul_le_mul' le_rfl (hC n))

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.locally_finite_m2_sum_maximal_bound
