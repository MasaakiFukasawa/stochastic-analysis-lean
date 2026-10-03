import Chapter11ReplicationRepresentation
import Chapter2CommonTimeEquality

open MeasureTheory Set Filter TopologicalSpace
open scoped Topology
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter5
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- Nonnegative conditional prices are nonnegative simultaneously at all
times, as needed by admissibility, using path continuity and a dense set. -/
theorem nonnegative_conditional_price_common {Ω D : Type*} [m : MeasurableSpace Ω]
    [TopologicalSpace D] [SeparableSpace D] [Nonempty D]
    (P : Measure Ω) (F : D → MeasurableSpace Ω) (U : Ω → ℝ)
    (V : D → Ω → ℝ) (hV : ∀ w,Continuous (fun t => V t w))
    (hU : 0≤ᵐ[P] U) (he : ∀ t,V t=ᵐ[P] P[U|F t]) :
    ∀ᵐ w ∂P,∀ t,0≤V t w := by
  have hn t : ∀ᵐ w ∂P,0≤V t w := by
    filter_upwards [he t,condExp_nonneg (m:=F t) hU] with w hw hn
    rw [hw]
    exact hn
  have hq := ae_all_iff.mpr (fun n => hn (denseSeq D n))
  filter_upwards [hq] with w hw
  intro t
  exact (denseRange_denseSeq D).induction_on t (isClosed_le continuous_const (hV w)) hw

end Asakura.Chapter11
