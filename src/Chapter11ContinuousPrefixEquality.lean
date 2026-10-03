import Chapter11CommonIntegralLimit
import Chapter4FinitePathLift

open MeasureTheory Set Filter TopologicalSpace
open scoped Topology
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter4

/-- The single null set follows from continuity, without an almost-sure
 subsequence argument. -/
theorem continuous_prefix_equality {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (R : ℝ) (hR : 0≤R) (X Y : ℝ → Ω → ℝ)
    (hX : ∀ w,ContinuousOn (fun t => X t w) (Icc 0 R))
    (hY : ∀ w,ContinuousOn (fun t => Y t w) (Icc 0 R))
    (he : ∀ t,t∈Icc 0 R → X t=ᵐ[P] Y t) :
    ∀ᵐ w ∂P,∀ t,t∈Icc 0 R → X t w=Y t w := by
  letI : Nonempty (Icc (0:ℝ) R) := ⟨⟨0,by exact ⟨le_rfl,hR⟩⟩⟩
  let q := denseSeq (Icc (0:ℝ) R)
  filter_upwards [ae_all_iff.mpr (fun n => he (q n).val (q n).property)] with w hw
  have hh : ∀ t : Icc (0:ℝ) R,X t.val w=Y t.val w :=
    fun t => (denseRange_denseSeq (Icc (0:ℝ) R)).induction_on t
      (isClosed_eq (continuousOn_iff_continuous_restrict.mp (hX w)) (continuousOn_iff_continuous_restrict.mp (hY w))) hw
  intro t ht
  exact hh ⟨t,ht⟩

end Asakura.Chapter11
