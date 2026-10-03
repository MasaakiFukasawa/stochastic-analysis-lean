import FullAuditMartingalePathNorm

open MeasureTheory Set Filter
open scoped Topology NNReal
namespace Asakura.Chapter7
open Asakura.FullAudit
set_option maxHeartbeats 1600000

/-- The event that a continuous path remains in [-1,1] over a compact
interval is measurable as soon as all its coordinates are measurable. -/
theorem interval_stay_measurable
    {Ω : Type*} (G : MeasurableSpace Ω) (X : ℝ≥0 → Ω → ℝ)
    (hc : ∀ w,Continuous (fun t => X t w)) (δ : ℝ≥0)
    (hm : ∀ t,t ≤ δ → Measurable[G] (X t)) :
    MeasurableSet[G] {w | ∀ t : ℝ≥0,t ≤ δ → |X t w| ≤ 1} := by
  letI : MeasurableSpace Ω := G
  let path : Ω → C(Icc (0:ℝ≥0) δ,ℝ) := fun w =>
    ⟨fun t => X t.val w,(hc w).comp continuous_subtype_val⟩
  have hp : Measurable path := ContinuousMap.measurable_iff_eval.mpr (fun t => hm t.val t.property.2)
  have he : {w | ∀ t : ℝ≥0,t ≤ δ → |X t w| ≤ 1} = {w | ‖path w‖ ≤ 1} := by
    ext w
    rw [mem_setOf_eq,mem_setOf_eq,ContinuousMap.norm_le (path w) (by norm_num : (0:ℝ) ≤ 1)]
    constructor
    · intro h t
      exact h t.val t.property.2
    · intro h t ht
      exact h ⟨t,t.property,ht⟩
  rw [he]
  exact measurableSet_le hp.norm measurable_const

end Asakura.Chapter7
