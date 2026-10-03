import Chapter2L2SectionMeasurable

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {S : Type*} [MeasurableSpace S]

theorem memLp_extend_indicator (ν : Measure S) (B : Set S) (hB : MeasurableSet B)
    (f : S → ℝ) (hf : MemLp f 2 (ν.restrict B)) : MemLp (B.indicator f) 2 ν := by
  rw [memLp_iff]
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hB]
  exact hf.eLpNorm_lt_top

noncomputable def l2RestrictLift (ν : Measure S) (B : Set S) (hB : MeasurableSet B)
    (f : Lp ℝ 2 (ν.restrict B)) : Lp ℝ 2 ν :=
  (memLp_extend_indicator ν B hB f (Lp.memLp f)).toLp (B.indicator f)

theorem l2RestrictLift_isometry (ν : Measure S) (B : Set S) (hB : MeasurableSet B) :
    Isometry (l2RestrictLift ν B hB) := by
  intro f g
  unfold l2RestrictLift
  rw [Lp.edist_toLp_toLp,Lp.edist_def]
  change eLpNorm (fun r => B.indicator f r-B.indicator g r) 2 ν = _
  rw [← indicator_sub,eLpNorm_indicator_eq_eLpNorm_restrict hB]
  rfl

theorem l2RestrictLift_toLp (ν : Measure S) (B : Set S) (hB : MeasurableSet B)
    (f : S → ℝ) (hf : MemLp f 2 (ν.restrict B)) :
    l2RestrictLift ν B hB (hf.toLp f) = (memLp_extend_indicator ν B hB f hf).toLp (B.indicator f) := by
  unfold l2RestrictLift
  apply MemLp.toLp_congr
  have he := (ae_restrict_iff' hB).mp hf.coeFn_toLp
  filter_upwards [he] with r hr
  by_cases hb : r ∈ B
  · simpa only [indicator_of_mem hb] using hr hb
  · simp only [indicator_of_notMem hb]

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.l2RestrictLift_isometry
#print axioms Asakura.Chapter2Complete.l2RestrictLift_toLp
