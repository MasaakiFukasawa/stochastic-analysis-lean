import Chapter2L2SectionIndicator
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
variable {E S : Type*} [MeasurableSpace E] [MeasurableSpace S]

theorem simple_section_memLp (ν : Measure S) [IsFiniteMeasure ν]
    (f : SimpleFunc (E × S) ℝ) (x : E) : MemLp (fun r => f (x,r)) 2 ν := by
  exact SimpleFunc.memLp_of_finite_measure_preimage 2 (f := f.comp (Prod.mk x) measurable_prodMk_left)
    (fun _ _ => measure_lt_top ν _)

theorem stronglyMeasurable_simple_L2_sections
    (ν : Measure S) [IsFiniteMeasure ν] (f : SimpleFunc (E × S) ℝ) :
    StronglyMeasurable (fun x => (simple_section_memLp ν f x).toLp (fun r => f (x,r))) := by
  classical
  induction f using SimpleFunc.induction with
  | @const c s hs =>
    have he : (fun x => (simple_section_memLp ν (SimpleFunc.piecewise _ hs (SimpleFunc.const _ c) (SimpleFunc.const _ 0)) x).toLp _) =
        fun x => c • setL2 ν (Prod.mk x ⁻¹' _) (measurable_prodMk_left hs) := by
      funext x
      unfold setL2
      rw [← MemLp.toLp_const_smul]
      apply MemLp.toLp_congr
      exact ae_of_all _ (fun r => by
        by_cases h : (x,r) ∈ s <;> simp [SimpleFunc.coe_piecewise,h])
    rw [he]
    exact (stronglyMeasurable_setL2_sections ν _ hs).const_smul c
  | @add f g hd hf hg =>
    have he : (fun x => (simple_section_memLp ν (f+g) x).toLp _) =
        fun x => (simple_section_memLp ν f x).toLp _ + (simple_section_memLp ν g x).toLp _ := by
      funext x
      rw [← MemLp.toLp_add]
      rfl
    rw [he]
    exact hf.add hg

/-- Actual L2-valued strong measurability of jointly measurable functions on a
finite measure space, with no countability assumption on either sigma algebra. -/
theorem stronglyMeasurable_L2_sections_finite
    (ν : Measure S) [IsFiniteMeasure ν] (H : E × S → ℝ) (hH : Measurable H)
    (hLp : ∀ x, MemLp (fun r => H (x,r)) 2 ν) :
    StronglyMeasurable (fun x => (hLp x).toLp (fun r => H (x,r))) := by
  classical
  let fs (n : ℕ) := SimpleFunc.approxOn H hH univ 0 (mem_univ _) n
  apply stronglyMeasurable_of_tendsto atTop (fun n => stronglyMeasurable_simple_L2_sections ν (fs n))
  apply tendsto_pi_nhds.mpr
  intro x
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ _ _ _).mpr
  have hmeas : Measurable (fun r => H (x,r)) := hH.comp measurable_prodMk_left
  have hl := SimpleFunc.tendsto_approxOn_Lp_eLpNorm hmeas (s := univ) (mem_univ (0:ℝ))
    (p := (2:ℝ≥0∞)) (by norm_num) (μ := ν)
    (ae_of_all _ (fun r => by simp)) (by simpa using (hLp x).eLpNorm_lt_top)
  exact hl

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.stronglyMeasurable_L2_sections_finite
