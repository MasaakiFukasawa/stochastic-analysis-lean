import Chapter2CompatibleMeasurePasting
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Topology.Order.MonotoneConvergence

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.Chapter2Complete
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

variable {S : Type*} [MeasurableSpace S]

theorem compatible_measure_paste_support (μ : ℕ → Measure S) (B : ℕ → Set S)
    (hB : ∀ n, MeasurableSet (B n)) :
    (compatibleMeasurePaste μ B).restrict (⋃ n, B n) = compatibleMeasurePaste μ B := by
  rw [compatibleMeasurePaste,Measure.restrict_sum _ (MeasurableSet.iUnion hB)]
  congr 1
  funext n
  rw [Measure.restrict_comm (MeasurableSet.iUnion hB)]
  exact Measure.restrict_restrict_of_subset ((disjointed_subset B n).trans (subset_iUnion B n))

theorem compatible_measure_paste_lintegral_limit (μ : ℕ → Measure S) (B : ℕ → Set S)
    (hB : ∀ n, MeasurableSet (B n)) (hBm : Monotone B)
    (hself : ∀ n, (μ n).restrict (B n) = μ n)
    (hcompat : ∀ j n, (μ j).restrict (B n) = (μ n).restrict (B j))
    (f : S → ℝ≥0∞) (hf : Measurable f) :
    Tendsto (fun n => ∫⁻ x, f x ∂μ n) atTop (𝓝 (∫⁻ x, f x ∂compatibleMeasurePaste μ B)) := by
  classical
  let ν := compatibleMeasurePaste μ B
  let g := fun n => (B n).indicator f
  have hg n : Measurable (g n) := hf.indicator (hB n)
  have hgm : Monotone g := by
    intro n k hnk x
    by_cases hx : x ∈ B n
    · simp [g,hx,hBm hnk hx]
    · simp only [g,indicator_of_notMem hx]; exact bot_le
  have he : (fun x => ⨆ n, g n x) = (⋃ n, B n).indicator f := by
    funext x
    by_cases hx : x ∈ ⋃ n, B n
    · rw [indicator_of_mem hx]
      apply le_antisymm
      · apply iSup_le
        intro n
        by_cases hn : x ∈ B n <;> simp [g,hn]
      · obtain ⟨n,hn⟩ := mem_iUnion.mp hx
        exact le_iSup_of_le n (by simp [g,hn])
    · rw [indicator_of_notMem hx]
      apply le_antisymm ?_ bot_le
      apply iSup_le
      intro n
      have hn : x ∉ B n := fun h => hx (mem_iUnion.mpr ⟨n,h⟩)
      simp [g,hn]
  have hle : (⨆ n, ∫⁻ x, g n x ∂ν) = ∫⁻ x, f x ∂ν := by
    rw [← lintegral_iSup hg hgm,he,lintegral_indicator (MeasurableSet.iUnion hB),
      compatible_measure_paste_support μ B hB]
  have hl := tendsto_atTop_iSup (show Monotone (fun n => ∫⁻ x, g n x ∂ν) from fun n k hnk => lintegral_mono (hgm hnk))
  rw [hle] at hl
  have hval n : (∫⁻ x, g n x ∂ν) = ∫⁻ x, f x ∂μ n := by
    change (∫⁻ x, (B n).indicator f x ∂ν) = ∫⁻ x, f x ∂μ n
    rw [lintegral_indicator (hB n),compatible_measure_paste_restrict μ B hB hself hcompat]
  simpa only [hval] using hl

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.compatible_measure_paste_lintegral_limit
