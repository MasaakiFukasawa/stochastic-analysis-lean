import Chapter2ProbabilityErrorSum
import Chapter7ProbabilityProduct

open MeasureTheory Filter
open scoped Topology
namespace Asakura.Chapter7
open Asakura.Chapter2Complete

lemma probability_add_zero {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X Y : ℕ → Ω → ℝ)
    (hX : TendstoInMeasure P X atTop (fun _ => 0))
    (hY : TendstoInMeasure P Y atTop (fun _ => 0)) :
    TendstoInMeasure P (fun n w => X n w+Y n w) atTop (fun _ => 0) := by
  apply tendstoInMeasure_iff_dist.mpr
  intro ε hε
  simp only [Real.dist_eq,sub_zero]
  apply probability_error_sum_limit P (fun n w => |X n w+Y n w|)
    (fun n w => |X n w|) (fun n w => |Y n w|) 1 (by norm_num)
    (fun n => ae_of_all P (fun w => by simpa only [one_mul] using abs_add_le (X n w) (Y n w)))
  · intro δ hδ
    simpa only [Real.dist_eq,sub_zero] using tendstoInMeasure_iff_dist.mp hX δ hδ
  · intro δ hδ
    simpa only [Real.dist_eq,sub_zero] using tendstoInMeasure_iff_dist.mp hY δ hδ
  · exact hε

lemma probability_of_abs_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X Y : ℕ → Ω → ℝ)
    (hY : TendstoInMeasure P Y atTop (fun _ => 0))
    (hb : ∀ n,∀ᵐ w ∂P,|X n w|≤|Y n w|) :
    TendstoInMeasure P X atTop (fun _ => 0) := by
  apply tendstoInMeasure_iff_dist.mpr
  intro ε hε
  have hh := tendstoInMeasure_iff_dist.mp hY ε hε
  simp only [Real.dist_eq,sub_zero] at hh ⊢
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hh (fun _ => bot_le)
  intro n
  exact measure_mono_ae ((hb n).mono (fun w hw hx => hx.trans hw))

end Asakura.Chapter7
