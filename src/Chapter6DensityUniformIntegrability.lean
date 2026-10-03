import Chapter6EntropyTail
import Mathlib.MeasureTheory.Function.UniformIntegrable

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal
namespace Asakura.Chapter6
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

lemma uniform_integrable_of_nonnegative_tails
    {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : ι → Ω → ℝ) (hm : ∀ i,Measurable (D i)) (hi : ∀ i,Integrable (D i) P)
    (hp : ∀ i,∀ᵐ w ∂P,0 ≤ D i w)
    (ht : ∀ ε : ℝ,0 < ε → ∃ R : ℝ,0 < R ∧ ∀ i,(∫ w in {w | R < D i w},D i w ∂P) ≤ ε) :
    UniformIntegrable D 1 P := by
  apply uniformIntegrable_of (by norm_num) (by norm_num) (fun i => (hm i).aestronglyMeasurable)
  intro ε hε
  by_cases he : ε = ∞
  · exact ⟨0,fun _ => by simp [he]⟩
  have hep : 0 < ε.toReal := ENNReal.toReal_pos (ne_of_gt hε) he
  obtain ⟨R,hR,hb⟩ := ht ε.toReal hep
  refine ⟨⟨R+1,by positivity⟩,?_⟩
  intro i
  let A := {w | (⟨R+1,by positivity⟩ : ℝ≥0) ≤ ‖D i w‖₊}
  let S := {w | R < D i w}
  have hA : MeasurableSet A := measurableSet_le measurable_const (hm i).nnnorm
  have hS : MeasurableSet S := measurableSet_lt measurable_const (hm i)
  have hSi : Integrable (S.indicator (D i)) P := (hi i).indicator hS
  have hmono : eLpNorm (A.indicator (D i)) 1 P ≤ eLpNorm (S.indicator (D i)) 1 P := by
    apply eLpNorm_mono_ae ((hm i).indicator hA).aestronglyMeasurable
    filter_upwards [hp i] with w hw
    by_cases hwA : w ∈ A
    · have hDw : R+1 ≤ D i w := by
        have hh : R+1 ≤ ‖D i w‖ := hwA
        simpa only [Real.norm_eq_abs,abs_of_nonneg hw] using hh
      have hwS : w ∈ S := by dsimp [S]; linarith
      rw [Set.indicator_of_mem hwA,Set.indicator_of_mem hwS]
    · rw [Set.indicator_of_notMem hwA,norm_zero]
      exact norm_nonneg _
  have heq : eLpNorm (S.indicator (D i)) 1 P = ENNReal.ofReal (∫ w in S,D i w ∂P) := by
    rw [eLpNorm_one_eq_lintegral_enorm hSi.aestronglyMeasurable,← ofReal_integral_norm_eq_lintegral_enorm hSi]
    congr 1
    rw [← integral_indicator hS]
    apply integral_congr_ae
    filter_upwards [hp i] with w hw
    by_cases hs : w ∈ S
    · rw [Set.indicator_of_mem hs]
      exact Real.norm_of_nonneg hw
    · simp only [Set.indicator_of_notMem hs,norm_zero]
  exact hmono.trans (heq.le.trans ((ENNReal.ofReal_le_ofReal (hb i)).trans (by simp [ENNReal.ofReal_toReal he])))

end Asakura.Chapter6
