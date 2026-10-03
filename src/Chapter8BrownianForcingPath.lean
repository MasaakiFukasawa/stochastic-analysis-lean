import Chapter8SDEAdditiveEquation
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap

open MeasureTheory Set
open scoped BigOperators
namespace Asakura.Chapter8
open Asakura.Chapter4 Asakura.Chapter3Complete Asakura.FullAudit
open Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1600000

theorem half_real_time_finite (r : ℝ) : realTimeClamp (T:=⊤) r<⊤ := by
  apply (real_time_clamp_mono (le_max_left r 0)).trans_lt
  exact real_time_below (max r 0) (le_max_right r 0) (EReal.coe_lt_top _)

/-- The Brownian forcing, as a measurable random element of the continuous
path space used to construct the differentiable additive solution map. -/
theorem brownian_forcing_path {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ}
    (B : BrownianSystem P n) (σ : Fin d → Fin n → ℝ)
    (T : ℝ) :
    ∃ V : Ω → C(Icc (0:ℝ) T,Fin d → ℝ), Measurable V ∧
      ∀ w t i,V w t i=∑ j,σ i j*B.W j (realTimeClamp t.val) w := by
  have hc w : Continuous (fun r : ℝ => fun i => ∑ j,σ i j*B.W j (realTimeClamp r) w) := by
    apply continuous_pi
    intro i
    apply continuous_finset_sum
    intro j _
    apply Continuous.const_mul
    apply continuous_iff_continuousAt.mpr
    intro r
    exact ((B.martingale j).path P B.F w _ (half_real_time_finite r)).comp
      real_time_clamp_continuous.continuousAt
  let V : Ω → C(Icc (0:ℝ) T,Fin d → ℝ) := fun w =>
    ⟨fun t i => ∑ j,σ i j*B.W j (realTimeClamp t.val) w,(hc w).comp continuous_subtype_val⟩
  refine ⟨V,?_,fun _ _ _ => rfl⟩
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  apply measurable_pi_lambda
  intro i
  change Measurable (fun w => ∑ j,σ i j*B.W j (realTimeClamp t.val) w)
  apply Finset.measurable_sum
  intro j _
  exact (((B.martingale j).adapted P B.F _ (half_real_time_finite t.val)).mono (B.le _) le_rfl).const_mul _

end Asakura.Chapter8
