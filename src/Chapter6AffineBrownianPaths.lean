import Chapter6BorelProgressive
import Chapter4BrownianSystem
import Chapter7ClockHalfTime

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter7
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

lemma affine_brownian_regular
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {dim : ℕ} (B : BrownianSystem P dim) (S : Fin dim → Fin dim → ℝ)
    (ξ : Ω → Fin dim → ℝ) (hξ : Measurable[B.F ⊥] ξ) :
    let X := fun r w i => ξ w i+∑ j,S i j*B.W j (realTimeClamp (max 0 r)) w
    (∀ r,Measurable[m] (X r)) ∧
    (∀ w,Continuous (fun r => X r w)) ∧
    (∀ r,0 ≤ r → Measurable[B.F (realTimeClamp r)] (X r)) := by
  dsimp only
  have ha r : Measurable[B.F (realTimeClamp (max 0 r))]
      (fun w i => ξ w i+∑ j,S i j*B.W j (realTimeClamp (max 0 r)) w) := by
    letI : MeasurableSpace Ω := B.F (realTimeClamp (max 0 r))
    apply measurable_pi_iff.mpr
    intro i
    exact ((measurable_pi_apply i).comp (hξ.mono (B.mono bot_le) le_rfl)).add
      (Finset.measurable_sum _ fun j _ => measurable_const.mul ((B.martingale j).adapted P B.F _ (changed_time_finite _ (le_max_left _ _))))
  refine ⟨fun r => (ha r).mono (B.le _) le_rfl,?_,?_⟩
  · intro w
    apply continuous_pi
    intro i
    apply continuous_const.add
    apply continuous_finset_sum
    intro j _
    apply continuous_const.mul
    apply continuous_iff_continuousAt.mpr
    intro r
    exact (((B.martingale j).path P B.F w _ (changed_time_finite _ (le_max_left _ _))).comp
      real_time_clamp_continuous.continuousAt).comp (continuous_const.max continuous_id).continuousAt
  · intro r hr
    convert ha r using 1 <;> simp only [max_eq_right hr]

end Asakura.Chapter6
