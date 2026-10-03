import Chapter10RandomIntegrandMartingale

open MeasureTheory Set Filter
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4
set_option backward.isDefEq.respectTransparency false

theorem stopped_martingale_initial_conditional_zero {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : HalfClosedTime → MeasurableSpace Ω) (hle : ∀ t,F t≤m)
    (Z : HalfClosedTime → Ω → ℝ) (T : ℝ)
    (hM : ContinuousMpWitness P F 2 (fun t w => Z (min (realTimeClamp T) t) w))
    (G : MeasurableSpace Ω) (hG : G≤F ⊥) :
    Integrable (Z (realTimeClamp T)) P ∧ P[Z (realTimeClamp T)|G]=ᵐ[P] 0 := by
  letI : MeasurableSpace Ω := m
  have hi : Integrable (Z (realTimeClamp T)) P := by
    simpa only [min_self] using (hM.moment (realTimeClamp T)).integrable (by norm_num)
  have hc : P[Z (realTimeClamp T)|F ⊥]=ᵐ[P] 0 := by
    have hh := (hM.martingale ⊥ (realTimeClamp T) bot_le).trans hM.initial
    simpa only [min_self] using hh
  refine ⟨hi,?_⟩
  exact (condExp_condExp_of_le hG (hle ⊥)).symm.trans
    ((condExp_congr_ae (m := G) hc).trans (by simp))

end Asakura.Chapter10
