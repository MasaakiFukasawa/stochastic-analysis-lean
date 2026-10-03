import Chapter12FiniteConditionalRepresentation

open MeasureTheory Set
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

/-- A finite-maturity Ito representation already identifies the price at
every earlier time, by the martingale property and conditional expectation. -/
theorem finite_represented_conditional_price {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : HalfClosedTime → MeasurableSpace Ω) (hle : ∀ t,F t≤m)
    (N : HalfClosedTime → Ω → ℝ) (hN : ContinuousM2Witness P F N)
    (Y : Ω → ℝ) (c : ℝ) (T : HalfClosedTime)
    (hY : Y =ᵐ[P] (fun w => c+N T w)) :
    Integrable Y P ∧ ∀ t,t≤T → P[Y|F t] =ᵐ[P] (fun w => c+N t w) := by
  have hi := (hN.moment T).integrable (by norm_num : (1:ENNReal)≤2)
  refine ⟨((integrable_const c).add hi).congr hY.symm,?_⟩
  intro t ht
  have he := condExp_congr_ae (m := F t) hY
  have hs := condExp_add (integrable_const c) hi (F t)
  have hm := hN.martingale t T ht
  rw [condExp_of_stronglyMeasurable (hle t) stronglyMeasurable_const (integrable_const c)] at hs
  change P[(fun w => c+N T w)|F t] =ᵐ[P] (fun w => c+P[N T|F t] w) at hs
  filter_upwards [he,hs,hm] with w hw hs hm
  rw [hw,hs]
  exact congrArg (fun z => c+z) hm

end Asakura.Chapter12
