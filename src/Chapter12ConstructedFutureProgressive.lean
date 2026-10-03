import Chapter12FutureIntegralProgressive
import Chapter12WienerFutureProcess

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter4
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

/-- Prefixes and independent-copy future increments from actual continuous
M2 integrals give the progressive Gaussian-averaging function used in Clark's
cylinder argument. -/
theorem continuous_integral_future_average_progressive
    {Ω : Type*} [m : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (n : ℕ) (N : Fin n → HalfClosedTime → Ω → ℝ)
    (hN : ∀ i,ContinuousM2Witness P F (N i)) (T : ℝ)
    (f : (Fin n → ℝ) × (Fin n → ℝ) → ℝ) (hf : Measurable f) :
    @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) T => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) T => ∫ w,
        f ((fun i => N i (realTimeClamp z.2.val) z.1),
          (fun i => N i ⊤ w-N i (realTimeClamp z.2.val) w)) ∂P) := by
  let X := fun z : Ω × Icc (0:ℝ) T => fun i => N i (realTimeClamp z.2.val) z.1
  let Y := fun z : Icc (0:ℝ) T × Ω => fun i => N i ⊤ z.2-N i (realTimeClamp z.1.val) z.2
  have hX : @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) T => F (realTimeClamp t.val))) inferInstance X := by
    letI : MeasurableSpace (Ω × Icc (0:ℝ) T) := progressiveSpace (fun t : Icc (0:ℝ) T => F (realTimeClamp t.val))
    apply measurable_pi_iff.mpr
    intro i
    apply (measurable_progressive_iff _ _).mpr
    intro t
    letI : MeasurableSpace Ω := F (realTimeClamp t.val)
    have hc w : Continuous (fun s : Iic t => N i (realTimeClamp s.val.val) w) :=
      ((hN i).path w).comp (real_time_clamp_continuous.comp (continuous_subtype_val.comp continuous_subtype_val))
    have hm (s : Iic t) : Measurable (fun w => N i (realTimeClamp s.val.val) w) :=
      ((hN i).adapted _).mono (hF (real_time_clamp_mono s.property)) le_rfl
    exact (measurable_uncurry_of_continuous_of_measurable hc hm).comp measurable_swap
  have hY : Measurable Y := by
    apply measurable_pi_iff.mpr
    intro i
    have hc w : Continuous (fun t : Icc (0:ℝ) T => N i (realTimeClamp t.val) w) :=
      ((hN i).path w).comp (real_time_clamp_continuous.comp continuous_subtype_val)
    have hm (t : Icc (0:ℝ) T) : Measurable (fun w => N i (realTimeClamp t.val) w) :=
      ((hN i).adapted _).mono (hle _) le_rfl
    exact (((hN i).adapted ⊤).mono (hle _) le_rfl).comp measurable_snd |>.sub
      (measurable_uncurry_of_continuous_of_measurable hc hm)
  exact independent_future_integral_progressive _ P X Y hX hY f hf

end Asakura.Chapter12
#print axioms Asakura.Chapter12.continuous_integral_future_average_progressive
