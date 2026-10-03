import Chapter5ConditionalProcessConstructed
import Chapter2ProgressiveSpace
import Chapter2HalfLineLocalization

open MeasureTheory Set
open scoped ENNReal Topology
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter5
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-- The continuous conditional-expectation process supplied by the actual
martingale representation is progressive on each finite time interval. -/
theorem represented_conditional_progressive {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t ≤ m)
    (U : Ω → ℝ) (hU : MemLp U 2 P) (M : HalfClosedTime → Ω → ℝ)
    (hM : ContinuousM2Witness P F M) (c : ℝ)
    (hrep : U =ᵐ[P] fun w => c+M ⊤ w) (T : ℝ) :
    @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) T => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) T => c+M (realTimeClamp z.2.val) z.1) ∧
    (∀ t : Icc (0:ℝ) T,(fun w => c+M (realTimeClamp t.val) w) =ᵐ[P]
      P[U|F (realTimeClamp t.val)]) := by
  have hc := conditional_process_from_represented_terminal P F hle U hU M hM c hrep
  refine ⟨?_,fun t => hc.2.2.2 _⟩
  apply (measurable_progressive_iff _ _).mpr
  intro t
  letI : MeasurableSpace Ω := F (realTimeClamp t.val)
  have hcont (w : Ω) : Continuous (fun s : Iic t => c+M (realTimeClamp s.val.val) w) :=
    (hc.2.1 w).comp (continuous_subtype_val.comp continuous_subtype_val)
  have hm (s : Iic t) : Measurable (fun w => c+M (realTimeClamp s.val.val) w) :=
    (hc.2.2.1 _).mono (hF (real_time_clamp_mono s.property)) le_rfl
  exact (measurable_uncurry_of_continuous_of_measurable hcont hm).comp measurable_swap

end Asakura.Chapter12
