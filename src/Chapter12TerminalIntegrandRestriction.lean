import Chapter12CompactIntegrandRestriction
import Chapter12ProductTrim

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter2Written Asakura.Chapter2Complete
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

/-- Restricting an actual progressive finite-energy integrand to [0,T]
gives a square-integrable function on the terminal-information product space. -/
theorem terminal_integrand_restriction {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t ≤ m)
    (c : ℕ → ℝ) (hco : ∀ r,∃ n,r ≤ c n)
    (H : progressiveEnergyIntegrands F c (P.prod (volume.restrict (Ioi (0:ℝ)))))
    (T : ℝ) (hT : 0 ≤ T) :
    @Measurable _ _ ((F (realTimeClamp T)).prod inferInstance) inferInstance
      (fun z : Ω × Icc (0:ℝ) T => H.val (z.1,z.2.val)) ∧
    @MemLp _ _ ((F (realTimeClamp T)).prod inferInstance) _ _
      (fun z : Ω × Icc (0:ℝ) T => H.val (z.1,z.2.val)) 2
      (@Measure.prod Ω (Icc (0:ℝ) T) (F (realTimeClamp T)) inferInstance
        (P.trim (hle (realTimeClamp T))) (compactTimeMeasure T hT)) := by
  letI : Fact (0 ≤ T) := ⟨hT⟩
  have hp := compact_progressive_restriction F c hco H.val H.property.2.1 T
  have hm := hp.mono (progressive_space_le_product
    (fun t : Icc (0:ℝ) T => F (realTimeClamp t.val))
    (fun t => hF (real_time_clamp_mono t.property.2))) le_rfl
  refine ⟨hm,?_⟩
  apply (product_trim_memLp P (F (realTimeClamp T)) (hle _) (compactTimeMeasure T hT)
    _ hm 2).mpr
  exact compact_time_restriction_memLp P T hT H.val H.property.2.2

end Asakura.Chapter12
