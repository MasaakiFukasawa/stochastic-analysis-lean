import Chapter5BrownianIntegralBracket
import Chapter5BracketCommonTime

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

theorem clock_ito_integral_bracket_common
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t E, MeasurableSet[m] E → P E = 0 → MeasurableSet[F t] E)
    (W A X : ClosedTime T → Ω → ℝ) (hW : LocalMProcessWitness P F W)
    (hA : LocalCovarianceWitness P F W W A) (hX : LocalMProcessWitness P F X)
    (c : ℕ → ℝ) (hc : ∀ n, 0 < c n) (hcm : StrictMono c) (hcT : ∀ n, (c n:EReal) < T)
    (hct : StrictMono (fun n => realTimeClamp (T := T) (c n)))
    (hcut : ∀ n, realTimeClamp (T := T) (c n) < ⊤)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < realTimeClamp (T := T) (c n))
    (hclock : ∀ n w r, r ∈ Icc 0 (c n) → A (realTimeClamp r) w = r)
    (G : Ω × ℝ → ℝ)
    (hG : ∀ n, @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) (c n) => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) (c n) => G (z.1,z.2.val)))
    (hi : ∀ n, ∀ᵐ w ∂P, IntervalIntegrable (fun r => G (w,r)^2) volume 0 (c n))
    (hXI : ItoCovarianceFormula P F W G X) :
    ∃ C : ClosedTime T → Ω → ℝ, LocalCovarianceWitness P F X X C ∧
      (∀ d : ℝ, 0 ≤ d → (d:EReal) < T → C (realTimeClamp d) =ᵐ[P] fun w => ∫ r in 0..d,G (w,r)^2) ∧
      (∀ n, ∀ᵐ w ∂P, ∀ r ∈ Icc 0 (c n), C (realTimeClamp r) w = ∫ s in 0..r,G (w,s)^2) := by
  obtain ⟨C,hC,hCG⟩ := clock_ito_integral_bracket P hT F hF hle hnull
    W A X hW hA hX c hc hcm hcT hct hcut hcc hclock G hG hi hXI
  have hCGall n : ∀ᵐ w ∂P, ∀ r ∈ Icc 0 (c n), C (realTimeClamp r) w = ∫ s in 0..r, G (w,s)^2 := by
    refine bracket_primitive_common_time P (c n) (hc n).le (fun r => C (realTimeClamp r)) (fun w r => G (w,r)^2) ?_ (hi n) ?_
    · intro w r hr
      have hrt : realTimeClamp (T := T) r < ⊤ := by
        change (realTimeClamp r : EReal) < T
        rw [real_time_clamp_eq r hr.1 ((EReal.coe_le_coe hr.2).trans (hcT n).le)]
        exact (EReal.coe_le_coe hr.2).trans_lt (hcT n)
      have hm := hX.path P F w _ hrt
      have hh := (hm.mul hm).sub (hC.defect.path P F w _ hrt)
      have hcp : ContinuousAt (fun t => C t w) (realTimeClamp r) := by
        convert hh using 1
        funext t
        dsimp only [Pi.sub_apply,Pi.mul_apply]
        ring
      exact (hcp.comp real_time_clamp_continuous.continuousAt).continuousWithinAt
    · intro r hr
      exact hCG r hr.1 ((EReal.coe_le_coe hr.2).trans_lt (hcT n))
  exact ⟨C,hC,hCG,hCGall⟩

end Asakura.Chapter5
