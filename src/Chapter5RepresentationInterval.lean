import Chapter2ItoStoppedIntervalConstruction
import Chapter5RepresentationEndpoints

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- The increment's global representation can actually be restricted to
its time interval. This is constructed with the Chapter 2 stopping theorem,
not assumed merely from the terminal representation identity. -/
theorem represented_integral_restrict_to_interval
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t E, MeasurableSet[m] E → P E = 0 → MeasurableSet[F t] E)
    (X A : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (hA : LocalCovarianceWitness P F X X A)
    (c : ℕ → ℝ) (hc : ∀ n, 0 < c n) (hcm : StrictMono c) (hcT : ∀ n, (c n:EReal) < T)
    (hct : StrictMono (fun n => realTimeClamp (T := T) (c n)))
    (hcut : ∀ n, realTimeClamp (T := T) (c n) < ⊤)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < realTimeClamp (T := T) (c n))
    (hAm : ∀ n ω, MonotoneOn (fun r => A (realTimeClamp r) ω) (Icc 0 (c n)))
    (hAc : ∀ n ω, ContinuousOn (fun r => A (realTimeClamp r) ω) (Icc 0 (c n)))
    (H : Ω × ℝ → ℝ)
    (hH : ∀ n, @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) (c n) => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) (c n) => H (z.1,z.2.val)))
    (hi : ∀ n, ∀ᵐ ω ∂P, Integrable (fun r => H (ω,r)^2)
      (intervalStieltjes 0 (c n) (hc n).le (fun r => A (realTimeClamp r) ω) (hAm n ω)
        (fun r hr => (hAc n ω r hr).mono inter_subset_left)).measure)
    (hHm : ∀ ω, Measurable (fun r => H (ω,r)))
    (M : ClosedTime T → Ω → ℝ) (hM : LocalMProcessWitness P F M)
    (hMI : ItoCovarianceFormula P F X H M)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hbT : (b:EReal) < T)
    (ξ : Ω → ℝ) (hMa : M (realTimeClamp a) =ᵐ[P] 0)
    (hMb : M (realTimeClamp b) =ᵐ[P] ξ) :
    ∃ Z : ClosedTime T → Ω → ℝ,
      LocalMProcessWitness P F Z ∧
      ItoCovarianceFormula P F X
        (fun z => (Ioc a b).indicator (fun r => H (z.1,r)) z.2) Z ∧
      Z (realTimeClamp b) =ᵐ[P] ξ ∧
      (∀ᵐ w ∂P,∀ t,t < ⊤ → Z t w = M (min (realTimeClamp b) t) w-M (min (realTimeClamp a) t) w) := by
  have hb : 0 ≤ b := ha.trans hab
  have haT : (a:EReal) < T := (EReal.coe_le_coe hab).trans_lt hbT
  have hs (r : ℝ) : ∀ t,MeasurableSet[F t] {w : Ω | realTimeClamp (T := T) r ≤ t} := by
    intro t
    by_cases h : realTimeClamp (T := T) r ≤ t <;> simp [h]
  obtain ⟨Y,Z,hY,hZ,hYI,hZI,he⟩ := ito_stochastic_interval_constructed
    P hT F hF hle hnull X A hX hA c hc hcm hcT hct hcut hcc hAm hAc H hH hi hHm
    (fun _ => a) (fun _ => b) (fun _ => ha) (fun _ => hb)
    (fun _ => haT) (fun _ => hbT) (fun _ => hab) (hs a) (hs b)
  have hYM := ItoCovarianceFormula.unique P hT F hF hle hnull X Y M H hX hY hM hYI hMI
  have heM : ∀ᵐ w ∂P,∀ t,t < ⊤ → Z t w = M (min (realTimeClamp b) t) w-M (min (realTimeClamp a) t) w := by
    filter_upwards [he,hYM] with w hw hmw
    intro t ht
    rw [hw t ht,hmw _ (lt_of_le_of_lt (min_le_right _ _) ht),hmw _ (lt_of_le_of_lt (min_le_right _ _) ht)]
  have hbt : realTimeClamp (T := T) b < ⊤ := by
    change (realTimeClamp b : EReal) < T
    rw [real_time_clamp_eq b hb hbT.le]; exact hbT
  have hab' : realTimeClamp (T := T) a ≤ realTimeClamp b := real_time_clamp_mono hab
  refine ⟨Z,hZ,hZI,?_,heM⟩
  filter_upwards [heM,hMa,hMb] with w hw h0 h1
  simpa only [min_self,min_eq_left hab',h0,h1,Pi.zero_apply,sub_zero] using hw _ hbt

end Asakura.Chapter5
