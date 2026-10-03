import Chapter11FiniteClockExtension

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter4
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

/-- No condition is imposed on unused clock values outside the finite prefix. -/
theorem local_clock_step_density
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (b : ℝ) (hb : 0<b) [Fact (0≤b)] (A B : Ω → ℝ → ℝ)
    (hA : ∀ w,MonotoneOn (A w) (Icc 0 b)) (hB : ∀ w,MonotoneOn (B w) (Icc 0 b))
    (hAc : ∀ w,ContinuousOn (A w) (Icc 0 b)) (hBc : ∀ w,ContinuousOn (B w) (Icc 0 b))
    (hAm : ∀ t,t∈Icc 0 b → Measurable (fun w => A w t)) (hBm : ∀ t,t∈Icc 0 b → Measurable (fun w => B w t))
    {T : EReal} [Fact (0≤T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤‹MeasurableSpace Ω›)
    (hAa : ∀ t : Icc (0:ℝ) b,Measurable[F (realTimeClamp t.val)] (fun w => A w t.val))
    (hBa : ∀ t : Icc (0:ℝ) b,Measurable[F (realTimeClamp t.val)] (fun w => B w t.val))
    (hnull : ∀ t N,MeasurableSet N → P N=0 → MeasurableSet[F t] N)
    (H : Ω × ℝ → ℝ)
    (hH : @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) b => F (realTimeClamp t.val))) inferInstance (fun z : Ω × Icc (0:ℝ) b => H (z.1,z.2.val))) :
    let α := fun w => (intervalStieltjes 0 b hb.le (A w) (hA w) (fun r hr => (hAc w r hr).mono inter_subset_left)).measure
    let β := fun w => (intervalStieltjes 0 b hb.le (B w) (hB w) (fun r hr => (hBc w r hr).mono inter_subset_left)).measure
    (∀ᵐ w ∂P,Integrable (fun r => (H (w,r))^2) (α w)) →
    (∀ᵐ w ∂P,Integrable (fun r => |H (w,r)|) (β w)) →
    ∃ (N : ℕ → ℕ) (u : ℕ → ℕ → ℝ) (V : ℕ → ℕ → Ω → ℝ),
      (∀ n,StrictMonoOn (u n) (Iic (N n))) ∧
      (∀ n i,u n i∈Icc 0 b) ∧
      (∀ n j,j<N n → Measurable[F (realTimeClamp (u n j))] (V n j) ∧ MemLp (V n j) ∞ P) ∧
      let J := fun n (z : Ω × ℝ) => ∑ j∈Finset.range (N n),(Ioc (u n j) (u n (j+1))).indicator (fun _ => V n j z.1) z.2
      (∀ n,Measurable (J n)) ∧
      (∀ n (d : ℝ),@Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) d => F (realTimeClamp t.val))) inferInstance (fun z : Ω × Icc (0:ℝ) d => J n (z.1,z.2.val))) ∧
      (∀ n,∀ᵐ w ∂P,Integrable (fun r => (J n (w,r)-H (w,r))^2) (α w)) ∧
      (∀ n,∀ᵐ w ∂P,Integrable (fun r => |J n (w,r)-H (w,r)|) (β w)) ∧
      (∀ ε>0,Tendsto (fun n => P {w | ε≤∫ r,(J n (w,r)-H (w,r))^2 ∂α w}) atTop (𝓝 0)) ∧
      (∀ ε>0,Tendsto (fun n => P {w | ε≤∫ r,|J n (w,r)-H (w,r)| ∂β w}) atTop (𝓝 0)) := by
  intro α β hiA hiB
  obtain ⟨hC,hCc,hCm,heC,hμC⟩ := finite_clock_extension b hb.le A hA hAc hAm
  obtain ⟨hD,hDc,hDm,heD,hμD⟩ := finite_clock_extension b hb.le B hB hBc hBm
  have hCa (t : Icc (0:ℝ) b) : Measurable[F (realTimeClamp t.val)] (fun w => A w (intervalClamp 0 b hb.le t.val)) := by
    simp only [intervalClamp_eq 0 b hb.le t.property]
    exact hAa t
  have hDa (t : Icc (0:ℝ) b) : Measurable[F (realTimeClamp t.val)] (fun w => B w (intervalClamp 0 b hb.le t.val)) := by
    simp only [intervalClamp_eq 0 b hb.le t.property]
    exact hBa t
  have hiC : ∀ᵐ w ∂P,Integrable (fun r => H (w,r)^2)
      (intervalStieltjes 0 b hb.le (fun r => A w (intervalClamp 0 b hb.le r)) (hC w)
        (fun r hr => (hCc w r hr).mono inter_subset_left)).measure := by
    simpa only [hμC] using hiA
  have hiD : ∀ᵐ w ∂P,Integrable (fun r => |H (w,r)|)
      (intervalStieltjes 0 b hb.le (fun r => B w (intervalClamp 0 b hb.le r)) (hD w)
        (fun r hr => (hDc w r hr).mono inter_subset_left)).measure := by
    simpa only [hμD] using hiB
  have hh := real_two_clock_step_density P b hb _ _ hC hD hCc hDc hCm hDm F hF hle hCa hDa hnull H hH hiC hiD
  simpa only [hμC,hμD] using hh

end Asakura.Chapter11
