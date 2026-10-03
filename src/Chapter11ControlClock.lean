import Chapter11MixedStepDensity

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter2Complete
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

lemma interval_stieltjes_add (a b : ℝ) (hab : a≤b) (A B : ℝ → ℝ)
    (hA : MonotoneOn A (Icc a b)) (hB : MonotoneOn B (Icc a b))
    (hAc : ContinuousOn A (Icc a b)) (hBc : ContinuousOn B (Icc a b)) :
    (intervalStieltjes a b hab (fun r => A r+B r) (hA.add hB)
      (fun r hr => ((hAc.add hBc) r hr).mono inter_subset_left)).measure=
      (intervalStieltjes a b hab A hA (fun r hr => (hAc r hr).mono inter_subset_left)).measure+
      (intervalStieltjes a b hab B hB (fun r hr => (hBc r hr).mono inter_subset_left)).measure := by
  rw [←StieltjesFunction.measure_add]
  congr 1


/-- The sum of the quadratic-variation and total-variation clocks supplies
 the common adapted approximants, even when H is only L1 for the latter. -/
theorem two_clock_step_density
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (b : ℝ) (hb : 0<b) [Fact (0≤b)] (A B : Ω → ℝ → ℝ)
    (hA : ∀ w,MonotoneOn (A w) (Icc 0 b)) (hB : ∀ w,MonotoneOn (B w) (Icc 0 b))
    (hAc : ∀ w,ContinuousOn (A w) (Icc 0 b)) (hBc : ∀ w,ContinuousOn (B w) (Icc 0 b))
    (hAm : ∀ t,Measurable (fun w => A w t)) (hBm : ∀ t,Measurable (fun w => B w t))
    (F : Icc (0:ℝ) b → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤‹MeasurableSpace Ω›)
    (hAa : ∀ t : Icc (0:ℝ) b,Measurable[F t] (fun w => A w t.val))
    (hBa : ∀ t : Icc (0:ℝ) b,Measurable[F t] (fun w => B w t.val))
    (hnull : ∀ t N,MeasurableSet N → P N=0 → MeasurableSet[F t] N)
    (H : Ω × Icc (0:ℝ) b → ℝ) (hH : @Measurable _ _ (progressiveSpace F) inferInstance H) :
    let α := fun w => (intervalStieltjes 0 b hb.le (A w) (hA w) (fun r hr => (hAc w r hr).mono inter_subset_left)).measure
    let β := fun w => (intervalStieltjes 0 b hb.le (B w) (hB w) (fun r hr => (hBc w r hr).mono inter_subset_left)).measure
    (∀ᵐ w ∂P,Integrable (fun r => (H (w,projIcc 0 b hb.le r))^2) (α w)) →
    (∀ᵐ w ∂P,Integrable (fun r => |H (w,projIcc 0 b hb.le r)|) (β w)) →
    ∃ (N : ℕ → ℕ) (u : ℕ → ℕ → Icc (0:ℝ) b) (V : ℕ → ℕ → Ω → ℝ),
      (∀ n,StrictMonoOn (u n) (Iic (N n))) ∧
      (∀ n j,j<N n → Measurable[F (u n j)] (V n j) ∧ MemLp (V n j) ∞ P) ∧
      let J := fun n (z : Ω × ℝ) => ∑ j∈Finset.range (N n),(Ico (u n j) (u n (j+1))).indicator (fun _ => V n j z.1) (projIcc 0 b hb.le z.2)
      (∀ n,Measurable (J n)) ∧
      (∀ n,∀ᵐ w ∂P,Integrable (fun r => (J n (w,r)-H (w,projIcc 0 b hb.le r))^2) (α w)) ∧
      (∀ n,∀ᵐ w ∂P,Integrable (fun r => |J n (w,r)-H (w,projIcc 0 b hb.le r)|) (β w)) ∧
      (∀ ε>0,Tendsto (fun n => P {w | ε≤∫ r,(J n (w,r)-H (w,projIcc 0 b hb.le r))^2 ∂α w}) atTop (𝓝 0)) ∧
      (∀ ε>0,Tendsto (fun n => P {w | ε≤∫ r,|J n (w,r)-H (w,projIcc 0 b hb.le r)| ∂β w}) atTop (𝓝 0)) := by
  intro α β hiA hiB
  letI (w : Ω) : IsFiniteMeasure (α w) := intervalStieltjes_finite 0 b hb.le (A w) (hA w) _
  letI (w : Ω) : IsFiniteMeasure (β w) := intervalStieltjes_finite 0 b hb.le (B w) (hB w) _
  apply finite_mixed_step_density P b hb (fun w r => A w r+B w r)
    (fun w => (hA w).add (hB w)) (fun w => (hAc w).add (hBc w))
    (fun r => (hAm r).add (hBm r)) F hF hle (fun t => (hAa t).add (hBa t)) hnull H hH α β
  · intro w
    rw [interval_stieltjes_add 0 b hb.le (A w) (B w) (hA w) (hB w) (hAc w) (hBc w)]
    intro s
    exact le_add_right le_rfl
  · intro w
    rw [interval_stieltjes_add 0 b hb.le (A w) (B w) (hA w) (hB w) (hAc w) (hBc w)]
    intro s
    exact le_add_left le_rfl
  · intro f hf
    exact random_stieltjes_integral_measurable 0 b hb.le A hA hAc hAm f hf
  · intro f hf
    exact random_stieltjes_integral_measurable 0 b hb.le B hB hBc hBm f hf
  · exact hiA
  · exact hiB

end Asakura.Chapter11
