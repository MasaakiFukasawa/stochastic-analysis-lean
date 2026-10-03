import Chapter6ExponentialLocal
import Chapter2LowerBoundedLocal

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

/-- The mean-one hypothesis in Girsanov--Maruyama upgrades the constructed
positive local exponential to the actual closed density martingale. -/
theorem stochastic_exponential_closed_martingale
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t ≤ m)
    (hnull : ∀ t N,MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (Z C : ClosedTime T → Ω → ℝ) (hZ : LocalMProcessWitness P F Z)
    (hC : LocalCovarianceWitness P F Z Z C)
    (τ : Ω → ClosedTime T) (hτ : ∀ t,MeasurableSet[F t] {w | τ w ≤ t})
    (hτt : ∀ w,τ w < ⊤)
    (hmean : (∫ w,Real.exp (Z (τ w) w-C (τ w) w/2) ∂P) = 1) :
    let M := fun t w => Real.exp (Z (min (τ w) t) w-C (min (τ w) t) w/2)
    (∀ t,Measurable[F t] (M t)) ∧ (∀ t,Integrable (M t) P) ∧
    (∀ w,Continuous (fun t => M t w)) ∧
    (∀ s t,s ≤ t → P[M t|F s] =ᵐ[P] M s) ∧
    (∀ t,M t =ᵐ[P] P[M ⊤|F t]) := by
  let X := fun t w => Real.exp (Z t w-C t w/2)-1
  have hX := stochastic_exponential_local P hT F hF hle hnull Z C hZ hC
  have hb : ∀ᵐ w ∂P,∀ t,t < ⊤ → -(1:ℝ) ≤ X t w :=
    .of_forall fun w t _ => by dsimp [X]; linarith [Real.exp_pos (Z t w-C t w/2)]
  obtain ⟨_,hXi,_,_,_⟩ := lower_bounded_local_stopped_supermartingale P F hF hle X hX τ hτ hτt 1 hb
  have hEi : Integrable (fun w => Real.exp (Z (τ w) w-C (τ w) w/2)) P := by
    convert (hXi ⊤).add (integrable_const (1:ℝ)) using 1
    funext w
    simp [X]
  have hzero : (∫ w,X (τ w) w ∂P) = 0 := by
    dsimp only [X]
    rw [integral_sub hEi (integrable_const (1:ℝ)),hmean,integral_const]
    simp
  obtain ⟨ha,hi,hc,hm,_⟩ := lower_bounded_local_zero_terminal_mean_is_martingale P F hF hle
    X hX τ hτ hτt 1 hb hzero
  let M := fun t w => Real.exp (Z (min (τ w) t) w-C (min (τ w) t) w/2)
  have he (t) : M t = fun w => X (min (τ w) t) w+1 := by funext w; simp [M,X]
  have hma t : Measurable[F t] (M t) := by rw [he]; exact (ha t).add measurable_const
  have hmi t : Integrable (M t) P := by rw [he]; exact (hi t).add (integrable_const _)
  have hmc w : Continuous (fun t => M t w) := by
    simp_rw [he]
    exact (hc w).add continuous_const
  have hmm s t (hst : s ≤ t) : P[M t|F s] =ᵐ[P] M s := by
    rw [he t,he s]
    have hh := condExp_add (hi t) (integrable_const (1:ℝ)) (m := F s)
    filter_upwards [hh,hm s t hst] with w hw hm
    change P[(fun w => X (min (τ w) t) w+1)|F s] w =
      P[(fun w => X (min (τ w) t) w)|F s] w+P[(fun _ => (1:ℝ))|F s] w at hw
    rw [hw,hm,condExp_const (μ := P) (hle s) (1:ℝ)]
  exact ⟨hma,hmi,hmc,hmm,fun t => (hmm t ⊤ le_top).symm⟩

end Asakura.Chapter6
