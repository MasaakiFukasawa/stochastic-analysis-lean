import Chapter6IntervalDensity
import Chapter6FiniteDensityProduct

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false

lemma exp_increment_product (f : ℕ → ℝ) (n : ℕ) :
    (∏ i ∈ Finset.range n,Real.exp (f (i+1)-f i)) = Real.exp (f n-f 0) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ,ih,← Real.exp_add]
    congr 1
    ring

/-- The finite-partition Novikov criterion, including the conditional mean
of each interval factor, integrability of the product, and telescoping.
The partition reaches the endpoint in finitely many steps, as Pi_Lambda
is defined in the manuscript. -/
theorem finite_partition_novikov_written
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t ≤ m)
    (hnull : ∀ t N,MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (Z C : ClosedTime T → Ω → ℝ) (hZ : LocalMProcessWitness P F Z)
    (hC : LocalCovarianceWitness P F Z Z C)
    (τ : Ω → ClosedTime T) (hτ : ∀ t,MeasurableSet[F t] {w | τ w ≤ t})
    (hτt : ∀ w,τ w < ⊤)
    (t : ℕ → ClosedTime T) (ht : Monotone t) (ht0 : t 0 = ⊥)
    (N : ℕ) (htN : t N = ⊤) (γ : ℝ) (hγ : 1/2 < γ)
    (hi : ∀ i,i < N → Integrable (fun w =>
      Real.exp (γ*(C (min (t (i+1)) (τ w)) w-C (min (t i) (τ w)) w))) P) :
    let M := fun s w => Real.exp (Z (min (τ w) s) w-C (min (τ w) s) w/2)
    (∀ s,Integrable (M s) P) ∧
    (∀ s r,s ≤ r → P[M r|F s] =ᵐ[P] M s) ∧ (∫ w,M ⊤ w ∂P) = 1 := by
  have htlate i (hi : N ≤ i) : t i = ⊤ := top_unique (htN ▸ ht hi)
  have hiAll i : Integrable (fun w =>
      Real.exp (γ*(C (min (t (i+1)) (τ w)) w-C (min (t i) (τ w)) w))) P := by
    by_cases hin : i < N
    · exact hi i hin
    · have hn := Nat.le_of_not_gt hin
      simp only [htlate i hn,htlate (i+1) (hn.trans (Nat.le_succ i)),min_top_left,
        sub_self,mul_zero,Real.exp_zero]
      exact integrable_const _
  let r := fun i w => Real.exp ((Z (min (t (i+1)) (τ w)) w-Z (min (t i) (τ w)) w)-
    (C (min (t (i+1)) (τ w)) w-C (min (t i) (τ w)) w)/2)
  have hr i : Measurable[F (t (i+1))] (r i) ∧ Integrable (r i) P ∧
      P[r i|F (t i)] =ᵐ[P] (fun _ => (1:ℝ)) :=
    novikov_interval_density P hT F hF hle hnull Z C hZ hC τ hτ hτt
      (t i) (t (i+1)) (ht (Nat.le_succ i)) γ hγ (hiAll i)
  let d : ℕ → Ω → ℝ≥0 := fun i w => ⟨r i w,(Real.exp_pos _).le⟩
  have hd i : Measurable[F (t (i+1))] (d i) := (hr i).1.subtype_mk
  obtain ⟨hprodI,_,hprodmean⟩ := finite_conditional_density_product P (fun i => F (t i))
    (hF.comp ht) (fun i => hle (t i)) d hd (fun i => (hr i).2.1) (fun i => (hr i).2.2)
  have hz := local_initial_zero P F Z hZ
  have hc0 := local_quadratic_variation_initial P F Z C hZ hC
  have he : (fun w => ∏ i ∈ Finset.range N,(d i w : ℝ)) =ᵐ[P]
      (fun w => Real.exp (Z (τ w) w-C (τ w) w/2)) := by
    filter_upwards [hz,hc0] with w hw hc
    let f := fun i => Z (min (t i) (τ w)) w-C (min (t i) (τ w)) w/2
    have hinc i : (d i w : ℝ) = Real.exp (f (i+1)-f i) := by
      change Real.exp ((Z (min (t (i+1)) (τ w)) w-Z (min (t i) (τ w)) w)-
        (C (min (t (i+1)) (τ w)) w-C (min (t i) (τ w)) w)/2) = Real.exp (f (i+1)-f i)
      dsimp [f]
      congr 1
      ring
    simp_rw [hinc]
    rw [exp_increment_product]
    simp only [f,ht0,htN,min_top_left,min_bot_left,hw,hc,Pi.zero_apply,zero_div,sub_zero]
  have hmean : (∫ w,Real.exp (Z (τ w) w-C (τ w) w/2) ∂P) = 1 := by
    rw [← integral_congr_ae he]
    exact hprodmean N
  obtain ⟨_,hMi,_,hMm,_⟩ := stochastic_exponential_closed_martingale P hT F hF hle hnull Z C hZ hC τ hτ hτt hmean
  exact ⟨hMi,hMm,by simpa only [min_top_right] using hmean⟩

end Asakura.Chapter6
