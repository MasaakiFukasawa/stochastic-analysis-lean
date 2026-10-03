import Chapter5BoundedLeftRepresentation
import Chapter5FiniteObservationGrid

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false

/-- Arbitrary finite observation times, including repetitions and time zero,
are sorted internally. No extra L² assumption on the payoff is imposed. -/
theorem bounded_C2_observation_left_representation
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t N,MeasurableSet[m] N → P N=0 → MeasurableSet[F t] N)
    {n k : ℕ} (W : Fin (n+1) → ClosedTime T → Ω → ℝ) (A : ClosedTime T → Ω → ℝ)
    (hW : ∀ i,LocalMProcessWitness P F (W i))
    (hCOV : ∀ i j,LocalCovarianceWitness P F (W i) (W j) (fun t w => if i=j then A t w else 0))
    (hclock : ∀ w (r : ℝ),0≤r → (r:EReal)<T → A (realTimeClamp r) w=r)
    (c : ℕ → ℝ) (hc : ∀ j,0≤c j) (hcm : Monotone c) (hcT : ∀ j,(c j:EReal)<T)
    (hcc : ∀ t,t<⊤ → ∃ j,t<realTimeClamp (T := T) (c j))
    (index : Fin k → Fin (n+1)) (τ : Fin k → ℝ)
    (hτ : ∀ i,0≤τ i) (hτT : ∀ i,(τ i:EReal)<T)
    (f : (Fin k → ℝ) → ℝ) (hf : ContDiff ℝ 2 f) (C K : ℝ≥0)
    (hC : ∀ x i,|fderiv ℝ f x (Pi.single i 1)|≤C)
    (hK : ∀ x i j,|fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1)|≤K) :
    ∃ R : ℝ,0≤R ∧ (R:EReal)<T ∧ (∀ i,τ i≤R) ∧
    ∃ H : Fin (n+1) → Ω × ℝ → ℝ,∃ Z : Fin (n+1) → ClosedTime T → Ω → ℝ,∃ B : ℝ,
      (∀ i w t,ContinuousWithinAt (fun r => H i (w,r)) (Iic t) t) ∧
      (∀ i w r,|H i (w,r)|≤B) ∧
      (∀ i (r : ℝ),0≤r → (r:EReal)<T → Measurable[F (realTimeClamp r)] (fun w => H i (w,r))) ∧
      (∀ i,ContinuousM2Witness P F (Z i)) ∧
      (∀ i,ItoCovarianceFormula P F (W i) (H i) (Z i)) ∧
      (∀ i,Z i (realTimeClamp R)=Z i ⊤) ∧
      MemLp (fun w => f (fun i => W (index i) (realTimeClamp (τ i)) w)) 2 P ∧
      (fun w => f (fun i => W (index i) (realTimeClamp (τ i)) w)) =ᵐ[P]
        fun w => (∫ w,f (fun i => W (index i) (realTimeClamp (τ i)) w) ∂P)+
          ∑ i,Z i (realTimeClamp R) w := by
  obtain ⟨N,q,obs,hq,hq0,hobs,heq,hmax⟩ := finite_observation_sorted_grid τ hτ
  have hqNT : (q N:EReal)<T := by
    rcases hmax with hh|⟨i,hh⟩
    · rw [hh]; exact_mod_cast hT
    · rw [hh]; exact hτT i
  refine ⟨q N,?_,hqNT,?_,?_⟩
  · simpa only [hq0] using hq.monotone (Nat.zero_le N)
  · intro i; rw [← heq i]; exact hq.monotone (hobs i)
  · simpa only [heq] using bounded_C2_grid_left_representation P hT F hF hle hnull
      W A hW hCOV hclock c hc hcm hcT hcc index q hq hq0 N hqNT obs hobs f hf C K hC hK

end Asakura.Chapter5
