import Chapter5StoppedObservationCovariance
import Chapter5ClippedClockDensity

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- Repeated coordinates of Brownian motion, stopped at the observation
times, give an adapted vector process with explicit covariance densities.
After a past observation time its density is zero. -/
theorem stopped_brownian_observation_family
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t,F t ≤ m)
    (hnull : ∀ t N,MeasurableSet[m] N → P N=0 → MeasurableSet[F t] N)
    {d k : ℕ} (W : Fin d → ClosedTime T → Ω → ℝ) (A : ClosedTime T → Ω → ℝ)
    (hW : ∀ i,LocalMProcessWitness P F (W i))
    (hC : ∀ i j,LocalCovarianceWitness P F (W i) (W j) (fun t w => if i=j then A t w else 0))
    (hclock : ∀ w (r : ℝ),0≤r → (r:EReal)<T → A (realTimeClamp r) w=r)
    (c : ℕ → ClosedTime T) (hcm : Monotone c) (hct : ∀ n,c n<⊤)
    (hcc : ∀ t,t<⊤ → ∃ n,t<c n)
    (index : Fin k → Fin d) (τ : Fin k → ℝ) (hτ : ∀ i,0≤τ i) (hτT : ∀ i,(τ i:EReal)<T) :
    let X := fun i t w => W (index i) (min (realTimeClamp (τ i)) t) w
    let C := fun i j t w => if index i=index j then A (min (min (realTimeClamp (τ i)) (realTimeClamp (τ j))) t) w else 0
    (∀ i,LocalMProcessWitness P F (X i)) ∧
      (∀ i j,LocalCovarianceWitness P F (X i) (X j) (C i j)) ∧
      (∀ i j w (r : ℝ),0≤r → (r:EReal)<T → C i j (realTimeClamp r) w=
        ∫ s in 0..r,if index i=index j then (Iio (min (τ i) (τ j))).indicator (fun _ => (1:ℝ)) s else 0) := by
  dsimp only
  have hs i : ∀ t,MeasurableSet[F t] {w : Ω | realTimeClamp (T := T) (τ i)≤t} := by
    intro t
    by_cases h : realTimeClamp (T := T) (τ i)≤t <;> simp [h]
  have ht i : realTimeClamp (T := T) (τ i)<⊤ := by
    change (realTimeClamp (τ i):EReal)<T
    rw [real_time_clamp_eq _ (hτ i) (hτT i).le]; exact hτT i
  refine ⟨fun i => (hW (index i)).stopped P F hF hle _ (hs i),?_,?_⟩
  · intro i j
    exact different_stopped_covariance P F hF hle hnull _ _ _ (hW (index i)) (hW (index j))
      (hC (index i) (index j)) c hcm hct hcc _ _ (ht i) (ht j)
  · intro i j w r hr hrT
    by_cases hij : index i=index j
    · simp only [hij,ite_true]
      rw [← real_time_clamp_mono.map_min,← real_time_clamp_mono.map_min]
      rw [hclock w _ (le_min (le_min (hτ i) (hτ j)) hr)
        ((EReal.coe_le_coe (min_le_right _ _)).trans_lt hrT)]
      exact (clipped_clock_density_integral (min (τ i) (τ j)) r (le_min (hτ i) (hτ j)) hr).symm
    · simp only [hij,ite_false,intervalIntegral.integral_zero]

end Asakura.Chapter5
