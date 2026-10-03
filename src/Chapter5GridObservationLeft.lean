import Chapter5GaussianObservationLeft
import Chapter5ObservationGrid

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 4800000
set_option backward.isDefEq.respectTransparency false

/-- The actual one-step theorem specialized to the manuscript's finite
observation grid. All regularity of the new payoff is supplied by its
constructed Gaussian average. -/
theorem grid_observation_left_M2_step
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t N,MeasurableSet[m] N → P N=0 → MeasurableSet[F t] N)
    {n k : ℕ} (W : Fin (n+1) → ClosedTime T → Ω → ℝ) (A : ClosedTime T → Ω → ℝ)
    (hW : ∀ i,LocalMProcessWitness P F (W i))
    (hC : ∀ i j,LocalCovarianceWitness P F (W i) (W j) (fun t w => if i=j then A t w else 0))
    (hclock : ∀ w (r : ℝ),0≤r → (r:EReal)<T → A (realTimeClamp r) w=r)
    (c : ℕ → ℝ) (hc : ∀ j,0≤c j) (hcm : Monotone c) (hcT : ∀ j,(c j:EReal)<T)
    (hcc : ∀ t,t<⊤ → ∃ j,t<realTimeClamp (T := T) (c j))
    (index : Fin k → Fin (n+1)) (q : ℕ → ℝ) (hq : StrictMono q) (hq0 : q 0=0)
    (obs : Fin k → ℕ) (j : ℕ) (hnext : (q (j+1):EReal)<T)
    (u : SmoothCylinderData (Fin k → ℝ)) :
    let active := fun i => j+1≤obs i
    let v := u.gaussianAverage n (observationNoiseMap index active) (q (j+1)-q j)
    ∃ G : Fin k → Ω × ℝ → ℝ, ∃ Z : Fin k → ClosedTime T → Ω → ℝ,
      (∀ i w t,ContinuousWithinAt (fun r => G i (w,r)) (Iic t) t) ∧
      (∀ i w r,|G i (w,r)|≤u.firstBound) ∧
      (∀ i (r : ℝ),0≤r → (r:EReal)<T → Measurable[F (realTimeClamp r)] (fun w => G i (w,r))) ∧
      (∀ i t w,realTimeClamp (q (j+1))≤t → Z i t w=Z i ⊤ w) ∧
      (∀ i,ContinuousM2Witness P F (Z i)) ∧
      (∀ i,ItoCovarianceFormula P F (W (index i)) (G i) (Z i)) ∧
      (∀ i,Measurable (G i) ∧ MemLp (G i) 2 (P.prod (volume.restrict (Ioi 0)))) ∧
      (∀ i (b : ℝ) (hb : 0≤b), (b:EReal)<T →
        @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) b => F (realTimeClamp t.val))) inferInstance
          (fun z : Ω × Icc (0:ℝ) b => G i (z.1,z.2.val))) ∧
      (∀ i,(∫ w,Z i ⊤ w ∂P)=0) ∧
      (fun w => u.value (fun i => W (index i) (realTimeClamp (min (q (obs i)) (q (j+1)))) w)) =ᵐ[P]
        fun w => v.value (fun i => W (index i) (realTimeClamp (min (q (obs i)) (q j))) w)+
          ∑ i ∈ Finset.univ.filter active,Z i ⊤ w := by
  classical
  dsimp only
  let active := fun i => j+1≤obs i
  let σ := fun i => min (q (obs i)) (q (j+1))
  have hqnonneg l : 0≤q l := by simpa only [hq0] using hq.monotone (Nat.zero_le l)
  have hσ i : 0≤σ i := le_min (hqnonneg _) (hqnonneg _)
  have hσT i : (σ i:EReal)<T := (EReal.coe_le_coe (min_le_right _ _)).trans_lt hnext
  have hgrid := grid_clipped_observation_step q hq.monotone obs j
  obtain ⟨G,Z,hGl,hGb,hGa,hGs,hZ,hZI,hGe,hGp,hZm,hrep⟩ := gaussian_observation_left_M2_representation
    P hT F hF hle hnull W A hW hC hclock c hc hcm hcT hcc index active σ hσ hσT
    (q j) (q (j+1)) (hqnonneg j) (hq (Nat.lt_succ_self j)) hnext hgrid.2 hgrid.1
    u.value u.first u.second u.derivative u.secondDerivative u.firstContinuous u.secondContinuous
    u.firstBound u.secondBound u.first_le u.second_le
  refine ⟨G,Z,hGl,hGb,hGa,hGs,hZ,hZI,hGe,hGp,hZm,?_⟩
  have hmin (x y : ℝ) : min (realTimeClamp (T := T) x) (realTimeClamp y)=realTimeClamp (min x y) := by
    rcases le_total x y with hh|hh
    · rw [min_eq_left hh,min_eq_left (real_time_clamp_mono hh)]
    · rw [min_eq_right hh,min_eq_right (real_time_clamp_mono hh)]
  have he i : min (realTimeClamp (T := T) (σ i)) (realTimeClamp (q j))=
      realTimeClamp (min (q (obs i)) (q j)) := by
    rw [hmin]
    exact congrArg realTimeClamp (grid_clipped_observation_previous q hq.monotone obs j i)
  simpa only [SmoothCylinderData.gaussianAverage,SmoothCylinderData.average_value,he,σ,active] using hrep

end Asakura.Chapter5
