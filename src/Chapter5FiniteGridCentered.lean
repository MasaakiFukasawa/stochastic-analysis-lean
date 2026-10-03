import Chapter5ObservationIsometry
import Chapter5FiniteCentering
import Chapter5CompactCylinderData

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 4800000
set_option backward.isDefEq.respectTransparency false

/-- The smooth finite-grid cylinder is represented by the actual complete
Brownian isometry. Its expectation is derived, and every Gaussian recursion
step and interval integral has been constructed. -/
theorem finite_grid_centered_isometry
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
    (N : ℕ) (hqNT : (q N:EReal)<T) (obs : Fin k → ℕ) (hobs : ∀ i,obs i≤N)
    (u : SmoothCylinderData (Fin k → ℝ))
    (I : Fin (n+1) → progressiveEnergyRange F c (P.prod (volume.restrict (Ioi 0))) →ₗᵢ[ℝ] Lp ℝ 2 P)
    (L : PiLp 2 (fun _ : Fin (n+1) => progressiveEnergyRange F c (P.prod (volume.restrict (Ioi 0)))) →ₗᵢ[ℝ] Lp ℝ 2 P)
    (hL : ∀ x,L x=∑ i,I i (x i))
    (hI : ∀ i,∀ H : progressiveEnergyIntegrands F c (P.prod (volume.restrict (Ioi 0))),
      ∃ M : ClosedTime T → Ω → ℝ,∃ hM : ContinuousM2Witness P F M,
        ItoCovarianceFormula P F (W i) H.val M ∧
        I i ⟨progressiveEnergyToLp F c _ H,LinearMap.mem_range_self _ H⟩=(hM.moment ⊤).toLp (M ⊤))
    (hf : MemLp (fun w => u.value (fun i => W (index i) (realTimeClamp (q (obs i))) w)) 2 P) :
    ∃ x,L x=hf.toLp _-(condExpL2 ℝ ℝ bot_le (hf.toLp _) : Lp ℝ 2 P) := by
  classical
  obtain ⟨J,hrep⟩ := finite_grid_observation_representation P hT F hF hle hnull W A hW hC hclock
    c hc hcm hcT hcc index q hq hq0 N hqNT obs hobs u
  let s : Finset (Fin N × Fin k) := Finset.univ.filter (fun p => N-p.1.val≤obs p.2)
  let g := fun p : Fin N × Fin k => (J p.1).integral p.2 ⊤
  have hg p : MemLp (g p) 2 P := (J p.1).martingale p.2 |>.moment ⊤
  have hr p : ∃ x,L x=(hg p).toLp (g p) :=
    observation_integral_isometry_realization P hT F hF hle hnull W hW index c hc hcT (J p.1) I L hL hI p.2
  have hs w : (∑ p∈s,g p w)=
      ∑ l : Fin N,∑ i ∈ Finset.univ.filter (fun i => N-l.val≤obs i),(J l).integral i ⊤ w := by
    simp only [s,Finset.sum_filter,Fintype.sum_prod_type,g]
  apply finite_integral_representation_centered P L s g hg (fun p => (J p.1).mean p.2) hr _ hf
    (gaussianRecursion u n (fun l => observationNoiseMap index (fun i => N-l≤obs i))
      (fun l => q (N-l)-q (N-(l+1))) N |>.value 0)
  simpa only [hs] using hrep

end Asakura.Chapter5
