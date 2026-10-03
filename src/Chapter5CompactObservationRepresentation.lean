import Chapter5FiniteObservationGrid

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 4800000
set_option backward.isDefEq.respectTransparency false

/-- Arbitrary finite observation times, including repetitions and time
zero, are sorted into the verified grid. Compact C² regularity supplies
all the bounds used by the actual Gaussian recursion. -/
theorem compact_observation_centered_isometry
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
    (index : Fin k → Fin (n+1)) (τ : Fin k → ℝ)
    (hτ : ∀ i,0≤τ i) (hτT : ∀ i,(τ i:EReal)<T)
    (f : (Fin k → ℝ) → ℝ) (hfd : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (I : Fin (n+1) → progressiveEnergyRange F c (P.prod (volume.restrict (Ioi 0))) →ₗᵢ[ℝ] Lp ℝ 2 P)
    (L : PiLp 2 (fun _ : Fin (n+1) => progressiveEnergyRange F c (P.prod (volume.restrict (Ioi 0)))) →ₗᵢ[ℝ] Lp ℝ 2 P)
    (hL : ∀ x,L x=∑ i,I i (x i))
    (hI : ∀ i,∀ H : progressiveEnergyIntegrands F c (P.prod (volume.restrict (Ioi 0))),
      ∃ M : ClosedTime T → Ω → ℝ,∃ hM : ContinuousM2Witness P F M,
        ItoCovarianceFormula P F (W i) H.val M ∧
        I i ⟨progressiveEnergyToLp F c _ H,LinearMap.mem_range_self _ H⟩=(hM.moment ⊤).toLp (M ⊤))
    (hf : MemLp (fun w => f (fun i => W (index i) (realTimeClamp (τ i)) w)) 2 P) :
    ∃ x,L x=hf.toLp _-(condExpL2 ℝ ℝ bot_le (hf.toLp _) : Lp ℝ 2 P) := by
  obtain ⟨u,hu⟩ := compact_cylinder_data f hfd hfc
  obtain ⟨N,q,obs,hq,hq0,hobs,he,hend⟩ := finite_observation_sorted_grid τ hτ
  have hNT : (q N:EReal)<T := by
    rcases hend with h0|⟨i,hi⟩
    · rw [h0]
      exact_mod_cast hT
    · rw [hi]
      exact hτT i
  have hefun : (fun w => u.value (fun i => W (index i) (realTimeClamp (q (obs i))) w))=
      (fun w => f (fun i => W (index i) (realTimeClamp (τ i)) w)) := by simp only [hu,he]
  have hfu : MemLp (fun w => u.value (fun i => W (index i) (realTimeClamp (q (obs i))) w)) 2 P := hefun.symm ▸ hf
  have hh := finite_grid_centered_isometry P hT F hF hle hnull W A hW hC hclock c hc hcm hcT hcc
    index q hq hq0 N hNT obs hobs u I L hL hI hfu
  simpa only [hefun] using hh

end Asakura.Chapter5
