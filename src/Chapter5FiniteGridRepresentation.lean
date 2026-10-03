import Chapter5GridObservationStep
import Chapter5FiniteTelescoping

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 4800000
set_option backward.isDefEq.respectTransparency false

/-- Data of the actual observation integrals, with all analytic obligations. -/
structure ObservationIntegralData
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (F : ClosedTime T → MeasurableSpace Ω)
    {d k : ℕ} (W : Fin d → ClosedTime T → Ω → ℝ) (index : Fin k → Fin d) where
  integrand : Fin k → Ω × ℝ → ℝ
  integral : Fin k → ClosedTime T → Ω → ℝ
  martingale : ∀ i,ContinuousM2Witness P F (integral i)
  formula : ∀ i,ItoCovarianceFormula P F (W (index i)) (integrand i) (integral i)
  energy : ∀ i,Measurable (integrand i) ∧ MemLp (integrand i) 2 (P.prod (volume.restrict (Ioi 0)))
  progressive : ∀ i (b : ℝ), 0≤b → (b:EReal)<T →
    @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) b => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) b => integrand i (z.1,z.2.val))
  mean : ∀ i,(∫ w,integral i ⊤ w ∂P)=0

/-- Finite backward Gaussian recursion, constructed from the actual
one-interval Ito theorem at every step and telescoped on a common null set. -/
theorem finite_grid_observation_representation
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
    (u : SmoothCylinderData (Fin k → ℝ)) :
    let Q := fun l => observationNoiseMap index (fun i => N-l≤obs i)
    let dt := fun l => q (N-l)-q (N-(l+1))
    let U := gaussianRecursion u n Q dt
    ∃ J : Fin N → ObservationIntegralData P F W index,
      (fun w => u.value (fun i => W (index i) (realTimeClamp (q (obs i))) w)) =ᵐ[P]
        fun w => (U N).value 0+
          ∑ l : Fin N,∑ i ∈ Finset.univ.filter (fun i => N-l.val≤obs i),(J l).integral i ⊤ w := by
  classical
  dsimp only
  let Q := fun l => observationNoiseMap index (fun i => N-l≤obs i)
  let dt := fun l => q (N-l)-q (N-(l+1))
  let U := gaussianRecursion u n Q dt
  let V : ℕ → Ω → ℝ := fun l w => (U l).value
    (fun i => W (index i) (realTimeClamp (min (q (obs i)) (q (N-l)))) w)
  have hstep (l : Fin N) : ∃ J : ObservationIntegralData P F W index,
      V l.val =ᵐ[P] fun w => V (l.val+1) w+
        ∑ i ∈ Finset.univ.filter (fun i => N-l.val≤obs i),J.integral i ⊤ w := by
    let j := N-(l.val+1)
    have hj : j+1=N-l.val := by dsimp only [j]; omega
    have hjN : j+1≤N := by rw [hj]; omega
    obtain ⟨G,Z,hZ,hZI,hGe,hGp,hZm,hrep⟩ := grid_observation_M2_step P hT F hF hle hnull
      W A hW hC hclock c hc hcm hcT hcc index q hq hq0 obs j
      ((EReal.coe_le_coe (hq.monotone hjN)).trans_lt hqNT) (U l.val)
    let J : ObservationIntegralData P F W index := {
      integrand := G
      integral := Z
      martingale := hZ
      formula := hZI
      energy := hGe
      progressive := hGp
      mean := hZm }
    refine ⟨J,?_⟩
    simpa only [V,U,gaussianRecursion,dt,Q,j,hj] using hrep
  choose J hJ using hstep
  have ht := finite_ae_reverse_telescope P N V
    (fun l w => ∑ i ∈ Finset.univ.filter (fun i => N-l.val≤obs i),(J l).integral i ⊤ w) hJ
  have hzero : realTimeClamp (T := T) 0=⊥ := by
    apply Subtype.ext
    exact (real_time_clamp_eq 0 le_rfl (by exact_mod_cast hT.le)).trans (by simp)
  have hinit : ∀ᵐ w ∂P,∀ i : Fin k,W (index i) ⊥ w=0 :=
    ae_all_iff.mpr (fun i => (hW (index i)).initial P F)
  refine ⟨J,?_⟩
  filter_upwards [ht,hinit] with w hw hz
  have hV0 : V 0 w=u.value (fun i => W (index i) (realTimeClamp (q (obs i))) w) := by
    dsimp only [V,U,gaussianRecursion,Nat.sub_zero]
    congr 1
    funext i
    rw [min_eq_left (hq.monotone (hobs i))]
  have hVN : V N w=(U N).value 0 := by
    dsimp only [V]
    congr 1
    funext i
    rw [Nat.sub_self,grid_clipped_observation_zero q hq.monotone hq0 obs i,hzero,hz i]
    rfl
  rw [hV0,hVN] at hw
  exact hw

end Asakura.Chapter5
