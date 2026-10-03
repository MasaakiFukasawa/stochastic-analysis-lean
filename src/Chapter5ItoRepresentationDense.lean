import Chapter5CompactObservationRepresentation
import Chapter2ProgressiveEnergyComplete

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 4800000
set_option backward.isDefEq.respectTransparency false

/-- The dense smooth representation hypothesis is now discharged by
actual finite Gaussian recursion and M² identification with the isometry. -/
theorem ito_representation_continuous_observations
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t N,MeasurableSet[m] N → P N=0 → MeasurableSet[F t] N)
    {n : ℕ} (W : Fin (n+1) → ClosedTime T → Ω → ℝ) (A : ClosedTime T → Ω → ℝ)
    (hW : ∀ i,LocalMProcessWitness P F (W i))
    (hC : ∀ i j,LocalCovarianceWitness P F (W i) (W j) (fun t w => if i=j then A t w else 0))
    (hclock : ∀ w (r : ℝ),0≤r → (r:EReal)<T → A (realTimeClamp r) w=r)
    (c : ℕ → ℝ) (hc : ∀ j,0≤c j) (hcm : Monotone c) (hcT : ∀ j,(c j:EReal)<T)
    (hcc : ∀ t,t<⊤ → ∃ j,t<realTimeClamp (T := T) (c j))
    {K : Type*} [TopologicalSpace K] [FirstCountableTopology K]
    (index : K → Fin (n+1)) (τ : K → ℝ)
    (hτ : ∀ t,0≤τ t) (hτT : ∀ t,(τ t:EReal)<T)
    (hXm : ∀ t,Measurable (W (index t) (realTimeClamp (τ t))))
    (hXc : ∀ w,Continuous (fun t => W (index t) (realTimeClamp (τ t)) w))
    (q : ℕ → K) (hq : DenseRange q)
    (I : Fin (n+1) → progressiveEnergyRange F c (P.prod (volume.restrict (Ioi 0))) →ₗᵢ[ℝ] Lp ℝ 2 P)
    (L : PiLp 2 (fun _ : Fin (n+1) => progressiveEnergyRange F c (P.prod (volume.restrict (Ioi 0)))) →ₗᵢ[ℝ] Lp ℝ 2 P)
    (hL : ∀ x,L x=∑ i,I i (x i))
    (hI : ∀ i,∀ H : progressiveEnergyIntegrands F c (P.prod (volume.restrict (Ioi 0))),
      ∃ M : ClosedTime T → Ω → ℝ,∃ hM : ContinuousM2Witness P F M,
        ItoCovarianceFormula P F (W i) H.val M ∧
        I i ⟨progressiveEnergyToLp F c _ H,LinearMap.mem_range_self _ H⟩=(hM.moment ⊤).toLp (M ⊤))
    (U : Lp ℝ 2 P)
    (hU : AEStronglyMeasurable[MeasurableSpace.comap
      (fun w t => W (index t) (realTimeClamp (τ t)) w) inferInstance] U P) :
    ∃! x,L x=U-(condExpL2 ℝ ℝ bot_le U : Lp ℝ 2 P) := by
  letI : CompleteSpace (progressiveEnergyRange F c (P.prod (volume.restrict (Ioi (0:ℝ))))) :=
    progressive_energy_complete F c _
  apply representation_extension_from_smooth_lemma P
    (fun t w => W (index t) (realTimeClamp (τ t)) w) hXm hXc q hq L ?_ U hU
  intro k f hf hfc hfd
  exact compact_observation_centered_isometry P hT F hF hle hnull W A hW hC hclock c hc hcm hcT hcc
    (fun i : Fin k => index (q i.val)) (fun i : Fin k => τ (q i.val))
    (fun i => hτ (q i.val)) (fun i => hτT (q i.val)) f (hfd.of_le (by norm_num)) hfc I L hL hI hf

end Asakura.Chapter5
