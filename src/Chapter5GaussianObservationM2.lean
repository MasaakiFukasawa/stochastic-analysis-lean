import Chapter5TerminalObservationRepresentation
import Chapter5CommonHeatGradientRegularity
import Chapter5IntervalM2Increment
import Chapter5BoundedIntervalEnergy
import Chapter2StochasticIntervalMembership

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 4800000
set_option backward.isDefEq.respectTransparency false

/-- The actual Gaussian observation step produces globally L² progressive
integrands and M² integrals, not merely local martingale increments. -/
theorem gaussian_observation_M2_representation
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
    (index : Fin k → Fin (n+1)) (active : Fin k → Prop) [DecidablePred active]
    (σ : Fin k → ℝ) (hσ : ∀ i,0≤σ i) (hσT : ∀ i,(σ i:EReal)<T)
    (a S : ℝ) (ha : 0≤a) (haS : a<S) (hST : (S:EReal)<T)
    (hpast : ∀ i,¬active i → σ i≤a) (hcurrent : ∀ i,active i → σ i=S)
    (f : (Fin k → ℝ) → ℝ) (D : (Fin k → ℝ) → (Fin k → ℝ) →L[ℝ] ℝ)
    (DD : (Fin k → ℝ) → (Fin k → ℝ) →L[ℝ] (Fin k → ℝ) →L[ℝ] ℝ)
    (hd : ∀ x,HasFDerivAt f (D x) x) (hdd : ∀ x,HasFDerivAt D (DD x) x)
    (hDc : Continuous D) (hDDc : Continuous DD)
    (C K : ℝ≥0) (hD : ∀ x,‖D x‖≤C) (hDD : ∀ x,‖DD x‖≤K) :
    let ν := (Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)).map (observationNoiseMap index active)
    let X : Fin k → ClosedTime T → Ω → ℝ := fun i t w => W (index i) (min (realTimeClamp (σ i)) t) w
    ∃ G : Fin k → Ω × ℝ → ℝ, ∃ Z : Fin k → ClosedTime T → Ω → ℝ,
      (∀ i,ContinuousM2Witness P F (Z i)) ∧
      (∀ i,ItoCovarianceFormula P F (W (index i)) (G i) (Z i)) ∧
      (∀ i,Measurable (G i) ∧ MemLp (G i) 2 (P.prod (volume.restrict (Ioi 0)))) ∧
      (∀ i (b : ℝ) (hb : 0≤b), (b:EReal)<T →
        @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) b => F (realTimeClamp t.val))) inferInstance
          (fun z : Ω × Icc (0:ℝ) b => G i (z.1,z.2.val))) ∧
      (∀ i,(∫ w,Z i ⊤ w ∂P)=0) ∧
      (fun w => f (fun i => W (index i) (realTimeClamp (σ i)) w)) =ᵐ[P]
        fun w => (∫ z,f ((fun i => X i (realTimeClamp a) w)+Real.sqrt (S-a) • z) ∂ν)+
          ∑ j ∈ Finset.univ.filter active,Z j ⊤ w := by
  classical
  dsimp only
  let ν := (Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)).map (observationNoiseMap index active)
  let X : Fin k → ClosedTime T → Ω → ℝ := fun i t w => W (index i) (min (realTimeClamp (σ i)) t) w
  let H : Fin k → Ω × ℝ → ℝ := fun i z => ∫ y,D ((fun j => X j (realTimeClamp z.2) z.1)+
    Real.sqrt (S-(finitePrefixTime (T := T) S (ha.trans haS.le) (realTimeClamp z.2)).val) • y) (Pi.single i 1) ∂ν
  have hi : Integrable (fun z : Fin k → ℝ => z) ν :=
    (linear_image_second_moment _ (observationNoiseMap index active)
      (Asakura.FullAudit.finite_gaussian_all_moments 2 (by norm_num))).integrable (by norm_num)
  obtain ⟨J,hJ,hJI,hbound,hrep⟩ := terminal_observation_representation P hT F hF hle hnull W A hW hC hclock
    c hc hcm hcT hcc index active σ hσ hσT a S ha haS hST hpast hcurrent
    f D DD hd hdd hDc hDDc C K hD hDD
  have hreg := common_heat_gradient_regularity P hT F hF hle hnull W hW index σ S (ha.trans haS.le)
    ν hi f D hd hDc C hD
  let G : Fin k → Ω × ℝ → ℝ := fun i z => (Ioc a S).indicator (fun r => H i (z.1,r)) z.2
  let Z : Fin k → ClosedTime T → Ω → ℝ := fun i t w => J i (min (realTimeClamp S) t) w-J i (min (realTimeClamp a) t) w
  have hA i : LocalCovarianceWitness P F (W (index i)) (W (index i)) A := by
    simpa only [ite_true] using hC (index i) (index i)
  have hz i := bounded_brownian_interval_M2 P hT F hF hle hnull (W (index i)) A (J i)
    (hW (index i)) (hA i) (hJ i) hclock (H i) (hreg.2 i).1 (hreg.2 i).2.1 (hreg.2 i).2.2
    (hJI i) a S C ha haS.le hST C.property (fun w r _ => hbound i (w,r))
  have he i := bounded_continuous_interval_energy P F hF hle (H i) a S C ha haS.le
    (fun r hr => (hreg.2 i).2.1 r hr.1 ((EReal.coe_le_coe hr.2).trans_lt hST))
    ((hreg.2 i).2.2 S (ha.trans haS.le) hST) (fun w r _ => hbound i (w,r))
  refine ⟨G,Z,(fun i => (hz i).1),(fun i => (hz i).2.1),he,?_,(fun i => (hz i).2.2),?_⟩
  · intro i b hb hbT
    have hstop (r : ℝ) : ∀ t,MeasurableSet[F t] {w : Ω | realTimeClamp (T := T) r≤t} := by
      intro t
      by_cases hh : realTimeClamp (T := T) r≤t <;> simp [hh]
    exact real_stochastic_interval_integrand_progressive F hF (fun _ => a) (fun _ => S)
      (fun _ => ha) (fun _ => ha.trans haS.le) (fun _ => (EReal.coe_le_coe haS.le).trans_lt hST)
      (fun _ => hST) (hstop a) (hstop S) b hb hbT (H i)
      (continuous_adapted_real_progressive F hF (H i) b hb
        (fun r hr => (hreg.2 i).2.1 r hr.1 ((EReal.coe_le_coe hr.2).trans_lt hbT))
        ((hreg.2 i).2.2 b hb hbT))
  · simpa only [Z,min_eq_left le_top] using hrep

end Asakura.Chapter5
