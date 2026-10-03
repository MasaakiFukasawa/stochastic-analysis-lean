import Chapter5ObservationRemovePast
import Chapter5BackwardGaussianGenerator

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

/-- One genuine Gaussian recursion step, including random past values,
actual Ito integrals, heat-equation cancellation and removal of past coordinates.
The second derivative bound is explicit, as it is not in the printed lemma. -/
theorem gaussian_observation_interval_representation
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t N,MeasurableSet[m] N → P N=0 → MeasurableSet[F t] N)
    {n k : ℕ} (W : Fin (n+1) → ClosedTime T → Ω → ℝ) (A : ClosedTime T → Ω → ℝ)
    (hW : ∀ i,LocalMProcessWitness P F (W i))
    (hC : ∀ i j,LocalCovarianceWitness P F (W i) (W j) (fun t w => if i=j then A t w else 0))
    (hclock : ∀ w (r : ℝ),0≤r → (r:EReal)<T → A (realTimeClamp r) w=r)
    (c : ℕ → ℝ) (hc : ∀ j,0≤c j) (hcm : Monotone c) (hcT : ∀ j,(c j:EReal)<T)
    (hcc : ∀ t,t<⊤ → ∃ j,t<realTimeClamp (T := T) (c j))
    (index : Fin k → Fin (n+1)) (active : Fin k → Prop) [DecidablePred active]
    (τ : Fin k → ℝ) (hτ : ∀ i,0≤τ i) (hτT : ∀ i,(τ i:EReal)<T)
    (a b S : ℝ) (ha : 0≤a) (hab : a≤b) (hbT : (b:EReal)<T) (hbS : b<S)
    (hpast : ∀ i,¬active i → τ i≤a) (hcurrent : ∀ i,active i → τ i=b)
    (f : (Fin k → ℝ) → ℝ) (D : (Fin k → ℝ) → (Fin k → ℝ) →L[ℝ] ℝ)
    (DD : (Fin k → ℝ) → (Fin k → ℝ) →L[ℝ] (Fin k → ℝ) →L[ℝ] ℝ)
    (hd : ∀ x,HasFDerivAt f (D x) x) (hdd : ∀ x,HasFDerivAt D (DD x) x)
    (hDc : Continuous D) (hDDc : Continuous DD)
    (C K : ℝ≥0) (hD : ∀ x,‖D x‖≤C) (hDD : ∀ x,‖DD x‖≤K) :
    let ν := (Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)).map (observationNoiseMap index active)
    let X : Fin k → ClosedTime T → Ω → ℝ := fun i t w => W (index i) (min (realTimeClamp (τ i)) t) w
    let clock := fun t (_ : Ω) => (finitePrefixTime (T := T) b (ha.trans hab) t).val
    let XX : Fin (k+1) → ClosedTime T → Ω → ℝ := Fin.cons clock X
    let M : Fin (k+1) → ClosedTime T → Ω → ℝ := Fin.cons (fun _ _ => (0:ℝ)) X
    ∃ g : ((Fin k → ℝ) × ℝ) → ℝ,ContDiff ℝ 2 g ∧
      (∀ p : (Fin k → ℝ) × ℝ,p.2≤b →
        g =ᶠ[𝓝 p] (fun q => ∫ z,f (q.1+Real.sqrt (S-q.2) • z) ∂ν)) ∧
      ∃ N : Fin (k+1) → ClosedTime T → Ω → ℝ,
        (∀ i,LocalMProcessWitness P F (N i)) ∧
        (∀ i,ItoCovarianceFormula P F (M i)
          (fun z => fderiv ℝ (fun x => g (spaceTimeCoordinates k x))
            (fun j => XX j (realTimeClamp z.2) z.1) (Pi.single i 1)) (N i)) ∧
        (fun w => ∫ z,f ((fun i => X i (realTimeClamp b) w)+Real.sqrt (S-b) • z) ∂ν) =ᵐ[P]
          fun w => (∫ z,f ((fun i => X i (realTimeClamp a) w)+Real.sqrt (S-a) • z) ∂ν)+
            ∑ j ∈ Finset.univ.filter active,(N j.succ (realTimeClamp b) w-N j.succ (realTimeClamp a) w) := by
  classical
  dsimp only
  let Q := observationNoiseMap index active
  let μ := Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)
  let ν := μ.map Q
  have hi : MemLp (fun z : Fin k → ℝ => z) 2 ν := linear_image_second_moment μ Q
    (Asakura.FullAudit.finite_gaussian_all_moments 2 (by norm_num))
  obtain ⟨g,hg,he⟩ := backward_heat_C2_extension ν hi f D DD hd hdd hDc hDDc C K hD hDD b S hbS
  have hz := backward_heat_extension_generator Q (fun t x => ∫ z,f (x+Real.sqrt t • z) ∂ν)
    g hg b S hbS he
    (fun x t ht => gaussian_subspace_heat_equation n Q f D DD hd hdd hDc hDDc C K hD hDD x t ht)
  obtain ⟨N,hN,hNI,hrep⟩ := stopped_observation_ito_increment P hT F hF hle hnull W A hW hC hclock
    c hc hcm hcT hcc index active τ hτ hτT a b ha hab hbT hpast hcurrent g hg hz
  have hremove := observation_integrals_remove_past P hT F hF hle hnull W hW index active τ hτ
    a b ha hab hbT hpast (fun x => g (spaceTimeCoordinates k x))
    (hg.comp (spaceTimeCoordinates k).contDiff) N hN hNI
  refine ⟨g,hg,he,N,hN,hNI,?_⟩
  filter_upwards [hrep,hremove] with w hw hr
  rw [(he _ le_rfl).eq_of_nhds,(he _ hab).eq_of_nhds,hr] at hw
  exact hw

end Asakura.Chapter5
