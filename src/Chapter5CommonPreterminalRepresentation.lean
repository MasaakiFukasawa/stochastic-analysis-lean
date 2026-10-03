import Chapter5CommonObservationIdentification

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 4800000
set_option backward.isDefEq.respectTransparency false

/-- All preterminal observation formulas use one constructed family of
integrals, so continuity can subsequently pass to the terminal time. -/
theorem common_preterminal_observation_representation
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
    let H := fun i (z : Ω × ℝ) => ∫ y,D ((fun j => X j (realTimeClamp z.2) z.1)+
      Real.sqrt (S-(finitePrefixTime (T := T) S (ha.trans haS.le) (realTimeClamp z.2)).val) • y) (Pi.single i 1) ∂ν
    ∃ J : Fin k → ClosedTime T → Ω → ℝ,
      (∀ i,LocalMProcessWitness P F (J i)) ∧
      (∀ i,ItoCovarianceFormula P F (W (index i)) (H i) (J i)) ∧
      (∀ i z,|H i z|≤C) ∧
      ∀ b∈Ico a S,
        (fun w => ∫ z,f ((fun i => X i (realTimeClamp b) w)+Real.sqrt (S-b) • z) ∂ν) =ᵐ[P]
          fun w => (∫ z,f ((fun i => X i (realTimeClamp a) w)+Real.sqrt (S-a) • z) ∂ν)+
            ∑ j ∈ Finset.univ.filter active,(J j (realTimeClamp b) w-J j (realTimeClamp a) w) := by
  classical
  dsimp only
  let Q := observationNoiseMap index active
  let μ := Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)
  let ν := μ.map Q
  have hi : Integrable (fun z : Fin k → ℝ => z) ν :=
    (linear_image_second_moment μ Q (Asakura.FullAudit.finite_gaussian_all_moments 2 (by norm_num))).integrable (by norm_num)
  have hS : 0≤S := ha.trans haS.le
  obtain ⟨hbound,hGm,J,hJ,hJI⟩ := common_heat_gradient_integrals P hT F hF hle hnull W hW index σ S hS
    ν hi f D hd hDc C hD
  refine ⟨J,hJ,hJI,hbound,?_⟩
  intro b hb
  have hb0 : 0≤b := ha.trans hb.1
  have hbT : (b:EReal)<T := (EReal.coe_le_coe hb.2.le).trans_lt hST
  let τ := fun i => if active i then b else σ i
  have hτ i : 0≤τ i := by
    dsimp only [τ]
    split_ifs
    · exact hb0
    · exact hσ i
  have hτT i : (τ i:EReal)<T := by dsimp only [τ]; split_ifs; exact hbT; exact hσT i
  have hτpast i (hi : ¬active i) : τ i≤a := by simpa only [τ,hi,ite_false] using hpast i hi
  have hτcurrent i (hi : active i) : τ i=b := by simp [τ,hi]
  have hσeq i : (if active i then S else τ i)=σ i := by
    by_cases hi : active i
    · simp [hi,hcurrent i hi]
    · simp [hi,τ]
  obtain ⟨g,hg,he,N,hN,hNI,hrep⟩ := gaussian_observation_interval_representation P hT F hF hle hnull W A hW hC hclock
    c hc hcm hcT hcc index active τ hτ hτT a b S ha hb.1 hbT hb.2 hτpast hτcurrent
    f D DD hd hdd hDc hDDc C K hD hDD
  have hident := common_observation_integral_identification P hT F hF hle hnull W hW index active τ
    b S hb0 hb.2.le hbT hτcurrent ν hi f D hd hDc C hD g hg (fun p hp => (he p hp).eq_of_nhds)
    J hJ N hN hNI
    (by simpa only [hσeq] using hJI)
    (by simpa only [hσeq] using hGm)
  have hvec r (hr : r≤b) w :
      (fun i => W (index i) (min (realTimeClamp (τ i)) (realTimeClamp r)) w)=
        (fun i => W (index i) (min (realTimeClamp (σ i)) (realTimeClamp r)) w) := by
    simpa only [hσeq] using observation_prefix_consistency W index active τ b S r hr hb.2.le hτcurrent w
  have hbt : realTimeClamp (T := T) b<⊤ := by
    change (realTimeClamp b:EReal)<T
    rw [real_time_clamp_eq b hb0 hbT.le]
    exact hbT
  have hat : realTimeClamp (T := T) a<⊤ := (real_time_clamp_mono hb.1).trans_lt hbt
  filter_upwards [hrep,hident] with w hw hid
  rw [hvec b le_rfl w,hvec a hb.1 w] at hw
  rw [hw]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hjA : active j := (Finset.mem_filter.mp hj).2
  rw [hid j hjA _ hbt,hid j hjA _ hat,min_self,min_eq_right (real_time_clamp_mono hb.1)]

end Asakura.Chapter5
