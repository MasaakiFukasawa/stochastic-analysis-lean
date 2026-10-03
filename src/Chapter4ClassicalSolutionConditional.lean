import Chapter4ClassicalSolutionData

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter5
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

theorem classical_solution_conditional
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T) {dim noise : ℕ}
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (W : Fin noise → ClosedTime T → Ω → ℝ)
    (B : Fin noise → Fin noise → ClosedTime T → Ω → ℝ)
    (hW : ∀ j,LocalMProcessWitness P F (W j))
    (hB : ∀ j k,LocalCovarianceWitness P F (W j) (W k) (B j k))
    (hclock : ∀ j k w (r : ℝ),0≤r → (r:EReal)<T → B j k (realTimeClamp r) w=if j=k then r else 0)
    (μ : Fin dim → (Fin dim → ℝ) → ℝ)
    (σ : Fin dim → Fin noise → (Fin dim → ℝ) → ℝ)
    (hμ : ∀ i,Continuous (μ i)) (hσ : ∀ i j,Continuous (σ i j))
    (ξ : Ω → Fin dim → ℝ) (X : ClosedTime T → Ω → Fin dim → ℝ)
    (hX : VectorSDESolution P F W μ σ ξ X)
    (f : (Fin dim → ℝ) → ℝ) (v : ClassicalForwardSolution μ σ f)
    (s t : ℝ) (htT : (t:EReal)<T) (hs : s∈Icc 0 t) :
    P[(fun w => f (X (realTimeClamp t) w)) | F (realTimeClamp s)]=ᵐ[P]
      fun w => v.value (t-s) (X (realTimeClamp s) w) := by
  obtain ⟨N,hN,hNI,he⟩ := hX.integrals
  obtain ⟨K,hK⟩ := v.bounded t (hs.1.trans hs.2)
  have hh := conditional_feynman_kac_coefficients P hT F hF hle hnull W B hW hB hclock X ξ
    hX.initial_adapted hX.adapted hX.path μ σ hμ hσ N hN hNI t (hs.1.trans hs.2) htT
    (he.mono fun w hw r hr => hw r hr.1 ((EReal.coe_le_coe hr.2).trans_lt htT))
    v.value v.timeDerivative v.space_smooth v.time_derivative v.continuous v.time_continuous
    v.gradient_continuous v.hessian_continuous v.pde K hK s hs
  simpa only [v.initial] using hh

/-- The same constructed formula at a deterministic initial state gives
the transition expectation for every classical test solution. -/
theorem classical_solution_transition_expectation
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T) {dim noise : ℕ}
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (W : Fin noise → ClosedTime T → Ω → ℝ)
    (B : Fin noise → Fin noise → ClosedTime T → Ω → ℝ)
    (hW : ∀ j,LocalMProcessWitness P F (W j))
    (hB : ∀ j k,LocalCovarianceWitness P F (W j) (W k) (B j k))
    (hclock : ∀ j k w (r : ℝ),0≤r → (r:EReal)<T → B j k (realTimeClamp r) w=if j=k then r else 0)
    (μ : Fin dim → (Fin dim → ℝ) → ℝ)
    (σ : Fin dim → Fin noise → (Fin dim → ℝ) → ℝ)
    (hμ : ∀ i,Continuous (μ i)) (hσ : ∀ i j,Continuous (σ i j))
    (x : Fin dim → ℝ) (X : ClosedTime T → Ω → Fin dim → ℝ)
    (hX : VectorSDESolution P F W μ σ (fun _ => x) X)
    (f : (Fin dim → ℝ) → ℝ) (v : ClassicalForwardSolution μ σ f)
    (t : ℝ) (ht : 0≤t) (htT : (t:EReal)<T) :
    v.value t x=∫ w,f (X (realTimeClamp t) w) ∂P := by
  have hh := classical_solution_conditional P hT F hF hle hnull W B hW hB hclock μ σ hμ hσ
    (fun _ => x) X hX f v 0 t htT ⟨le_rfl,ht⟩
  have hzero : realTimeClamp (T := T) 0=⊥ := by
    apply Subtype.ext
    rw [real_time_clamp_eq 0 le_rfl hT.le]
    rfl
  simp only [hzero,sub_zero] at hh
  exact transition_value_of_conditional_formula P (F ⊥) (hle ⊥) _ (X ⊥) x (v.value t)
    (hX.initial_value P hT F W μ σ (fun _ => x) X) hh

end Asakura.Chapter4
