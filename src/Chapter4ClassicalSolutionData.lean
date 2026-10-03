import Chapter4ConditionalFKCoefficients

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter5

/-- The exact regularity, growth, initial value and PDE assumptions in the
bounded classical-solution argument of the Markov section. -/
structure ClassicalForwardSolution {dim noise : ℕ}
    (μ : Fin dim → (Fin dim → ℝ) → ℝ)
    (σ : Fin dim → Fin noise → (Fin dim → ℝ) → ℝ)
    (f : (Fin dim → ℝ) → ℝ) where
  value : ℝ → (Fin dim → ℝ) → ℝ
  timeDerivative : ℝ × (Fin dim → ℝ) → ℝ
  space_smooth : ∀ a,0<a → ContDiff ℝ 2 (value a)
  time_derivative : ∀ a,0<a → ∀ x,HasDerivAt (fun s => value s x) (timeDerivative (a,x)) a
  continuous : ContinuousOn (fun z : ℝ × (Fin dim → ℝ) => value z.1 z.2) {z | 0≤z.1}
  time_continuous : ContinuousOn timeDerivative {z | 0<z.1}
  gradient_continuous : ContinuousOn (fun z : ℝ × (Fin dim → ℝ) => fderiv ℝ (value z.1) z.2) {z | 0<z.1}
  hessian_continuous : ContinuousOn (fun z : ℝ × (Fin dim → ℝ) => fderiv ℝ (fderiv ℝ (value z.1)) z.2) {z | 0<z.1}
  initial : ∀ x,value 0 x=f x
  bounded : ∀ t,0≤t → ∃ K : ℝ,∀ a∈Icc 0 t,∀ x,|value a x|≤K
  pde : ∀ a,0<a → ∀ x,timeDerivative (a,x)=
    (∑ i,fderiv ℝ (value a) x (Pi.single i 1)*μ i x)+
    (∑ i,∑ l,fderiv ℝ (fderiv ℝ (value a)) x (Pi.single i 1) (Pi.single l 1)*(∑ j,σ i j x*σ l j x))/2

/-- An actual vector SDE solution: its stochastic integrals and integral
equation are part of the data, rather than a prescribed transition law. -/
structure VectorSDESolution
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] {dim noise : ℕ}
    (F : ClosedTime T → MeasurableSpace Ω)
    (W : Fin noise → ClosedTime T → Ω → ℝ)
    (μ : Fin dim → (Fin dim → ℝ) → ℝ)
    (σ : Fin dim → Fin noise → (Fin dim → ℝ) → ℝ)
    (ξ : Ω → Fin dim → ℝ) (X : ClosedTime T → Ω → Fin dim → ℝ) : Prop where
  initial_adapted : Measurable[F ⊥] ξ
  adapted : ∀ t,t<⊤ → Measurable[F t] (X t)
  path : ∀ w t,t<⊤ → ContinuousAt (fun s => X s w) t
  integrals : ∃ N : Fin dim → Fin noise → ClosedTime T → Ω → ℝ,
    (∀ i j,LocalMProcessWitness P F (N i j)) ∧
    (∀ i j,ItoCovarianceFormula P F (W j) (fun z => σ i j (X (realTimeClamp z.2) z.1)) (N i j)) ∧
    ∀ᵐ w ∂P,∀ r : ℝ,0≤r → (r:EReal)<T → ∀ i,
      X (realTimeClamp r) w i=ξ w i+(∫ s in 0..r,μ i (X (realTimeClamp s) w))+∑ j,N i j (realTimeClamp r) w

theorem VectorSDESolution.initial_value
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T) {dim noise : ℕ}
    (F : ClosedTime T → MeasurableSpace Ω)
    (W : Fin noise → ClosedTime T → Ω → ℝ)
    (μ : Fin dim → (Fin dim → ℝ) → ℝ)
    (σ : Fin dim → Fin noise → (Fin dim → ℝ) → ℝ)
    (ξ : Ω → Fin dim → ℝ) (X : ClosedTime T → Ω → Fin dim → ℝ)
    (hX : VectorSDESolution P F W μ σ ξ X) : X ⊥=ᵐ[P] ξ := by
  obtain ⟨N,hN,_,he⟩ := hX.integrals
  have hzero : realTimeClamp (T := T) 0=⊥ := by
    apply Subtype.ext
    rw [real_time_clamp_eq 0 le_rfl hT.le]
    rfl
  filter_upwards [he,ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun j => (hN i j).initial P F))] with w hw hz
  ext i
  have hh := hw 0 le_rfl hT i
  simpa only [hzero,intervalIntegral.integral_same,add_zero,hz,Pi.zero_apply,Finset.sum_const_zero] using hh

end Asakura.Chapter4
