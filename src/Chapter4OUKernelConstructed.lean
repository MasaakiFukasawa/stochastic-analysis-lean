import Chapter4DeterministicItoLaw
import Chapter4OUVariance
import Chapter4OUConstructed

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter5
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- The OU example's actual Ito solution has the stated transition law.
Together with ou_kernel_composition this verifies the OU exercise without
assuming the law of a Wiener integral. -/
theorem ou_solution_and_transition_law
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (W A : ClosedTime T → Ω → ℝ) (hW : LocalMProcessWitness P F W)
    (hA : LocalCovarianceWitness P F W W A)
    (hclock : ∀ w (r : ℝ),0≤r → (r:EReal)<T → A (realTimeClamp r) w=r)
    (κ σ x : ℝ) (hκ : 0<κ) :
    ∃ N : ClosedTime T → Ω → ℝ,LocalMProcessWitness P F N ∧
      ItoCovarianceFormula P F W (fun z => σ*Real.exp (κ*z.2)) N ∧
      (∀ᵐ w ∂P,∀ (R : ℝ),0≤R → (R:EReal)<T →
        Real.exp (-κ*R)*(x+N (realTimeClamp R) w)=x-
          κ*(∫ r in 0..R,Real.exp (-κ*r)*(x+N (realTimeClamp r) w))+σ*W (realTimeClamp R) w) ∧
      ∀ (R : ℝ) (hR : 0≤R),(R:EReal)<T →
        HasLaw (fun w => Real.exp (-κ*R)*(x+N (realTimeClamp R) w)) (ouKernel κ σ hκ ⟨R,hR⟩ x) P := by
  obtain ⟨N,hN,hNI,he⟩ := ou_sde_constructed P hT F hF hle hnull W A hW hA hclock x (-κ) σ
  have hNI' : ItoCovarianceFormula P F W (fun z => σ*Real.exp (κ*z.2)) N := by
    simpa only [neg_neg] using hNI
  refine ⟨N,hN,hNI',?_,?_⟩
  · filter_upwards [he] with w hw
    intro R hR hRT
    simpa only [neg_mul,sub_eq_add_neg] using hw R hR hRT
  intro R hR hRT
  have hl := deterministic_brownian_integral_law P hT F hF hle hnull W A N hW hA hN hclock
    (fun r => σ*Real.exp (κ*r)) (by fun_prop) hNI' R hR hRT
  have hl' : HasLaw (N (realTimeClamp R)) (gaussianReal 0 (NNReal.mk
      (∫ r in 0..R,(σ*Real.exp (κ*r))^2) (intervalIntegral.integral_nonneg_of_forall hR (fun _ => sq_nonneg _)))) P := hl
  have hh := gaussianReal_const_mul hl' (Real.exp (-κ*R))
  have hv : (NNReal.mk (Real.exp (-κ*R)^2) (sq_nonneg _))*
      (NNReal.mk (∫ r in 0..R,(σ*Real.exp (κ*r))^2) (intervalIntegral.integral_nonneg_of_forall hR (fun _ => sq_nonneg _)))=
        ouVariance κ σ hκ ⟨R,hR⟩ := by
    apply NNReal.eq
    change Real.exp (-κ*R)^2*(∫ r in 0..R,(σ*Real.exp (κ*r))^2)=σ^2*(1-Real.exp (-2*κ*R))/(2*κ)
    exact ou_scaled_integral_variance κ σ R hκ
  rw [mul_zero,hv] at hh
  have hsol := ou_explicit_solution_law P κ σ x hκ ⟨R,hR⟩ _ hh
  apply hsol.congr
  apply ae_of_all
  intro w
  change Real.exp (-κ*R)*(x+N (realTimeClamp R) w)=Real.exp (-κ*R)*x+Real.exp (-κ*R)*N (realTimeClamp R) w
  ring

end Asakura.Chapter4
