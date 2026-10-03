import Chapter3WrittenLimits
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter4
set_option backward.isDefEq.respectTransparency false

/-- Cancellation of the finite-variation part of the discounted reverse-time
PDE solution. The generator and Ito formula themselves are prior obligations. -/
theorem fk_drift_cancellation (vt Lv k v g A : ℝ)
    (hpde : vt+k*v=Lv+g) : A*(-vt+Lv)-k*A*v = -A*g := by
  nlinarith [mul_eq_mul_left_iff.mpr (Or.inl hpde : vt+k*v=Lv+g ∨ A=0)]

/-- k≥0 makes the discount factor a contraction, which is exactly why the
polynomial growth assumption gives a stopping-independent dominator. -/
theorem fk_discount_bound (v K C : ℝ) (hK : 0 ≤ K) (hv : |v| ≤ C) :
    |v*Real.exp (-K)| ≤ C := by
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  have he : Real.exp (-K) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  exact (mul_le_of_le_one_right (abs_nonneg v) he).trans hv

/-- Taking the stopping times to the terminal time gives the printed terminal
payoff, using continuity at time zero rather than differentiability there. -/
theorem fk_terminal_limit {E : Type*} [TopologicalSpace E]
    (v : ℝ × E → ℝ) (X : ℝ → E) (K : ℝ → ℝ) (t : ℝ) (τ : ℕ → ℝ)
    (hv : ContinuousAt v (0,X t)) (hX : ContinuousAt X t) (hK : ContinuousAt K t)
    (hτ : Tendsto τ atTop (𝓝 t)) :
    Tendsto (fun n => v (t-τ n,X (τ n))*Real.exp (-K (τ n))) atTop
      (𝓝 (v (0,X t)*Real.exp (-K t))) := by
  have ht : Tendsto (fun n => t-τ n) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := t)).sub hτ
  exact (hv.tendsto.comp (ht.prodMk_nhds (hX.tendsto.comp hτ))).mul
    (Real.continuous_exp.continuousAt.tendsto.comp ((hK.tendsto.comp hτ).neg))

/-- The conditional FK proof's dominated-convergence step, carried out on
all events in G. No conditional identity of the limit is an assumption. -/
theorem conditional_limit_from_stopped_tests
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (G : MeasurableSpace Ω) (hG : G ≤ m)
    (U : ℕ → Ω → ℝ) (Y V B : Ω → ℝ)
    (hU : ∀ n, AEStronglyMeasurable[m] (U n) P)
    (hY : AEStronglyMeasurable[m] Y P) (hV : StronglyMeasurable[G] V)
    (hVi : Integrable V P) (hB : Integrable B P)
    (hb : ∀ n, ∀ᵐ ω ∂P, ‖U n ω‖ ≤ B ω)
    (hconv : ∀ᵐ ω ∂P, Tendsto (fun n => U n ω) atTop (𝓝 (Y ω)))
    (he : ∀ n A, MeasurableSet[G] A → (∫ ω in A, U n ω ∂P) = ∫ ω in A, V ω ∂P) :
    P[Y | G] =ᵐ[P] V := by
  have hbound : ∀ᵐ ω ∂P, ‖Y ω‖ ≤ B ω := by
    filter_upwards [hconv,ae_all_iff.2 hb] with ω hω hbω
    exact le_of_tendsto hω.norm (Eventually.of_forall hbω)
  have hYi : Integrable Y P := hB.mono' hY hbound
  apply Filter.EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hG hYi
    (fun _ _ _ => hVi.integrableOn) _ hV.aestronglyMeasurable
  intro A hA _
  have hlim := tendsto_integral_of_dominated_convergence (μ := P.restrict A) B
    (fun n => (hU n).restrict) hB.integrableOn
    (fun n => ae_restrict_of_ae (hb n)) (ae_restrict_of_ae hconv)
  have heq : (fun n => ∫ ω in A, U n ω ∂P) = fun _ => ∫ ω in A, V ω ∂P :=
    funext (fun n => he n A hA)
  rw [heq] at hlim
  exact tendsto_nhds_unique tendsto_const_nhds hlim

end Asakura.Chapter4
