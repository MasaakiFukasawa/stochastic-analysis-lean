import Chapter4EulerPathMoment
import Chapter4EulerStepGrowth
import Chapter4FiniteStepDomain
import Chapter4VectorRunningUniformMoment

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter5
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false

/-- The actual Euler interpolation has a second-moment bound whose constant
contains the terminal time but not the number of subdivisions. -/
theorem euler_interpolation_uniform_second_moment
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T) {dim noise : ℕ}
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (W A : Fin noise → ClosedTime T → Ω → ℝ)
    (hW : ∀ j,LocalMProcessWitness P F (W j))
    (hA : ∀ j,LocalCovarianceWitness P F (W j) (W j) (A j))
    (hclock : ∀ j w (r : ℝ),0≤r → (r:EReal)<T → A j (realTimeClamp r) w=r)
    (μ : Fin dim → (Fin dim → ℝ) → ℝ) (σ : Fin dim → Fin noise → (Fin dim → ℝ) → ℝ)
    (L : ℝ) (hL : 0≤L)
    (hμ : ∀ i x y,(μ i x-μ i y)^2≤L*‖x-y‖^2)
    (hσ : ∀ i j x y,(σ i j x-σ i j y)^2≤L*‖x-y‖^2)
    (ξ : Ω → Fin dim → ℝ) (hξa : Measurable[F ⊥] ξ) (hξ : MemLp ξ 2 P)
    (h : ℝ) (hh : 0≤h)
    (n : ℕ) (hnT : (((n:ℝ)*h : ℝ):EReal)<T)
    (K : ℝ) (hK : 0≤K)
    (hμg : ∀ i x,(μ i x)^2≤K*(1+‖x‖^2))
    (hσg : ∀ i j x,(σ i j x)^2≤K*(1+‖x‖^2)) :
    ∃ V : Ω → C(Icc (0:ℝ) ((n:ℝ)*h),Fin dim → ℝ),
      Measurable[m] V ∧ MemLp V 2 P ∧
      (∀ r,Measurable[F (realTimeClamp r.val)] (fun w => V w r)) ∧
      (∀ w r,V w r=eulerInterpolation μ σ (fun j r => W j (realTimeClamp r)) ξ h n r.val w) ∧
      let R := (n:ℝ)*h
      let α := (dim:ℝ)*3
      let δ := (noise:ℝ)*noise
      let rate := vectorMomentGrowthRate R 2 K α dim δ
      (∫ w,‖V w‖^2 ∂P)≤(α*(∑ i,∫ w,(ξ w i)^2 ∂P)+rate*R)*Real.exp ((rate+1)*R) := by
  classical
  obtain ⟨V,hVm,hVi,hVa,hV⟩ := euler_interpolation_path_memLp P hT F hF hle hnull W A hW hA hclock
    μ σ L hL hμ hσ ξ hξa hξ h hh n hnT
  refine ⟨V,hVm,hVi,hVa,hV,?_⟩
  let R := (n:ℝ)*h
  have hR : 0≤R := by dsimp only [R];positivity
  let Wr := fun j r => W j (realTimeClamp r)
  let Y := eulerGrid μ σ Wr ξ h
  let U := fun i (z : Ω × ℝ) => ∑ k∈Finset.range n,
    (Ioc ((k:ℝ)*h) (((k:ℝ)+1)*h)).indicator (fun _ => μ i (Y k z.1)) z.2
  let G := fun i j (z : Ω × ℝ) => ∑ k∈Finset.range n,
    (Ioc ((k:ℝ)*h) (((k:ℝ)+1)*h)).indicator (fun _ => σ i j (Y k z.1)) z.2
  have hY := euler_grid_adapted_memLp P hT F hF hle hnull W A hW hA hclock μ σ L hL hμ hσ ξ hξa hξ h hh
  have hkT k (hk : k∈Finset.range n) : (((k:ℝ)*h : ℝ):EReal)<T := by
    apply lt_of_le_of_lt _ hnT
    apply EReal.coe_le_coe
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast (Finset.mem_range.mp hk).le) hh
  have hUa i := finite_step_integrand_domain F hF hle (Finset.range n)
    (fun k => (k:ℝ)*h) (fun k => ((k:ℝ)+1)*h) (fun k w => μ i (Y k w))
    (fun k hk => (Vector.coordinate_continuous_of_square_lipschitz (μ i) L hL (hμ i)).measurable.comp (hY k (hkT k hk)).1)
  have hGa i j := finite_step_integrand_domain F hF hle (Finset.range n)
    (fun k => (k:ℝ)*h) (fun k => ((k:ℝ)+1)*h) (fun k w => σ i j (Y k w))
    (fun k hk => (Vector.coordinate_continuous_of_square_lipschitz (σ i j) L hL (hσ i j)).measurable.comp (hY k (hkT k hk)).1)
  obtain ⟨N,hN2,hN,hNI,hEq⟩ := euler_interpolation_ito_equation P hT F hF hle hnull W A hW hA hclock
    μ σ L hL hμ hσ ξ hξa hξ h hh n hnT
  obtain ⟨c,hc,hcm,hcT,hct,hcut,hcc⟩ := positive_real_time_exhaustion hT
  have hUg : ∀ i w r,r∈Icc 0 R → |U i (w,r)|^(2:ℝ)≤K*(1+‖prefixPath hR (normEnvelope (V w)) r‖^(2:ℝ)) := by
    intro i w r hr
    simpa only [Real.rpow_two,sq_abs] using
      euler_step_coefficient_growth μ σ Wr ξ h hh n V hV (μ i) K hK (hμg i) w r hr
  have hGg : ∀ i j w r,r∈Icc 0 R → |G i j (w,r)|^(2:ℝ)≤K*(1+‖prefixPath hR (normEnvelope (V w)) r‖^(2:ℝ)) := by
    intro i j w r hr
    simpa only [Real.rpow_two,sq_abs] using
      euler_step_coefficient_growth μ σ Wr ξ h hh n V hV (σ i j) K hK (hσg i j) w r hr
  have hrep : ∀ᵐ w ∂P,∀ r i,V w r i=ξ w i+(∫ s in 0..r.val,U i (w,s))+∑ j,N i j (realTimeClamp r.val) w := by
    exact Filter.Eventually.of_forall (fun w r i => by rw [hV];exact hEq w r.val r.property.1 i)
  have hξm i : Measurable[m] (fun w => ξ w i) := (measurable_pi_apply i).comp (hξa.mono (hle ⊥) le_rfl)
  have hb := vector_integral_running_uniform_power_bound P hT F hF hle hnull W A N hW hA hN
    c hc hcm hcT hct hcut hcc
    (fun j k w r hr => hclock j w r hr.1 ((EReal.coe_le_coe hr.2).trans_lt (hcT k)))
    G (fun i j k => (hGa i j).2.1 (c k))
    (fun i j k => Filter.Eventually.of_forall (fun w => (hGa i j).2.2 w (c k) (hc k).le))
    hNI R hR hnT 2 (by norm_num) V hVm (by simpa using hVi)
    (fun i w => ξ w i) hξm (fun i => by simpa using (memLp_pi_iff.mp hξ i))
    U (fun i => (hUa i).1) (fun i j => (hGa i j).1) K hK hUg hGg hrep
  simpa only [Real.rpow_two,sq_abs,show (2:ℝ)-1=1 by norm_num,Real.rpow_one] using hb

end Asakura.Chapter4
