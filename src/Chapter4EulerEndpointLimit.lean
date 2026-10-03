import Chapter4SDEEndpointMoment
import Chapter4BrownianSystem
import Chapter4EulerNoiseMap

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 3400000
set_option backward.isDefEq.respectTransparency false

theorem euler_endpoint_L2_limit
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P] {dim noise : ℕ}
    (B : BrownianSystem P noise)
    (L : ℝ) (hL : 0≤L)
    (μ : Fin dim → (Fin dim → ℝ) → ℝ) (σ : Fin dim → Fin noise → (Fin dim → ℝ) → ℝ)
    (hLip : ∀ x y,(∑ i,(μ i x-μ i y)^2)+(∑ i,∑ j,(σ i j x-σ i j y)^2)≤L*∑ i,(x i-y i)^2)
    (ξ : Ω → Fin dim → ℝ) (hξ : MemLp ξ 2 P)
    (X : HalfClosedTime → Ω → Fin dim → ℝ) (hX : VectorSDESolution P B.F B.W μ σ ξ X)
    (R : ℝ) (hR : 0≤R) :
    let Y := fun n : ℕ => eulerGrid μ σ (fun j r => B.W j (realTimeClamp r)) ξ (R/((n:ℝ)+1)) (n+1)
    (∀ n,Measurable[m] (Y n) ∧ MemLp (Y n) 2 P) ∧
    Measurable[m] (X (realTimeClamp R)) ∧ MemLp (X (realTimeClamp R)) 2 P ∧
    Tendsto (fun n => ∫ w,‖Y n w-X (realTimeClamp R) w‖^2 ∂P) atTop (𝓝 0) := by
  letI : MeasurableSpace Ω := m
  dsimp only
  let Y := fun n : ℕ => eulerGrid μ σ (fun j r => B.W j (realTimeClamp r)) ξ (R/((n:ℝ)+1)) (n+1)
  let V₀ := Vector.realVectorPath X hX.path R (EReal.coe_lt_top R)
  have hclock j w (r : ℝ) hr (_ : (r:EReal)<⊤) := B.diagonal_clock j w r hr
  obtain ⟨hm₀,hi₀,hXi⟩ := sde_finite_path_memLp P (EReal.coe_lt_top 0) rfl B.F B.mono B.le B.null
    B.W (fun j => B.C j j) B.martingale (fun j => B.cov j j) hclock L hL μ σ hLip ξ hξ X hX R hR (EReal.coe_lt_top R)
  obtain ⟨C,hC,hall⟩ := euler_strong_rate_manuscript P (EReal.coe_lt_top 0) rfl B.F B.mono B.le B.null
    B.W (fun j => B.C j j) B.martingale (fun j => B.cov j j) hclock L hL μ σ hLip R hR (EReal.coe_lt_top R)
  have hstep (n : ℕ) : Measurable[m] (Y n) ∧ MemLp (Y n) 2 P ∧
      (∫ w,‖Y n w-X (realTimeClamp R) w‖^2 ∂P)≤C*(1+∫ w,‖ξ w‖^2 ∂P)/((n:ℝ)+1) := by
    obtain ⟨V,hVm,hVi,_,hV,hb,_⟩ := hall ξ hX.initial_adapted hξ X hX (n+1) (Nat.succ_pos n)
    let rR : Icc (0:ℝ) R := ⟨R,right_mem_Icc.mpr hR⟩
    have hmul : ((n:ℝ)+1)*(R/((n:ℝ)+1))=R := by field_simp
    have hh : 0≤R/((n:ℝ)+1) := div_nonneg hR (by positivity)
    have hv : (fun w => V w rR)=Y n := by
      funext w
      rw [hV w rR]
      change eulerInterpolation μ σ _ ξ (R/((n+1:ℕ):ℝ)) (n+1) R w=Y n w
      simp only [Nat.cast_add,Nat.cast_one]
      have hg := congrFun (euler_interpolation_grid μ σ
        (fun j r => B.W j (realTimeClamp r)) ξ (R/((n:ℝ)+1)) hh (n+1)) w
      simpa only [Nat.cast_add,Nat.cast_one,hmul,Y] using hg
    have hYm : Measurable[m] (Y n) := by rw [← hv];exact (continuous_eval_const rR).measurable.comp hVm
    have hYi : MemLp (Y n) 2 P := by rw [← hv];exact random_path_evaluation_memLp P V hVm hVi rR
    refine ⟨hYm,hYi,?_⟩
    have hp := random_path_evaluation_square_moment P (fun w => V₀ w-V w) (hm₀.sub hVm) (hi₀.sub hVi) rR
    have hpoint w : (V₀ w-V w) rR=X (realTimeClamp R) w-Y n w := by
      change X (realTimeClamp R) w-V w rR=_
      rw [congrFun hv w]
    have hnorm w : ‖X (realTimeClamp R) w-Y n w‖=‖Y n w-X (realTimeClamp R) w‖ := norm_sub_rev _ _
    simp only [hpoint,hnorm] at hp
    exact hp.trans (by simpa only [Nat.cast_add,Nat.cast_one,V₀] using hb)
  refine ⟨fun n => ⟨(hstep n).1,(hstep n).2.1⟩,
    (hX.adapted _ (real_time_below R hR (EReal.coe_lt_top R))).mono (B.le _) le_rfl,hXi,?_⟩
  apply squeeze_zero (fun n => integral_nonneg (fun w => sq_nonneg _)) (fun n => (hstep n).2.2)
  have hh := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).const_mul (C*(1+∫ w,‖ξ w‖^2 ∂P))
  simpa only [mul_zero,mul_one_div] using hh

end Asakura.Chapter4
