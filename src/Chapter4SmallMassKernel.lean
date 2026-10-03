import Chapter4SmallMassRoots
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open MeasureTheory Filter Set
open scoped Topology
namespace Asakura.Chapter4
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

noncomputable def langevinKernel (κ γ σ m r : ℝ) : ℝ :=
  σ*(Real.exp (langevinSlow κ γ m*r)-Real.exp (langevinFast κ γ m*r))/
    (m*(langevinSlow κ γ m-langevinFast κ γ m))

lemma langevin_kernel_limit (κ γ σ r : ℝ) (hγ : 0<γ) (hr : 0<r) :
    Tendsto (fun m => langevinKernel κ γ σ m r) (𝓝[>] (0:ℝ))
      (𝓝 (σ/γ*Real.exp (-κ/γ*r))) := by
  obtain ⟨ha,hb,hgap⟩ := langevin_mass_root_limits κ γ hγ
  have hea := Real.continuous_exp.tendsto _ |>.comp (ha.mul_const r)
  have heb := Real.tendsto_exp_atBot.comp (hb.atBot_mul_pos hr tendsto_const_nhds)
  have hh := ((tendsto_const_nhds (x:=σ)).mul (hea.sub heb)).div hgap (ne_of_gt hγ)
  change Tendsto (fun m => σ*(Real.exp (langevinSlow κ γ m*r)-Real.exp (langevinFast κ γ m*r))/(m*(langevinSlow κ γ m-langevinFast κ γ m))) _ _
  convert hh using 1 <;> (try funext m) <;> (try dsimp only [Function.comp_def,Pi.div_apply]) <;> ring

lemma langevin_kernel_bound (κ γ σ m r : ℝ) (hκ : 0<κ) (hγ : 0<γ) (hm : 0<m)
    (hr : 0≤r) (hgap : γ/2≤m*(langevinSlow κ γ m-langevinFast κ γ m)) :
    |langevinKernel κ γ σ m r|≤4*|σ|/γ := by
  have ha : langevinSlow κ γ m≤0 := by
    dsimp only [langevinSlow]
    exact div_nonpos_of_nonpos_of_nonneg (by nlinarith) (by positivity)
  have hb : langevinFast κ γ m≤0 := by
    dsimp only [langevinFast]
    exact div_nonpos_of_nonpos_of_nonneg (by have := Real.sqrt_nonneg (γ^2-4*κ*m);linarith) (by positivity)
  have hea : Real.exp (langevinSlow κ γ m*r)≤1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg ha hr)
  have heb : Real.exp (langevinFast κ γ m*r)≤1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg hb hr)
  have hg : 0<m*(langevinSlow κ γ m-langevinFast κ γ m) := lt_of_lt_of_le (by linarith) hgap
  have hdiff : |Real.exp (langevinSlow κ γ m*r)-Real.exp (langevinFast κ γ m*r)|≤2 := by
    rw [abs_le]
    constructor <;> linarith [Real.exp_pos (langevinSlow κ γ m*r),Real.exp_pos (langevinFast κ γ m*r)]
  dsimp only [langevinKernel]
  rw [abs_div,abs_mul,abs_of_pos hg]
  apply (div_le_div_iff₀ hg hγ).mpr
  have hh := mul_le_mul_of_nonneg_left hdiff (abs_nonneg σ)
  have hh' := mul_le_mul_of_nonneg_left hgap (by positivity : 0≤4*|σ|)
  nlinarith

/-- Squared convergence of the Brownian convolution kernels on each
finite time interval; the possible discrepancy at r=0 is null. -/
theorem langevin_kernel_L2_limit (κ γ σ R : ℝ) (hκ : 0<κ) (hγ : 0<γ) (hR : 0≤R) :
    Tendsto (fun m => ∫ r in 0..R,
      (langevinKernel κ γ σ m r-σ/γ*Real.exp (-κ/γ*r))^2)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
  let μ := volume.restrict (Ioc 0 R)
  have hgap : ∀ᶠ m in 𝓝[>] (0:ℝ),γ/2≤m*(langevinSlow κ γ m-langevinFast κ γ m) :=
    (langevin_mass_root_limits κ γ hγ).2.2.eventually (eventually_ge_nhds (by linarith))
  have hbound : ∀ᶠ m in 𝓝[>] (0:ℝ),∀ᵐ r ∂μ,
      ‖(langevinKernel κ γ σ m r-σ/γ*Real.exp (-κ/γ*r))^2‖≤(5*|σ|/γ)^2 := by
    filter_upwards [hgap,self_mem_nhdsWithin] with m hg hm
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have hK := langevin_kernel_bound κ γ σ m r hκ hγ hm hr.1.le hg
    have he : |σ/γ*Real.exp (-κ/γ*r)|≤|σ|/γ := by
      rw [abs_mul,abs_div,abs_of_pos hγ,abs_of_pos (Real.exp_pos _)]
      exact mul_le_of_le_one_right (by positivity) (Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hκ.le) hγ.le) hr.1.le))
    have hh := (abs_sub _ _).trans (add_le_add hK he)
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    have hsum : 4*|σ|/γ+|σ|/γ=5*|σ|/γ := by ring
    rw [hsum] at hh
    nlinarith [sq_abs (langevinKernel κ γ σ m r-σ/γ*Real.exp (-κ/γ*r)),abs_nonneg (langevinKernel κ γ σ m r-σ/γ*Real.exp (-κ/γ*r))]
  have hmeas : ∀ m : ℝ,AEStronglyMeasurable
      (fun r => (langevinKernel κ γ σ m r-σ/γ*Real.exp (-κ/γ*r))^2) μ := by
    intro m
    apply Continuous.aestronglyMeasurable
    dsimp only [langevinKernel]
    fun_prop
  have hlim : ∀ᵐ r ∂μ,Tendsto
      (fun m => (langevinKernel κ γ σ m r-σ/γ*Real.exp (-κ/γ*r))^2)
      (𝓝[>] (0:ℝ)) (𝓝 (0:ℝ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    simpa only [sub_self,zero_pow (by norm_num : (2:ℕ)≠0)] using
      ((langevin_kernel_limit κ γ σ r hγ hr.1).sub (tendsto_const_nhds (x:=σ/γ*Real.exp (-κ/γ*r)))).pow 2
  have hh := tendsto_integral_filter_of_dominated_convergence (μ:=μ) (fun _ => (5*|σ|/γ)^2)
    (Eventually.of_forall hmeas) hbound (integrable_const _) hlim
  simpa only [intervalIntegral.integral_of_le hR,integral_zero] using hh

end Asakura.Chapter4
