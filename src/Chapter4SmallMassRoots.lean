import Chapter4LangevinRoots
import Mathlib.Topology.Algebra.Order.Field

open Filter
open scoped Topology
namespace Asakura.Chapter4
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

noncomputable def langevinSlow (κ γ m : ℝ) : ℝ := -2*κ/(γ+Real.sqrt (γ^2-4*κ*m))
noncomputable def langevinFast (κ γ m : ℝ) : ℝ := (-γ-Real.sqrt (γ^2-4*κ*m))/(2*m)

lemma langevin_slow_rationalized (κ γ m : ℝ) (hγ : 0<γ) (hm : 0<m)
    (hD : 0≤γ^2-4*κ*m) :
    langevinSlow κ γ m=(-γ+Real.sqrt (γ^2-4*κ*m))/(2*m) := by
  have hs := Real.sq_sqrt hD
  have hn : γ+Real.sqrt (γ^2-4*κ*m)≠0 := ne_of_gt (by positivity)
  dsimp only [langevinSlow]
  field_simp
  simp only [mul_comm 4 κ] at hs
  nlinarith

/-- The slow root, fast root, and scaled gap have exactly the limits
used in the mass-zero passage. -/
theorem langevin_mass_root_limits (κ γ : ℝ) (hγ : 0<γ) :
    Tendsto (langevinSlow κ γ) (𝓝[>] (0:ℝ)) (𝓝 (-κ/γ)) ∧
    Tendsto (langevinFast κ γ) (𝓝[>] (0:ℝ)) atBot ∧
    Tendsto (fun m => m*(langevinSlow κ γ m-langevinFast κ γ m))
      (𝓝[>] (0:ℝ)) (𝓝 γ) := by
  have hm0 : Tendsto (fun m : ℝ => m) (𝓝[>] (0:ℝ)) (𝓝 0) := tendsto_id.mono_right nhdsWithin_le_nhds
  have hs : Tendsto (fun m : ℝ => Real.sqrt (γ^2-4*κ*m)) (𝓝[>] (0:ℝ)) (𝓝 γ) := by
    have hD : Tendsto (fun m : ℝ => γ^2-4*κ*m) (𝓝[>] (0:ℝ)) (𝓝 (γ^2)) := by
      simpa only [mul_zero,sub_zero] using (tendsto_const_nhds (x := γ^2)).sub ((tendsto_const_nhds (x := 4*κ)).mul hm0)
    simpa only [Function.comp_def,Real.sqrt_sq hγ.le] using (Real.continuous_sqrt.tendsto (γ^2)).comp hD
  have ha : Tendsto (langevinSlow κ γ) (𝓝[>] (0:ℝ)) (𝓝 (-κ/γ)) := by
    have hh := (tendsto_const_nhds (x := -2*κ)).div (tendsto_const_nhds.add hs)
      (show γ+γ≠0 by linarith)
    change Tendsto (fun m => -2*κ/(γ+Real.sqrt (γ^2-4*κ*m))) _ _
    convert hh using 1 <;> field_simp <;> ring
  have hb0 : Tendsto (fun m : ℝ => (-γ-Real.sqrt (γ^2-4*κ*m))/2)
      (𝓝[>] (0:ℝ)) (𝓝 (-γ)) := by
    convert (tendsto_const_nhds.sub hs).div_const 2 using 1 <;> ring
  have hb : Tendsto (langevinFast κ γ) (𝓝[>] (0:ℝ)) atBot := by
    convert hb0.neg_mul_atTop (neg_neg_of_pos hγ) tendsto_inv_nhdsGT_zero using 1
    ext m
    dsimp only [langevinFast]
    ring
  refine ⟨ha,hb,?_⟩
  have hh := (hm0.mul ha).sub hb0
  have heq : (fun m : ℝ => m*langevinSlow κ γ m-(-γ-Real.sqrt (γ^2-4*κ*m))/2)
      =ᶠ[𝓝[>] (0:ℝ)] (fun m => m*(langevinSlow κ γ m-langevinFast κ γ m)) := by
    filter_upwards [self_mem_nhdsWithin] with m hm
    have hmne : m≠0 := ne_of_gt hm
    dsimp only [langevinFast]
    field_simp <;> ring
  simpa only [zero_mul,zero_sub,neg_neg] using hh.congr' heq

end Asakura.Chapter4
