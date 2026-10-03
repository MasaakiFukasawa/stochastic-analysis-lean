import Chapter4SmallMassRoots

open Filter
open scoped Topology
namespace Asakura.Chapter4
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false

noncomputable def langevinInitial (κ γ m r y v : ℝ) : ℝ :=
  ((m*langevinSlow κ γ m*Real.exp (langevinFast κ γ m*r)-
      m*langevinFast κ γ m*Real.exp (langevinSlow κ γ m*r))*y+
    m*(Real.exp (langevinSlow κ γ m*r)-Real.exp (langevinFast κ γ m*r))*v)/
      (m*(langevinSlow κ γ m-langevinFast κ γ m))

theorem langevin_initial_limit (κ γ r y v : ℝ) (hγ : 0<γ) (hr : 0<r) :
    Tendsto (fun m => langevinInitial κ γ m r y v) (𝓝[>] (0:ℝ))
      (𝓝 (Real.exp (-κ/γ*r)*y)) := by
  obtain ⟨ha,hb,hgap⟩ := langevin_mass_root_limits κ γ hγ
  have hm0 : Tendsto (fun m : ℝ => m) (𝓝[>] (0:ℝ)) (𝓝 0) := tendsto_id.mono_right nhdsWithin_le_nhds
  have hma : Tendsto (fun m => m*langevinSlow κ γ m) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    simpa only [zero_mul] using hm0.mul ha
  have hmb : Tendsto (fun m => m*langevinFast κ γ m) (𝓝[>] (0:ℝ)) (𝓝 (-γ)) := by
    have hh := hma.sub hgap
    convert hh using 1 <;> (try funext m) <;> ring
  have hea := Real.continuous_exp.tendsto _ |>.comp (ha.mul_const r)
  have heb := Real.tendsto_exp_atBot.comp (hb.atBot_mul_pos hr tendsto_const_nhds)
  have hh := (((hma.mul heb).sub (hmb.mul hea)).mul_const y |>.add
    ((hm0.mul (hea.sub heb)).mul_const v)).div hgap (ne_of_gt hγ)
  change Tendsto (fun m => ((m*langevinSlow κ γ m*Real.exp (langevinFast κ γ m*r)-
      m*langevinFast κ γ m*Real.exp (langevinSlow κ γ m*r))*y+
    m*(Real.exp (langevinSlow κ γ m*r)-Real.exp (langevinFast κ γ m*r))*v)/
      (m*(langevinSlow κ γ m-langevinFast κ γ m))) _ _
  convert hh using 1 <;> (try funext m) <;> (try dsimp only [Function.comp_def,Pi.div_apply]) <;> field_simp <;> ring

  all_goals simp only [mul_inv_cancel₀ (ne_of_gt hγ),one_mul]

lemma langevin_initial_unscaled (κ γ m r y v : ℝ) (hm : m≠0) :
    langevinInitial κ γ m r y v=
      ((langevinSlow κ γ m*Real.exp (langevinFast κ γ m*r)-
        langevinFast κ γ m*Real.exp (langevinSlow κ γ m*r))*y+
        (Real.exp (langevinSlow κ γ m*r)-Real.exp (langevinFast κ γ m*r))*v)/
        (langevinSlow κ γ m-langevinFast κ γ m) := by
  dsimp only [langevinInitial]
  rw [show (m*langevinSlow κ γ m*Real.exp (langevinFast κ γ m*r)-
      m*langevinFast κ γ m*Real.exp (langevinSlow κ γ m*r))*y+
      m*(Real.exp (langevinSlow κ γ m*r)-Real.exp (langevinFast κ γ m*r))*v=
      m*((langevinSlow κ γ m*Real.exp (langevinFast κ γ m*r)-
        langevinFast κ γ m*Real.exp (langevinSlow κ γ m*r))*y+
        (Real.exp (langevinSlow κ γ m*r)-Real.exp (langevinFast κ γ m*r))*v) by ring]
  exact mul_div_mul_left _ _ hm

end Asakura.Chapter4
