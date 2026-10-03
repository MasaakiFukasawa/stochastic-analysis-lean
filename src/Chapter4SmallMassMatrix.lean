import Chapter4LangevinRealRoots
import Chapter4SmallMassKernel
import Chapter4SmallMassInitial

open Matrix
open scoped Topology Matrix.Norms.Operator
namespace Asakura.Chapter4
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

lemma langevin_small_mass_companion (κ γ m : ℝ) (hγ : 0<γ) (hm : 0<m)
    (hD : 0<γ^2-4*κ*m) :
    langevinSlow κ γ m+langevinFast κ γ m= -γ/m ∧
    -langevinSlow κ γ m*langevinFast κ γ m= -κ/m ∧
    langevinSlow κ γ m≠langevinFast κ γ m := by
  rw [langevin_slow_rationalized κ γ m hγ hm hD.le]
  dsimp only [langevinFast]
  have hs := Real.sq_sqrt hD.le
  have hsp := Real.sqrt_pos.mpr hD
  constructor
  · ring
  constructor
  · field_simp
    nlinarith
  · intro he
    have hmne : m≠0 := ne_of_gt hm
    have hh := (div_left_inj' (mul_ne_zero (by norm_num) hmne)).mp he
    linarith

/-- The real matrix formula has precisely the initial term and noise
kernel used in the proved mass-zero convergence statement. -/
theorem langevin_small_mass_matrix_formula (κ γ σ m r y v : ℝ)
    (hγ : 0<γ) (hm : 0<m) (hD : 0<γ^2-4*κ*m) :
    let A : Matrix (Fin 2) (Fin 2) ℝ := !![0,1;-κ/m,-γ/m]
    NormedSpace.exp (r • A) 0 0*y+NormedSpace.exp (r • A) 0 1*v=langevinInitial κ γ m r y v ∧
    NormedSpace.exp (r • A) 0 1*(σ/m)=langevinKernel κ γ σ m r := by
  dsimp only
  obtain ⟨hs,hp,hne⟩ := langevin_small_mass_companion κ γ m hγ hm hD
  have he := companion_exp_real_first_row (langevinSlow κ γ m) (langevinFast κ γ m) r hne
  dsimp only at he
  rw [hp,hs] at he
  rw [he.1,he.2]
  constructor
  · rw [langevin_initial_unscaled κ γ m r y v (ne_of_gt hm)]
    ring
  · dsimp only [langevinKernel]
    have hg : langevinSlow κ γ m-langevinFast κ γ m≠0 := sub_ne_zero.mpr hne
    field_simp <;> ring

end Asakura.Chapter4
