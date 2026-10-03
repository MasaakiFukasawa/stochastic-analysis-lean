import Chapter8NewtonHamiltonian
import Chapter8PhaseVolume
import Chapter8GibbsIntegrability
import Mathlib.MeasureTheory.Integral.Pi

open MeasureTheory
open scoped BigOperators
namespace Asakura.Chapter8
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem gaussian_coordinate_integrable (d : ℕ) (a : ℝ) (ha : 0<a) :
    Integrable (fun x : Fin d → ℝ => Real.exp (-a*∑ i,x i^2)) := by
  have hi := Integrable.fintype_prod (fun _ : Fin d => integrable_exp_neg_mul_sq ha)
  convert hi using 1
  funext x
  rw [← Real.exp_sum]
  congr 1
  simp only [Finset.mul_sum]

theorem gaussian_coordinate_second_moment (d : ℕ) (a : ℝ) (ha : 0<a) :
    Integrable (fun x : Fin d → ℝ => (1+∑ i,x i^2)*Real.exp (-a*∑ i,x i^2)) := by
  apply ((gaussian_coordinate_integrable d (a/2) (by positivity)).const_mul (1+2/a)).mono' (by fun_prop)
  apply ae_of_all
  intro x
  let r := ∑ i,x i^2
  have hr : 0≤r := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  change (1+r)*Real.exp (-a*r)≤(1+2/a)*Real.exp (-(a/2)*r)
  have he := Real.add_one_le_exp (a/2*r)
  have h1 : 1≤Real.exp (a/2*r) := Real.one_le_exp_iff.mpr (by positivity)
  have hq : r≤(2/a)*Real.exp (a/2*r) := by
    have hm : a*(2/a)=2 := mul_div_cancel₀ 2 ha.ne'
    nlinarith
  have hb : 1+r≤(1+2/a)*Real.exp (a/2*r) := by nlinarith
  have hh := mul_le_mul_of_nonneg_right hb (Real.exp_pos (-a*r)).le
  rw [mul_assoc,← Real.exp_add] at hh
  convert hh using 1 <;> congr 2 <;> ring

/-- The position second moment and the Gaussian velocity factor imply
the phase-space second moment required in the invariance argument. -/
theorem newton_hamiltonian_integrability {d : ℕ}
    (U : (Fin d → ℝ) → ℝ) (hU : Continuous U) (β m : ℝ) (hβ : 0<β) (hm : 0<m)
    (hi : Integrable (fun x : Fin d → ℝ => (1+∑ i,x i^2)*Real.exp (-β*U x))) :
    Integrable (fun z : Fin (d+d) → ℝ => (1+∑ i,z i^2)*Real.exp (-β*newtonHamiltonian U m z)) := by
  have hv := gaussian_coordinate_second_moment d (β*m/2) (by positivity)
  have hp := (phase_volume_preserving d).integrable_comp_of_integrable (hi.mul_prod hv)
  have hH : Continuous (newtonHamiltonian U m) := by
    unfold newtonHamiltonian
    exact (hU.comp (positionProjection d).continuous).add
      ((kineticBilinear d m).continuous.clm_apply continuous_id)
  apply hp.mono' (by fun_prop)
  apply ae_of_all
  intro z
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  change (1+∑ i,z i^2)*Real.exp (-β*newtonHamiltonian U m z)≤
    ((1+∑ i,(positionProjection d z i)^2)*Real.exp (-β*U (positionProjection d z)))*
      ((1+∑ i,(velocityProjection d z i)^2)*Real.exp (-(β*m/2)*∑ i,(velocityProjection d z i)^2))
  rw [phase_sum_squares,newton_hamiltonian_energy]
  have he : -β*(U (positionProjection d z)+(m/2)*∑ i,(velocityProjection d z i)^2)=
      -β*U (positionProjection d z)+(-(β*m/2)*∑ i,(velocityProjection d z i)^2) := by ring
  rw [he,Real.exp_add]
  have hq : 0≤∑ i,(positionProjection d z i)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hv : 0≤∑ i,(velocityProjection d z i)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hab := mul_nonneg hq hv
  have hw := mul_nonneg hab (mul_nonneg (Real.exp_pos (-β*U (positionProjection d z))).le
    (Real.exp_pos (-(β*m/2)*∑ i,(velocityProjection d z i)^2)).le)
  nlinarith

end Asakura.Chapter8
