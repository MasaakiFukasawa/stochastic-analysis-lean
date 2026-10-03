import Chapter9DirectionalJets

open Set Filter
open scoped Topology ContDiff
namespace Asakura.Chapter11
open Asakura.Chapter9
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
attribute [-instance] ContinuousMultilinearMap.seminormedAddCommGroup ContinuousMultilinearMap.seminormedAddCommGroup'

theorem scalar_space_slice_derivative (F : ℝ × ℝ → ℝ) (t y : ℝ)
    (hF : ContDiffAt ℝ ∞ F (t,y)) :
    HasDerivAt (fun a => F (t,a)) (iteratedFDeriv ℝ 1 F (t,y) (fun _ => (0,1))) y := by
  have h := (hF.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt y
    ((hasDerivAt_const y t).prodMk (hasDerivAt_id y))
  simpa only [Function.comp_def,iteratedFDeriv_one_apply] using! h

theorem scalar_time_slice_derivative (F : ℝ × ℝ → ℝ) (t y : ℝ)
    (hF : ContDiffAt ℝ ∞ F (t,y)) :
    HasDerivAt (fun a => F (a,y)) (iteratedFDeriv ℝ 1 F (t,y) (fun _ => (1,0))) t := by
  have h := (hF.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t y))
  simpa only [Function.comp_def,iteratedFDeriv_one_apply] using! h

theorem scalar_space_second_jet (F : ℝ × ℝ → ℝ) (t y : ℝ)
    (hF : ∀ a,ContDiffAt ℝ ∞ F (t,a)) :
    iteratedFDeriv ℝ 2 F (t,y) (fun _ => (0,1))=deriv (deriv (fun a => F (t,a))) y := by
  have hd := second_jet_line F (t,y) (0,1) (hF y)
  have he (r : ℝ) : (t,y)+r • (0,1)=(t,y+r) := by ext <;> simp
  simp_rw [he,←(scalar_space_slice_derivative F t _ (hF _)).deriv] at hd
  have hh := hd.comp_of_eq y ((hasDerivAt_id y).sub_const y) (by simp)
  have hfun : (fun a => deriv (fun z => F (t,z)) (y+(a-y)))=deriv (fun z => F (t,z)) := by
    funext a
    congr 1
    ring
  simp only [Function.comp_def,mul_one,id_eq] at hh
  rw [hfun] at hh
  exact hh.deriv.symm

end Asakura.Chapter11
