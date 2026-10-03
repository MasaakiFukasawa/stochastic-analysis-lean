import Chapter11WeightedHeatSmooth
import Chapter9DirectionalJets

open Set Filter
open scoped Topology ContDiff
namespace Asakura.Chapter11
open Asakura.Chapter9
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false
attribute [-instance] ContinuousMultilinearMap.seminormedAddCommGroup ContinuousMultilinearMap.seminormedAddCommGroup'

theorem weighted_heat_dx (L z t y : ℝ) (ht : t≠0) :
    HasDerivAt (fun a => Real.exp (weightedHeatExponent L z (t,a)))
      (-(y-z)/t*Real.exp (weightedHeatExponent L z (t,y))) y := by
  have h := (((((hasDerivAt_id y).sub_const z).pow 2).div_const (2*t)).const_sub
    (-(1:ℝ)/2*Real.log (2*Real.pi*t))).add_const (z^2/(8*L))
  convert h.exp using 1
  · rfl
  · dsimp only [weightedHeatExponent]
    simp only [Nat.reduceSub,pow_one,Nat.cast_ofNat,Pi.pow_apply,id_eq]
    field_simp
    <;> ring

theorem weighted_heat_dxx (L z t y : ℝ) (ht : t≠0) :
    HasDerivAt (fun a => -(a-z)/t*Real.exp (weightedHeatExponent L z (t,a)))
      (((y-z)^2/t^2-1/t)*Real.exp (weightedHeatExponent L z (t,y))) y := by
  have h := ((((hasDerivAt_id y).sub_const z).neg.div_const t).mul (weighted_heat_dx L z t y ht))
  convert h using 1
  · rfl
  · simp only [Pi.neg_apply,Pi.sub_apply,Pi.div_apply,id_eq]
    field_simp
    <;> ring

theorem weighted_heat_dt (L z t y : ℝ) (ht : t≠0) :
    HasDerivAt (fun a => Real.exp (weightedHeatExponent L z (a,y)))
      (((y-z)^2/(2*t^2)-1/(2*t))*Real.exp (weightedHeatExponent L z (t,y))) t := by
  have hl := ((hasDerivAt_id t).const_mul (2*Real.pi)).log (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) ht)
  have hh := (((hl.const_mul (-(1:ℝ)/2)).sub
    ((hasDerivAt_const t ((y-z)^2)).div ((hasDerivAt_id t).const_mul 2) (mul_ne_zero (by norm_num) ht))).add_const (z^2/(8*L))).exp
  convert hh using 1
  · rfl
  · simp only [weightedHeatExponent,Pi.sub_apply,Pi.div_apply,id_eq]
    field_simp [Real.pi_ne_zero]
    <;> ring

theorem weighted_heat_smooth_at (L z t y : ℝ) (ht : 0<t ∧ t<L) :
    ContDiffAt ℝ ∞ (fun q => Real.exp (weightedHeatExponent L z q)) (t,y) :=
  (weighted_heat_exponent_smooth L z).exp.contDiffAt
    (((isOpen_lt continuous_const continuous_fst).inter (isOpen_lt continuous_fst continuous_const)).mem_nhds ht)

theorem weighted_heat_space_first_jet (L z t y : ℝ) (ht : 0<t ∧ t<L) :
    iteratedFDeriv ℝ 1 (fun q => Real.exp (weightedHeatExponent L z q)) (t,y) (fun _ => (0,1))=
      -(y-z)/t*Real.exp (weightedHeatExponent L z (t,y)) := by
  have hd := first_jet_line (fun q => Real.exp (weightedHeatExponent L z q)) (t,y) (0,1) (weighted_heat_smooth_at L z t y ht)
  have hh := (weighted_heat_dx L z t y ht.1.ne').comp_of_eq 0 ((hasDerivAt_id (0:ℝ)).const_add y) (by simp)
  have he : (fun r : ℝ => Real.exp (weightedHeatExponent L z ((t,y)+r • (0,1))))=
      fun r => Real.exp (weightedHeatExponent L z (t,y+r)) := by funext r;simp
  rw [he] at hd
  simpa using hd.unique hh

theorem weighted_heat_space_second_jet (L z t y : ℝ) (ht : 0<t ∧ t<L) :
    iteratedFDeriv ℝ 2 (fun q => Real.exp (weightedHeatExponent L z q)) (t,y) (fun _ => (0,1))=
      ((y-z)^2/t^2-1/t)*Real.exp (weightedHeatExponent L z (t,y)) := by
  have hd := second_jet_line (fun q => Real.exp (weightedHeatExponent L z q)) (t,y) (0,1) (weighted_heat_smooth_at L z t y ht)
  have hh := (weighted_heat_dxx L z t y ht.1.ne').comp_of_eq 0 ((hasDerivAt_id (0:ℝ)).const_add y) (by simp)
  have he (r : ℝ) : (t,y)+r • (0,1)=(t,y+r) := by ext <;> simp
  simp_rw [he,weighted_heat_space_first_jet L z t _ ht] at hd
  simpa using hd.unique hh

theorem weighted_heat_time_jet (L z t y : ℝ) (ht : 0<t ∧ t<L) :
    iteratedFDeriv ℝ 1 (fun q => Real.exp (weightedHeatExponent L z q)) (t,y) (fun _ => (1,0))=
      ((y-z)^2/(2*t^2)-1/(2*t))*Real.exp (weightedHeatExponent L z (t,y)) := by
  have hd := first_jet_line (fun q => Real.exp (weightedHeatExponent L z q)) (t,y) (1,0) (weighted_heat_smooth_at L z t y ht)
  have hh := (weighted_heat_dt L z t y ht.1.ne').comp_of_eq 0 ((hasDerivAt_id (0:ℝ)).const_add t) (by simp)
  have he : (fun r : ℝ => Real.exp (weightedHeatExponent L z ((t,y)+r • (1,0))))=
      fun r => Real.exp (weightedHeatExponent L z (t+r,y)) := by funext r;simp
  rw [he] at hd
  simpa using hd.unique hh

theorem weighted_heat_jet_equation (L z t y : ℝ) (ht : 0<t ∧ t<L) :
    iteratedFDeriv ℝ 1 (fun q => Real.exp (weightedHeatExponent L z q)) (t,y) (fun _ => (1,0))=
      (1/2:ℝ)*iteratedFDeriv ℝ 2 (fun q => Real.exp (weightedHeatExponent L z q)) (t,y) (fun _ => (0,1)) := by
  rw [weighted_heat_time_jet L z t y ht,weighted_heat_space_second_jet L z t y ht]
  ring

end Asakura.Chapter11
