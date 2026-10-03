import Chapter9GaussianSmoothness

open Set Filter MeasureTheory Finset
open scoped Topology ContDiff
namespace Asakura.Chapter11
open Asakura.Chapter9
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false
attribute [-instance] ContinuousMultilinearMap.seminormedAddCommGroup ContinuousMultilinearMap.seminormedAddCommGroup'

noncomputable def weightedHeatExponent (L z : ℝ) (q : ℝ × ℝ) : ℝ :=
  -(1:ℝ)/2*Real.log (2*Real.pi*q.1)-(q.2-z)^2/(2*q.1)+z^2/(8*L)
noncomputable def weightedHeatCoefficient (L : ℝ) (i : Fin 3) (q : ℝ × ℝ) : ℝ :=
  ![-(1:ℝ)/2*Real.log (2*Real.pi*q.1)-q.2^2/(2*q.1),q.2/q.1,-1/(2*q.1)+1/(8*L)] i
noncomputable def heatWeight (i : Fin 3) (z : ℝ) : ℝ := ![1,z,z^2] i

theorem weighted_heat_coefficient_smooth (L : ℝ) (i : Fin 3) :
    ContDiffOn ℝ ∞ (weightedHeatCoefficient L i) {q : ℝ × ℝ | 0<q.1 ∧ q.1<L} := by
  have ht q (hq : q∈{q : ℝ × ℝ | 0<q.1 ∧ q.1<L}) : q.1≠0 := ne_of_gt hq.1
  have h2 q (hq : q∈{q : ℝ × ℝ | 0<q.1 ∧ q.1<L}) : 2*q.1≠0 := mul_ne_zero (by norm_num) (ht q hq)
  have hp q (hq : q∈{q : ℝ × ℝ | 0<q.1 ∧ q.1<L}) : 2*Real.pi*q.1≠0 := mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) (ht q hq)
  fin_cases i
  · dsimp only [weightedHeatCoefficient,Matrix.cons_val_zero]
    exact (contDiffOn_const.mul ((by fun_prop : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => 2*Real.pi*q.1) _).log hp)).sub
      ((by fun_prop : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => q.2^2) _).div (by fun_prop) h2)
  · dsimp only [weightedHeatCoefficient,Matrix.cons_val_succ,Matrix.cons_val_zero]
    exact (by fun_prop : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => q.2) _).div (by fun_prop) ht
  · dsimp only [weightedHeatCoefficient,Matrix.cons_val_succ,Matrix.cons_val_zero]
    exact (contDiffOn_const.div (by fun_prop) h2).add contDiffOn_const

theorem weighted_heat_coefficients (L z : ℝ) (q : ℝ × ℝ) :
    weightedHeatExponent L z q=∑ i : Fin 3,heatWeight i z*weightedHeatCoefficient L i q := by
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,heatWeight,weightedHeatCoefficient,
    Matrix.cons_val_zero,Matrix.cons_val_succ,one_mul,add_zero]
  dsimp only [weightedHeatExponent]
  ring

theorem heat_weight_bound (i : Fin 3) (z : ℝ) : |heatWeight i z|≤1+|z|^2 := by
  fin_cases i
  · change |(1:ℝ)| ≤ 1+|z|^2
    simp only [abs_one];nlinarith [sq_nonneg |z|]
  · change |z| ≤ 1+|z|^2
    nlinarith [sq_nonneg (|z|-1)]
  · change |z^2| ≤ 1+|z|^2
    rw [abs_of_nonneg (sq_nonneg _)];nlinarith [sq_abs z]

theorem weighted_heat_exponent_smooth (L z : ℝ) :
    ContDiffOn ℝ ∞ (weightedHeatExponent L z) {q : ℝ × ℝ | 0<q.1 ∧ q.1<L} := by
  change ContDiffOn ℝ ∞ (fun q => weightedHeatExponent L z q) _
  simp_rw [weighted_heat_coefficients]
  apply ContDiffOn.sum
  intro i _
  exact contDiffOn_const.mul (weighted_heat_coefficient_smooth L i)

/-- Retain a Gaussian tail after multiplying the heat kernel by the
reciprocal Gaussian weight used to make the payoff a finite measure. -/
theorem weighted_heat_tail (L t y z : ℝ) (ht : 0<t) (htL : t≤L) :
    weightedHeatExponent L z (t,y)≤(-(1:ℝ)/2*Real.log (2*Real.pi*t)+y^2/(2*t))-z^2/(8*L) := by
  have hL : 0<L := ht.trans_le htL
  have h1 : z^2/(4*L)≤z^2/(4*t) := div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith)
  have h2 : -(y-z)^2/(2*t)≤y^2/(2*t)-z^2/(4*t) := by
    have hh : -(y-z)^2≤y^2-z^2/2 := by nlinarith [sq_nonneg (2*y-z)]
    have hh' := div_le_div_of_nonneg_right hh (show 0≤2*t by positivity)
    convert hh' using 1 <;> ring
  rw [neg_div] at h2
  dsimp only [weightedHeatExponent]
  have he : z^2/(4*L)=2*(z^2/(8*L)) := by ring
  linarith

/-- All actual derivatives of the weighted heat kernel have uniform bounds
on compact subsets of 0<t<L. No boundedness of the original payoff is used. -/
theorem weighted_heat_all_order_bound (L : ℝ) (hL : 0<L)
    (K : Set (ℝ × ℝ)) (hK : IsCompact K) (hKU : K⊆{q : ℝ × ℝ | 0<q.1 ∧ q.1<L})
    (n : ℕ) : ∃ B : ℝ,0≤B ∧ ∀ z q,q∈K →
      ‖iteratedFDerivWithin ℝ n (fun p => Real.exp (weightedHeatExponent L z p))
        {p : ℝ × ℝ | 0<p.1 ∧ p.1<L} q‖≤B := by
  let U := {q : ℝ × ℝ | 0<q.1 ∧ q.1<L}
  have hU : IsOpen U := (isOpen_lt continuous_const continuous_fst).inter (isOpen_lt continuous_fst continuous_const)
  obtain ⟨C,hC,hder⟩ := weighted_coefficient_derivative_bound U K hU hK hKU
    (weightedHeatCoefficient L) (weighted_heat_coefficient_smooth L) heatWeight abs heat_weight_bound n
  have hd z q (hq : q∈K) (i : ℕ) (_hi : 1 ≤ i) (hi : i ≤ n) :
      ‖iteratedFDerivWithin ℝ i (weightedHeatExponent L z) U q‖≤C*(1+|z|^2) := by
    rw [show weightedHeatExponent L z=(fun p => ∑ j,heatWeight j z*weightedHeatCoefficient L j p) from funext (weighted_heat_coefficients L z)]
    exact hder z q hq i hi
  have hp : ContinuousOn (fun q : ℝ × ℝ => -(1:ℝ)/2*Real.log (2*Real.pi*q.1)+q.2^2/(2*q.1)) K := by
    apply ContinuousOn.add
    · apply continuousOn_const.mul
      exact (by fun_prop : ContinuousOn (fun q : ℝ × ℝ => 2*Real.pi*q.1) K).log
        (fun q hq => by have hh := (hKU hq).1;positivity)
    · exact (by fun_prop : ContinuousOn (fun q : ℝ × ℝ => q.2^2) K).div (by fun_prop)
        (fun q hq => by have hh := (hKU hq).1;positivity)
  obtain ⟨M,hM⟩ := hK.exists_bound_of_continuousOn hp
  have htail z q (hq : q∈K) : Real.exp (weightedHeatExponent L z q)≤Real.exp M*Real.exp (-(1/(8*L))*|z|^2) := by
    rw [←Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hh := weighted_heat_tail L q.1 q.2 z (hKU hq).1 (hKU hq).2.le
    have hm := (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hM q hq)
    rw [sq_abs]
    convert hh.trans (sub_le_sub_right hm (z^2/(8*L))) using 1 <;> ring
  exact exponential_quadratic_all_order_bound U K hU hKU (weightedHeatExponent L) abs abs_nonneg n C
    (Real.exp M) (1/(8*L)) hC (Real.exp_pos _).le (by positivity) (weighted_heat_exponent_smooth L) hd htail

end Asakura.Chapter11
