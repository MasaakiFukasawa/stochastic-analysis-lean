import Chapter4EulerUniformMoment
import Chapter4EulerEstimates

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4
open Asakura.Chapter5
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

noncomputable def eulerSecondMomentConstant (R K : ℝ) (dim noise : ℕ) : ℝ :=
  let α := (dim:ℝ)*3
  let rate := vectorMomentGrowthRate R 2 K α dim ((noise:ℝ)*noise)
  (α*dim+rate*R)*Real.exp ((rate+1)*R)

lemma euler_moment_rate_nonneg (R K : ℝ) (hR : 0≤R) (hK : 0≤K) (dim noise : ℕ) :
    0≤vectorMomentGrowthRate R 2 K ((dim:ℝ)*3) dim ((noise:ℝ)*noise) := by
  have hc := (Asakura.Chapter3Complete.bdg_moment_constants_positive (2:ℝ) (by norm_num)).1.le
  unfold vectorMomentGrowthRate
  positivity

lemma euler_second_moment_constant_nonneg (R K : ℝ) (hR : 0≤R) (hK : 0≤K) (dim noise : ℕ) :
    0≤eulerSecondMomentConstant R K dim noise := by
  have hr := euler_moment_rate_nonneg R K hR hK dim noise
  unfold eulerSecondMomentConstant
  positivity

lemma coordinate_square_moment_sum_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {dim : ℕ}
    (ξ : Ω → Fin dim → ℝ) (hξ : MemLp ξ 2 P) :
    (∑ i,∫ w,(ξ w i)^2 ∂P)≤(dim:ℝ)*(∫ w,‖ξ w‖^2 ∂P) := by
  have hh i : (∫ w,(ξ w i)^2 ∂P)≤∫ w,‖ξ w‖^2 ∂P := by
    apply integral_mono ((memLp_two_iff_integrable_sq (memLp_pi_iff.mp hξ i).aestronglyMeasurable).mp (memLp_pi_iff.mp hξ i))
      (hξ.integrable_norm_pow (by norm_num : (2:ℕ)≠0))
    intro w
    have hi := norm_le_pi_norm (ξ w) i
    simpa only [Real.norm_eq_abs,sq_abs] using pow_le_pow_left₀ (norm_nonneg _) hi 2
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using
    Finset.sum_le_sum (s:=Finset.univ) (fun i _ => hh i)

lemma euler_moment_bound_linear_initial
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {dim noise : ℕ}
    (R K : ℝ) (hR : 0≤R) (hK : 0≤K)
    (ξ : Ω → Fin dim → ℝ) (hξ : MemLp ξ 2 P) (H : ℝ)
    (hH : H≤(((dim:ℝ)*3)*(∑ i,∫ w,(ξ w i)^2 ∂P)+
      vectorMomentGrowthRate R 2 K ((dim:ℝ)*3) dim ((noise:ℝ)*noise)*R)*
        Real.exp ((vectorMomentGrowthRate R 2 K ((dim:ℝ)*3) dim ((noise:ℝ)*noise)+1)*R)) :
    H≤eulerSecondMomentConstant R K dim noise*(1+∫ w,‖ξ w‖^2 ∂P) := by
  have hs := mul_le_mul_of_nonneg_left (coordinate_square_moment_sum_le P ξ hξ) (show 0≤(dim:ℝ)*3 by positivity)
  have hM : 0≤∫ w,‖ξ w‖^2 ∂P := integral_nonneg (fun w => sq_nonneg _)
  have hr := euler_moment_rate_nonneg R K hR hK dim noise
  apply hH.trans
  dsimp only [eulerSecondMomentConstant]
  have hbr := mul_nonneg hr hR
  have hh : (dim:ℝ)*3*(∑ i,∫ w,(ξ w i)^2 ∂P)+
      vectorMomentGrowthRate R 2 K ((dim:ℝ)*3) dim ((noise:ℝ)*noise)*R≤
      ((dim:ℝ)*3*dim+vectorMomentGrowthRate R 2 K ((dim:ℝ)*3) dim ((noise:ℝ)*noise)*R)*(1+∫ w,‖ξ w‖^2 ∂P) := by
    nlinarith [mul_nonneg hbr hM]
  convert mul_le_mul_of_nonneg_right hh (Real.exp_pos _).le using 1 <;> ring

lemma euler_volterra_final_bound (q : ℝ → ℝ) (R D L B : ℝ)
    (hR : 0≤R) (hD : 0≤D) (hL : 0≤L) (hB : 0≤B)
    (hq : Continuous q) (hq0 : ∀ r,0≤q r)
    (h : ∀ t∈Icc 0 R,q t≤D*(∫ r in 0..t,2*L*(q r+B))) :
    q R≤((D*(2*L)+1)*R*Real.exp ((D*(2*L)+1)*R))*B := by
  let c := D*(2*L)+1
  have hc : 0<c := by dsimp only [c];positivity
  have hh t (ht : t∈Icc 0 R) : q t≤c*B*R+c*(∫ r in 0..t,q r) := by
    have he : (∫ r in 0..t,2*L*(q r+B))=2*L*((∫ r in 0..t,q r)+B*t) := by
      rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_add (hq.intervalIntegrable _ _) intervalIntegrable_const]
      simp only [intervalIntegral.integral_const,sub_zero,smul_eq_mul]
      ring
    have hb := h t ht
    rw [he] at hb
    have hi : 0≤∫ r in 0..t,q r := intervalIntegral.integral_nonneg_of_forall ht.1 hq0
    have hbt := mul_le_mul_of_nonneg_left ht.2 hB
    have hbt' := mul_le_mul_of_nonneg_left hbt (show 0≤D*(2*L) by positivity)
    dsimp only [c]
    nlinarith only [hb,hi,hbt',mul_nonneg hB hR]
  have hg := Asakura.FullAudit.ch4_gronwall_written q (c*B*R) c R hR hq.continuousOn hc hh R ⟨hR,le_rfl⟩
  convert hg using 1 <;> dsimp only [c] <;> ring

end Asakura.Chapter4
