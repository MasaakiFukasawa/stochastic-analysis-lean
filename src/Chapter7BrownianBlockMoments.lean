import Chapter7ConditionalIntegralMean
import Chapter7BrownianProductConditionalMean
import Chapter7BrownianProductFourth
import Chapter7BrownianProjectionRegular
import Chapter7RandomFieldEnergy
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter4
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- Mean and fourth-order bound of the actual within-block time integral.
These are the h² and h⁴ estimates used to prove convergence of the bracket. -/
theorem brownian_block_moments {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (u v : Fin d → ℝ) (h : ℝ) (hh : 0 ≤ h) :
    let H := fun w r =>
      (∑ j,u j*(B.W j (realTimeClamp r) w-B.W j (realTimeClamp 0) w))*
      (∑ j,v j*(B.W j (realTimeClamp r) w-B.W j (realTimeClamp 0) w))
    let U := fun w => ∫ r in 0..h,H w r
    MemLp U 2 P ∧ (∫ w,U w ∂P)=h^2*(∑ j,u j*v j)/2 ∧
    (∫ w,U w^2 ∂P) ≤ h^4*((∑ j,u j^2)*(∑ j,v j^2)+2*(∑ j,u j*v j)^2)/3 ∧
    P[U|B.F (realTimeClamp 0)] =ᵐ[P] fun _ => h^2*(∑ j,u j*v j)/2 := by
  classical
  dsimp only
  let H := fun z : Ω × ℝ =>
    (∑ j,u j*(B.W j (realTimeClamp (max 0 z.2)) z.1-B.W j (realTimeClamp 0) z.1))*
    (∑ j,v j*(B.W j (realTimeClamp (max 0 z.2)) z.1-B.W j (realTimeClamp 0) z.1))
  let μ := volume.restrict (Ioc (0:ℝ) h)
  let L := (∑ j,u j^2)*(∑ j,v j^2)+2*(∑ j,u j*v j)^2
  have hL : 0 ≤ L := add_nonneg (mul_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _))) (by positivity)
  have hm : Measurable H := (brownian_projection_regular P B u).2.mul (brownian_projection_regular P B v).2
  have hmom (r : ℝ) (hr : 0 ≤ r) : MemLp (fun w => H (w,r)) 2 P ∧
      (∫ w,H (w,r)^2 ∂P)=r^2*L := by
    simpa only [H,max_eq_right hr,sub_zero,L] using brownian_product_fourth P B 0 r le_rfl hr u v
  have hmean (r : ℝ) (hr : 0 ≤ r) : (∫ w,H (w,r) ∂P)=r*(∑ j,u j*v j) := by
    simpa only [H,max_eq_right hr,sub_zero] using (brownian_projection_cross P B 0 r le_rfl hr u v).2
  have hHi : MemLp H 2 (P.prod μ) := by
    apply random_field_energy P μ H hm (h^2*L)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    refine ⟨(memLp_two_iff_integrable_sq (hmom r hr.1.le).1.aestronglyMeasurable).mp (hmom r hr.1.le).1,?_⟩
    rw [(hmom r hr.1.le).2]
    exact mul_le_mul_of_nonneg_right ((sq_le_sq₀ hr.1.le hh).mpr hr.2) hL
  have hU := random_integral_square P μ H hm hHi
  have hμ : μ.real univ=h := by simp [μ,Measure.real,hh]
  have hrep w : (∫ r,H (w,r) ∂μ)=∫ r in 0..h,
      (∑ j,u j*(B.W j (realTimeClamp r) w-B.W j (realTimeClamp 0) w))*
      (∑ j,v j*(B.W j (realTimeClamp r) w-B.W j (realTimeClamp 0) w)) := by
    rw [intervalIntegral.integral_of_le hh]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    simp only [H,max_eq_right hr.1.le]
  have hfirst : (∫ w,∫ r,H (w,r) ∂μ ∂P)=h^2*(∑ j,u j*v j)/2 := by
    rw [integral_integral_swap (hHi.integrable (by norm_num))]
    have he : (∫ r,∫ w,H (w,r) ∂P ∂μ)=∫ r,r*(∑ j,u j*v j) ∂μ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      exact hmean r hr.1.le
    rw [he]
    change (∫ r in Ioc 0 h,r*(∑ j,u j*v j))=_
    rw [← intervalIntegral.integral_of_le hh,intervalIntegral.integral_mul_const]
    simp [integral_id]
    <;> ring
  have hsecond : (∫ w,(∫ r,H (w,r) ∂μ)^2 ∂P) ≤ h^4*L/3 := by
    apply hU.2.trans
    rw [hμ]
    have he : (∫ r,∫ w,H (w,r)^2 ∂P ∂μ)=∫ r,r^2*L ∂μ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      exact (hmom r hr.1.le).2
    rw [he]
    change h*(∫ r in Ioc 0 h,r^2*L) ≤ _
    rw [← intervalIntegral.integral_of_le hh,intervalIntegral.integral_mul_const]
    simp [integral_pow]
    <;> ring_nf
    <;> exact le_rfl
  have hce : P[(fun w => ∫ r,H (w,r) ∂μ)|B.F (realTimeClamp 0)]
      =ᵐ[P] fun _ => h^2*(∑ j,u j*v j)/2 := by
    have hc := conditional_integral_mean P μ H (hHi.integrable (by norm_num))
      (fun r => r*(∑ j,u j*v j)) (B.F (realTimeClamp 0)) (B.le _) (by
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
        simpa only [H,max_eq_right hr.1.le,sub_zero] using
          brownian_product_conditional_mean P B 0 r le_rfl hr.1.le u v)
    have hb : (∫ r,r*(∑ j,u j*v j) ∂μ)=h^2*(∑ j,u j*v j)/2 := by
      change (∫ r in Ioc 0 h,r*(∑ j,u j*v j))=_
      rw [← intervalIntegral.integral_of_le hh,intervalIntegral.integral_mul_const]
      simp [integral_id]
      <;> ring
    simpa only [hb] using hc
  simpa only [hrep,L] using And.intro hU.1 (And.intro hfirst (And.intro hsecond hce))

end Asakura.Chapter7
