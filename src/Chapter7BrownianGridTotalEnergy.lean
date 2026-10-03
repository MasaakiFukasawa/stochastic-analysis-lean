import Chapter7BrownianSecondMoments

open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

lemma brownian_grid_total_energy {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P d)
    (u : Fin d → ℝ) (h : ℝ) (hh : 0≤h) :
    let V := fun w => ∑ k : Fin n,
      (∑ j,u j*(B.W j (realTimeClamp (((k:ℝ)+1)*h)) w-B.W j (realTimeClamp ((k:ℝ)*h)) w))^2
    Integrable V P ∧ (∫ w,V w ∂P)=(n:ℝ)*h*(∑ j,u j^2) := by
  let X := fun (k : Fin n) w => ∑ j,u j*(B.W j (realTimeClamp (((k:ℝ)+1)*h)) w-B.W j (realTimeClamp ((k:ℝ)*h)) w)
  have he (k : Fin n) : ((k:ℝ)+1)*h-(k:ℝ)*h=h := by ring
  have hm (k : Fin n) := brownian_projection_second P B ((k:ℝ)*h) (((k:ℝ)+1)*h)
    (mul_nonneg (by positivity) hh) (by nlinarith) u
  have hi k : Integrable (fun w => X k w^2) P :=
    (memLp_two_iff_integrable_sq (hm k).1.aestronglyMeasurable).mp (hm k).1
  refine ⟨integrable_finsetSum _ (fun k _ => hi k),?_⟩
  rw [integral_finsetSum _ (fun k _ => hi k)]
  have hmean k : (∫ w,X k w^2 ∂P)=h*(∑ j,u j^2) := by simpa only [he] using (hm k).2
  change (∑ k,∫ w,X k w^2 ∂P)=_
  simp only [hmean,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,mul_assoc]

lemma brownian_grid_energy_measurable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P d)
    (u : Fin d → ℝ) (h : ℝ) (hh : 0≤h) :
    Measurable (fun w => ∑ k : Fin n,
      (∑ j,u j*(B.W j (realTimeClamp (((k:ℝ)+1)*h)) w-B.W j (realTimeClamp ((k:ℝ)*h)) w))^2) := by
  apply Finset.measurable_sum
  intro k _
  apply Measurable.pow_const
  apply Finset.measurable_sum
  intro j _
  apply measurable_const.mul
  exact (((B.martingale j).adapted P B.F _ (real_time_below _ (by positivity) (EReal.coe_lt_top _))).mono (B.le _) le_rfl).sub
    (((B.martingale j).adapted P B.F _ (real_time_below _ (by positivity) (EReal.coe_lt_top _))).mono (B.le _) le_rfl)

end Asakura.Chapter7
