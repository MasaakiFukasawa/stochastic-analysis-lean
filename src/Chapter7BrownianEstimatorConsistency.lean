import Chapter7BrownianProductGridEnergy
import Chapter7MeanSquareProbability

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter4
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

noncomputable def realizedCovarianceEntry {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (u v : Fin d → ℝ) (T : ℝ) (n : ℕ) (w : Ω) : ℝ :=
  (∑ k : Fin n,
    (∑ j,u j*(B.W j (realTimeClamp (((k:ℝ)+1)*(T/n))) w-B.W j (realTimeClamp ((k:ℝ)*(T/n))) w))*
    (∑ j,v j*(B.W j (realTimeClamp (((k:ℝ)+1)*(T/n))) w-B.W j (realTimeClamp ((k:ℝ)*(T/n))) w)))/T

theorem brownian_estimator_mean_square {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (u v : Fin d → ℝ) (T : ℝ) (hT : 0 < T) (n : ℕ) (hn : 0 < n) :
    MemLp (fun w => realizedCovarianceEntry B u v T n w-(∑ j,u j*v j)) 2 P ∧
    (∫ w,(realizedCovarianceEntry B u v T n w-(∑ j,u j*v j))^2 ∂P)=
      ((∑ j,u j^2)*(∑ j,v j^2)+(∑ j,u j*v j)^2)/n := by
  classical
  let h := T/n
  have hnR : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hh : 0 ≤ h := div_nonneg hT.le (Nat.cast_nonneg _)
  let D := fun k : Fin n => fun w j =>
    B.W j (realTimeClamp (((k:ℝ)+1)*h)) w-B.W j (realTimeClamp ((k:ℝ)*h)) w
  let Z := fun k w => (∑ j,u j*D k w j)*(∑ j,v j*D k w j)-h*(∑ j,u j*v j)
  have hg := brownian_product_grid_energy (n := n) P B u v h hh
  have he w : realizedCovarianceEntry B u v T n w-(∑ j,u j*v j)=(∑ k,Z k w)/T := by
    change (∑ k : Fin n,(∑ j,u j*D k w j)*(∑ j,v j*D k w j))/T-(∑ j,u j*v j)=
      (∑ k : Fin n,((∑ j,u j*D k w j)*(∑ j,v j*D k w j)-h*(∑ j,u j*v j)))/T
    rw [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    have hnh : (n:ℝ)*h=T := by dsimp [h]; field_simp
    rw [← mul_assoc,hnh,sub_div,mul_div_cancel_left₀ _ hT.ne']
  constructor
  · have hi : MemLp (fun w => (∑ k,Z k w)/T) 2 P := by
      simpa only [div_eq_mul_inv] using hg.1.mul_const T⁻¹
    convert hi using 1
    funext w
    exact he w
  · simp_rw [he,div_pow]
    rw [integral_div,hg.2]
    dsimp only [h]
    field_simp
    <;> ring

theorem brownian_estimator_consistency {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (u v : Fin d → ℝ) (T : ℝ) (hT : 0 < T) :
    TendstoInMeasure P (fun n => realizedCovarianceEntry B u v T (n+1)) atTop
      (fun _ => ∑ j,u j*v j) := by
  apply mean_square_probability P _ _ (fun n => (brownian_estimator_mean_square P B u v T hT (n+1) (Nat.succ_pos _)).1)
  simp only [(brownian_estimator_mean_square P B u v T hT (_+1) (Nat.succ_pos _)).2]
  have hh : Tendsto (fun n : ℕ => ((n+1:ℕ):ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hlim := tendsto_inv_atTop_zero.comp hh
  simpa only [div_eq_mul_inv,mul_zero,Function.comp_def] using hlim.const_mul ((∑ j,u j^2)*(∑ j,v j^2)+(∑ j,u j*v j)^2)

end Asakura.Chapter7
