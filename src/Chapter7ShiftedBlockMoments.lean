import Chapter7BrownianBlockMoments

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

/-- The same estimates on a block starting at any deterministic time. -/
theorem shifted_brownian_block_moments {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (u v : Fin d → ℝ) (s h : ℝ) (hs : 0 ≤ s) (hh : 0 ≤ h) :
    let U := fun w => ∫ r in 0..h,
      (∑ j,u j*(B.W j (realTimeClamp (s+r)) w-B.W j (realTimeClamp s) w))*
      (∑ j,v j*(B.W j (realTimeClamp (s+r)) w-B.W j (realTimeClamp s) w))
    MemLp U 2 P ∧ (∫ w,U w ∂P)=h^2*(∑ j,u j*v j)/2 ∧
    (∫ w,U w^2 ∂P) ≤ h^4*((∑ j,u j^2)*(∑ j,v j^2)+2*(∑ j,u j*v j)^2)/3 ∧
    P[U|B.F (realTimeClamp s)] =ᵐ[P] fun _ => h^2*(∑ j,u j*v j)/2 := by
  dsimp only
  have hz : realTimeClamp 0 = (⊥ : HalfClosedTime) := by apply Subtype.ext; simp [realTimeClamp]
  have he w : (∫ r in 0..h,
      (∑ j,u j*((B.shift s hs).W j (realTimeClamp r) w-(B.shift s hs).W j (realTimeClamp 0) w))*
      (∑ j,v j*((B.shift s hs).W j (realTimeClamp r) w-(B.shift s hs).W j (realTimeClamp 0) w))) =
      ∫ r in 0..h,
      (∑ j,u j*(B.W j (realTimeClamp (s+r)) w-B.W j (realTimeClamp s) w))*
      (∑ j,v j*(B.W j (realTimeClamp (s+r)) w-B.W j (realTimeClamp s) w)) := by
    rw [intervalIntegral.integral_of_le hh,intervalIntegral.integral_of_le hh]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    simp only [BrownianSystem.shift,hz,deterministic_shift_real s hs r hr.1.le,
      deterministic_shift_bot s hs,sub_self,sub_zero]
  have hf : (B.shift s hs).F (realTimeClamp 0)=B.F (realTimeClamp s) := by
    simp only [BrownianSystem.shift,hz,deterministic_shift_bot s hs]
  simpa only [he,hf] using brownian_block_moments P (B.shift s hs) u v h hh

end Asakura.Chapter7
