import Chapter4VectorCoefficientDifference

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4.Vector
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

/-- The drift-coordinate estimate in the finite-dimensional Picard proof. -/
theorem drift_difference_path_moment
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {dim : ℕ}
    (R L : ℝ) (hR : 0≤R) (hL : 0≤L)
    (b : (Fin dim → ℝ) → ℝ) (hb : Continuous b)
    (hLip : ∀ x y,(b x-b y)^2≤L*‖x-y‖^2)
    (Y₁ Y₂ : Ω → C(Icc (0:ℝ) R,Fin dim → ℝ))
    (hm₁ : Measurable Y₁) (hm₂ : Measurable Y₂) (hi₁ : MemLp Y₁ 2 P) (hi₂ : MemLp Y₂ 2 P)
    (D : Ω → C(Icc (0:ℝ) R,ℝ)) (hDm : AEStronglyMeasurable D P)
    (hD : ∀ᵐ w ∂P,∀ t,D w t=∫ r in 0..t.val,
      (b (Y₁ w (projIcc 0 R hR r))-b (Y₂ w (projIcc 0 R hR r)))) :
    MemLp D 2 P ∧ (∫ w,‖D w‖^2 ∂P)≤
      (R*L)*(∫ r in 0..R,(∫ w,‖prefixPath hR (Y₁ w-Y₂ w) r‖^2 ∂P)) := by
  let U := fun z : Ω × ℝ => b (Y₁ z.1 (projIcc 0 R hR z.2))-b (Y₂ z.1 (projIcc 0 R hR z.2))
  have hUm : Measurable U := (hb.measurable.comp (clamped_path_evaluation_measurable R hR Y₁ hm₁)).sub
    (hb.measurable.comp (clamped_path_evaluation_measurable R hR Y₂ hm₂))
  obtain ⟨hiU,hE⟩ := one_coefficient_difference_energy P R L hR hL b hb hLip Y₁ Y₂ hm₁ hm₂ hi₁ hi₂
  obtain ⟨hDi,hDb⟩ := Asakura.Chapter4.drift_path_moment_bound P R hR U hUm hiU D hDm hD
  have hiU2 := (memLp_two_iff_integrable_sq hiU.aestronglyMeasurable).1 hiU
  have he : (∫ r in 0..R,(∫ w,U (w,r)^2 ∂P))=∫ z,U z^2 ∂P.prod (volume.restrict (Ioc (0:ℝ) R)) := by
    rw [intervalIntegral.integral_of_le hR,← integral_integral_swap hiU2]
    exact (integral_prod _ hiU2).symm
  rw [he] at hDb
  exact ⟨hDi,hDb.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hE hR)⟩

end Asakura.Chapter4.Vector
