import Chapter9FokkerPlanck
import Chapter9SliceDerivatives
import Chapter9ReverseIntegralGenerator

open Set Finset MeasureTheory
open scoped ContDiff
namespace Asakura.Chapter9
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
attribute [-instance] ContinuousMultilinearMap.seminormedAddCommGroup ContinuousMultilinearMap.seminormedAddCommGroup'

theorem ou_mixture_slice_smooth {d : ℕ} (μ : Measure (Fin d → ℝ)) [IsFiniteMeasure μ]
    (t : ℝ) (ht : 0<t) : ContDiff ℝ ∞ (fun y => ∫ x,Real.exp (ouExponent x (t,y)) ∂μ) := by
  apply spatial_slice_smooth (fun q => ∫ x,Real.exp (ouExponent x q) ∂μ) t
  intro y
  exact (ou_gaussian_mixture_smooth μ).contDiffAt
    ((isOpen_lt continuous_const continuous_fst).mem_nhds ht)

/-- The previously established joint-jet PDE is the actual time derivative
and the actual spatial adjoint acting on the same mixture density. -/
theorem ou_mixture_actual_time_derivative {d : ℕ} (μ : Measure (Fin d → ℝ)) [IsFiniteMeasure μ]
    (t : ℝ) (ht : 0<t) (y : Fin d → ℝ) :
    HasDerivAt (fun s => ∫ x,Real.exp (ouExponent x (s,y)) ∂μ)
      (ouAdjoint (fun z => ∫ x,Real.exp (ouExponent x (t,z)) ∂μ) y) t := by
  let p := fun q => ∫ x,Real.exp (ouExponent x q) ∂μ
  have hsm z : ContDiffAt ℝ ∞ p (t,z) := (ou_gaussian_mixture_smooth μ).contDiffAt
    ((isOpen_lt continuous_const continuous_fst).mem_nhds ht)
  have hd := time_slice_derivative p t y (hsm y)
  have he := ou_mixture_fokker_planck μ t ht y
  change iteratedFDeriv ℝ 1 p (t,y) (fun _ => (1,0)) =
    (∑ i,iteratedFDeriv ℝ 2 p (t,y) (fun _ => (0,Pi.single i 1)))+
    (d:ℝ)*p (t,y)+(∑ i,y i*iteratedFDeriv ℝ 1 p (t,y) (fun _ => (0,Pi.single i 1))) at he
  rw [he] at hd
  simp_rw [spatial_slice_first_jet p t y _ (hsm y),spatial_slice_second_jet p t y _ hsm] at hd
  convert hd using 1
  unfold ouAdjoint
  simp_rw [directional_coordinate_product _ (ou_mixture_slice_smooth μ t ht)]
  rw [sum_add_distrib,sum_add_distrib,sum_const]
  simp only [card_univ,Fintype.card_fin,nsmul_eq_mul]
  simp only [p,add_assoc]
end Asakura.Chapter9
