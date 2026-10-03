import Chapter12WienerCoordinates
import Chapter12BrownianDirectionPairing

open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace NNReal
namespace Asakura.Chapter12
open Asakura.FullAudit
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

theorem wiener_orthogonal_equal_variance_law {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : Measure Ω) [IsProbabilityMeasure P] (W : H →ₗᵢ[ℝ] Lp ℝ 2 P)
    (hlaw : ∀ h,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    {n : ℕ} (v : Fin n → H) (T : ℝ≥0)
    (hv : ∀ i j,inner ℝ (v i) (v j)=if i=j then (T:ℝ) else 0) :
    HasLaw (fun w i => W (v i) w) (Measure.pi (fun _ => gaussianReal 0 T)) P := by
  have hm (h : H) : (∫ w,W h w ∂P)=0 := by
    simpa only [integral_id_gaussianReal] using (hlaw h).integral_eq
  have hc i j : cov[(W (v i) : Ω → ℝ),(W (v j) : Ω → ℝ);P]=inner ℝ (v i) (v j) := by
    rw [covariance_eq_sub (Lp.memLp _) (Lp.memLp _),hm,hm,mul_zero,sub_zero]
    have hh := W.inner_map_map (v i) (v j)
    rw [L2.inner_def] at hh
    simpa only [real_inner_comm,Real.inner_apply,Pi.mul_apply] using hh
  have hind := (wiener_joint_gaussian P W hlaw v).iIndepFun_of_covariance_eq_zero
    (fun i j hij => by rw [hc,hv,if_neg hij])
  apply hind.hasLaw_pi
  intro i
  convert hlaw (v i) using 1
  congr 1
  apply NNReal.eq
  change (T:ℝ)=‖v i‖^2
  have hh := hv i i
  simpa only [if_true,real_inner_self_eq_norm_sq] using hh.symm

theorem brownian_terminal_direction_inner (d : ℕ) (T : ℝ) (hT : 0≤T)
    (i j : Fin (d+1)) :
    inner ℝ (brownianTimeDirection (i,⟨T,hT,le_rfl⟩))
      (brownianTimeDirection (j,⟨T,hT,le_rfl⟩))=if i=j then T else 0 := by
  by_cases hij : i=j
  · subst j
    rw [if_pos rfl]
    exact (brownian_coordinate_direction_properties d T hT i).2.2 ⟨T,hT,le_rfl⟩
  · rw [if_neg hij]
    simp only [brownianTimeDirection,PiLp.inner_apply]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hik : i=k
    · subst k
      simp [Pi.single_apply,hij,Ne.symm hij]
    · simp [Pi.single_apply,hik]

end Asakura.Chapter12
