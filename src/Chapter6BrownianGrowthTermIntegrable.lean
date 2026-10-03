import Chapter6BrownianWeightedRegression

open MeasureTheory ProbabilityTheory Set Filter Finset
open scoped Topology BigOperators
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter7
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

theorem brownian_growth_grid_term_integrable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P d)
    (h : ℝ) (hh : 0<h) (k : ℕ) (hk : k<n)
    (b : (Fin d → ℝ) → (Fin d → ℝ)) (hb : Measurable b) (K : ℝ)
    (hbound : ∀ x,‖WithLp.toLp 2 (b x)‖≤K*(1+‖WithLp.toLp 2 x‖)) :
    Integrable (fun w => ∑ i,b (fun i => B.W i (realTimeClamp ((k:ℝ)*h)) w) i*
      (B.W i (realTimeClamp (((k:ℝ)+1)*h)) w-B.W i (realTimeClamp ((k:ℝ)*h)) w)) P := by
  let U := fun w i => B.W i (realTimeClamp ((k:ℝ)*h)) w
  have hWa (i : Fin d) (a : ℕ) : Measurable (B.W i (realTimeClamp ((a:ℝ)*h))) :=
    ((B.martingale i).adapted P B.F _ (changed_time_finite _ (mul_nonneg (Nat.cast_nonneg a) hh.le))).mono (B.le _) le_rfl
  have hUm : Measurable U := measurable_pi_iff.mpr (fun i => hWa i k)
  let times : Bool × Fin d → ℕ := fun p => if p.1 then k+1 else k
  have ht p : times p≤n := by dsimp [times]; split_ifs <;> omega
  obtain ⟨hg,_,_⟩ := brownian_grid_samples_gaussian P B h hh.le times ht (fun p => p.2)
  let LU : ((Bool × Fin d) → ℝ) →L[ℝ] (Fin d → ℝ) := ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj (false,i))
  have hUg : HasGaussianLaw U P := hg.map LU
  have hUe : HasGaussianLaw (fun w => WithLp.toLp 2 (U w)) P := hUg.map_equiv (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm
  have hb2 : MemLp (fun w => WithLp.toLp 2 (b (U w))) 2 P := by
    have hdom : MemLp (fun w => K*(1+‖WithLp.toLp 2 (U w)‖)) 2 P := ((memLp_const (1:ℝ)).add hUe.memLp_two.norm).const_mul K
    exact hdom.mono' ((WithLp.measurable_toLp 2 _).comp (hb.comp hUm)).aestronglyMeasurable (ae_of_all _ (fun w => hbound _))
  apply integrable_finsetSum
  intro i _
  have hi : MemLp (fun w => B.W i (realTimeClamp (((k:ℝ)+1)*h)) w-U w i) 2 P := by
    simpa [times,U,Nat.cast_add,Nat.cast_one,Pi.sub_def] using (hg.eval (true,i)).memLp_two.sub (hg.eval (false,i)).memLp_two
  have hbi : MemLp (fun w => b (U w) i) 2 P :=
    hb2.norm.mono' (((measurable_pi_apply i).comp (hb.comp hUm)).aestronglyMeasurable)
      (ae_of_all _ (fun w => PiLp.norm_apply_le (WithLp.toLp 2 (b (U w))) i))
  exact hbi.integrable_mul hi

end Asakura.Chapter6
