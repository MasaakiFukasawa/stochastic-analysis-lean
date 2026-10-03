import Chapter9ReverseFields
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

open MeasureTheory Set Filter
open scoped ContDiff Topology
namespace Asakura.Chapter9
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- Compact smooth replacement agrees on a neighborhood of every point
 of the closed localization ball, so its first and second jets agree too. -/
theorem smooth_compact_replacement {d : ℕ} (q : (Fin d → ℝ) → ℝ)
    (hq : ContDiff ℝ ∞ q) (R : ℝ) (hR : 0≤R) :
    ∃ f : (Fin d → ℝ) → ℝ,ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      ∀ x,‖x‖≤R → f=ᶠ[𝓝 x] q := by
  let χ : ContDiffBump (0 : Fin d → ℝ) := ⟨R+1,R+2,by linarith,by linarith⟩
  refine ⟨fun x => χ x*q x,χ.contDiff.mul hq,χ.hasCompactSupport.mul_right,?_⟩
  intro x hx
  have he := χ.eventuallyEq_one_of_mem_ball (show x∈Metric.ball 0 χ.rIn by
    simpa only [Metric.mem_ball,dist_zero_right] using (show ‖x‖<R+1 by linarith))
  filter_upwards [he] with y hy
  change χ y=1 at hy
  rw [hy,one_mul]

theorem directional_congr_near {d : ℕ} {f g : (Fin d → ℝ) → ℝ}
    {x : Fin d → ℝ} (he : f=ᶠ[𝓝 x] g) (v : Fin d → ℝ) :
    directional f v=ᶠ[𝓝 x] directional g v := by
  have hh := he.fderiv (𝕜 := ℝ)
  filter_upwards [hh] with y hy
  exact congrArg (fun L => L v) hy

theorem reverse_generator_congr_near {d : ℕ} (μ : Measure (Fin d → ℝ))
    (t : ℝ) {f g : (Fin d → ℝ) → ℝ} {x : Fin d → ℝ}
    (he : f=ᶠ[𝓝 x] g) : ouReverseGenerator μ f (t,x)=ouReverseGenerator μ g (t,x) := by
  unfold ouReverseGenerator
  apply Finset.sum_congr rfl
  intro i _
  rw [(directional_congr_near (directional_congr_near he (Pi.single i 1)) (Pi.single i 1)).eq_of_nhds,
    (directional_congr_near he (Pi.single i 1)).eq_of_nhds]

 theorem directional_coordinate {d : ℕ} (i : Fin d) (v x : Fin d → ℝ) :
    directional (fun y : Fin d → ℝ => y i) v x=v i := by
  unfold directional
  change (fderiv ℝ (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ) x) v=v i
  rw [ContinuousLinearMap.fderiv]
  rfl

 theorem directional_coordinate_twice {d : ℕ} (i : Fin d) (v x : Fin d → ℝ) :
    directional (directional (fun y : Fin d → ℝ => y i) v) v x=0 := by
  have he : directional (fun y : Fin d → ℝ => y i) v=(fun _ => v i) :=
    funext (directional_coordinate i v)
  rw [he]
  simp [directional]

 theorem reverse_generator_coordinate {d : ℕ} (μ : Measure (Fin d → ℝ))
    (t : ℝ) (i : Fin d) (x : Fin d → ℝ) :
    ouReverseGenerator μ (fun y => y i) (t,x)=ouReverseDrift μ (t,x) i := by
  classical
  unfold ouReverseGenerator
  simp only [directional_coordinate_twice,directional_coordinate,zero_add]
  simp [Pi.single_apply,eq_comm]

theorem reverse_generator_product_rule {d : ℕ} (μ : Measure (Fin d → ℝ))
    (t : ℝ) (f g : (Fin d → ℝ) → ℝ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (x : Fin d → ℝ) :
    ouReverseGenerator μ (fun y => f y*g y) (t,x)=
      g x*ouReverseGenerator μ f (t,x)+f x*ouReverseGenerator μ g (t,x)+
        2*∑ i,directional f (Pi.single i 1) x*directional g (Pi.single i 1) x := by
  unfold ouReverseGenerator
  simp_rw [directional_product_twice f g hf hg,directional_product f g hf hg]
  rw [Finset.mul_sum,Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem reverse_generator_coordinate_product {d : ℕ} (μ : Measure (Fin d → ℝ))
    (t : ℝ) (i j : Fin d) (x : Fin d → ℝ) :
    ouReverseGenerator μ (fun y => y i*y j) (t,x)=
      x j*ouReverseDrift μ (t,x) i+x i*ouReverseDrift μ (t,x) j+
        2*(if i=j then 1 else 0) := by
  classical
  rw [reverse_generator_product_rule μ t _ _ (by fun_prop) (by fun_prop),
    reverse_generator_coordinate,reverse_generator_coordinate]
  simp [directional_coordinate,Pi.single_apply,eq_comm]
end Asakura.Chapter9
