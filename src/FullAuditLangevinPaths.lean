import FullAuditChapter4Gronwall
import Mathlib.Analysis.InnerProductSpace.Calculus

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace
namespace Asakura.FullAudit
set_option maxHeartbeats 600000

/-- Integrate the Hessian lower bound along the actual segment from y to x. -/
theorem langevin_gradient_monotone {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : E → E) (H : E → E →L[ℝ] E) (κ : ℝ)
    (hD : ∀ x, HasFDerivAt g (H x) x)
    (hH : ∀ x v, κ*‖v‖^2 ≤ ⟪v,H x v⟫) (x y : E) :
    κ*‖x-y‖^2 ≤ ⟪x-y,g x-g y⟫ := by
  let v := x-y
  let f := fun s : ℝ => ⟪v,g (y+s • v)⟫
  have hd (s : ℝ) : HasDerivAt f ⟪v,H (y+s • v) v⟫ s := by
    have hp : HasDerivAt (fun t : ℝ => y+t • v) v s := by
      simpa using ((hasDerivAt_id s).smul_const v).const_add y
    simpa only [Function.comp_apply,inner_zero_left,add_zero] using
      (hasDerivAt_const s v).inner ℝ ((hD _).comp_hasDerivAt s hp)
  have hf : Differentiable ℝ f := fun s => (hd s).differentiableAt
  have h := mul_sub_le_image_sub_of_le_deriv hf (fun s => by rw [(hd s).deriv]; exact hH _ v)
    (show (0:ℝ) ≤ 1 by norm_num)
  simpa [f,v,inner_sub_right] using h

/-- The integrating factor proves the contraction for each pair of paths.
 Only their difference needs a derivative; the individual noisy paths do not. -/
theorem langevin_path_contraction {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (X Y : ℝ → E) (g : E → E) (κ T : ℝ) (hT : 0 ≤ T)
    (hcX : ContinuousOn X (Icc 0 T)) (hcY : ContinuousOn Y (Icc 0 T))
    (hmono : ∀ x y, κ*‖x-y‖^2 ≤ ⟪x-y,g x-g y⟫)
    (hD : ∀ t ∈ Ioo 0 T, HasDerivAt (fun s => X s-Y s) (-(g (X t)-g (Y t))) t) :
    ∀ t ∈ Icc 0 T, ‖X t-Y t‖ ≤ Real.exp (-κ*t)*‖X 0-Y 0‖ := by
  let D := fun t => X t-Y t
  let F := fun t => Real.exp (2*κ*t)*‖D t‖^2
  have hF : ContinuousOn F (Icc 0 T) := by
    exact ((by fun_prop : Continuous (fun t : ℝ => Real.exp (2*κ*t))).continuousOn).mul ((hcX.sub hcY).norm.pow 2)
  have hd (t : ℝ) (ht : t ∈ Ioo 0 T) : HasDerivAt F
      (2*Real.exp (2*κ*t)*(κ*‖D t‖^2-⟪D t,g (X t)-g (Y t)⟫)) t := by
    have h := (((hasDerivAt_id t).const_mul (2*κ)).exp).mul (hD t ht).norm_sq
    convert h using 1
    · rfl
    · simp only [inner_neg_right,id_eq]
      dsimp only [D]
      ring
  have ha : AntitoneOn F (Icc 0 T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 T) hF
    · intro t ht
      exact (hd t (by simpa using ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hd t (by simpa using ht)).deriv]
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr (hmono _ _))
  intro t ht
  have hh := ha (show (0:ℝ) ∈ Icc 0 T from ⟨le_rfl,hT⟩) ht ht.1
  have hb := mul_le_mul_of_nonneg_left hh (Real.exp_pos (-2*κ*t)).le
  have hexp : Real.exp (-2*κ*t)*Real.exp (2*κ*t) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1 <;> congr 1 <;> ring
  have hsq : ‖D t‖^2 ≤ (Real.exp (-κ*t)*‖D 0‖)^2 := by
    dsimp only [F] at hb
    rw [← mul_assoc,hexp,one_mul,mul_zero,Real.exp_zero,one_mul] at hb
    rw [mul_pow,pow_two (Real.exp _),← Real.exp_add]
    convert hb using 1
    congr 2
    ring
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))).mp hsq

/-- Cancellation from the integral form of the two equations, driven by the
 same arbitrary continuous noise. The stochastic differentiation step is not assumed. -/
theorem langevin_common_noise_difference {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E]
    (X Y W : ℝ → E) (g : E → E) (x y : E) (T : ℝ)
    (hX : Continuous X) (hY : Continuous Y) (hg : Continuous g)
    (hIX : ∀ t ∈ Icc 0 T, X t = x-(∫ s in (0:ℝ)..t, g (X s))+W t)
    (hIY : ∀ t ∈ Icc 0 T, Y t = y-(∫ s in (0:ℝ)..t, g (Y s))+W t) :
    ∀ t ∈ Ioo 0 T, HasDerivAt (fun s => X s-Y s) (-(g (X t)-g (Y t))) t := by
  intro t ht
  have hcx := hg.comp hX
  have hcy := hg.comp hY
  have hdx := intervalIntegral.integral_hasDerivAt_right (hcx.intervalIntegrable 0 t)
    hcx.stronglyMeasurable.stronglyMeasurableAtFilter hcx.continuousAt
  have hdy := intervalIntegral.integral_hasDerivAt_right (hcy.intervalIntegrable 0 t)
    hcy.stronglyMeasurable.stronglyMeasurableAtFilter hcy.continuousAt
  have hd := ((hasDerivAt_const t x).sub hdx).sub ((hasDerivAt_const t y).sub hdy)
  have hd' : HasDerivAt (fun u => (x-(∫ s in (0:ℝ)..u,g (X s)))-(y-(∫ s in (0:ℝ)..u,g (Y s))))
      (-(g (X t)-g (Y t))) t := by
    convert hd using 1
    · rfl
    · simp only [Function.comp_apply,zero_sub]
      abel
  apply hd'.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with u hu
  rw [hIX u ⟨hu.1.le,hu.2.le⟩,hIY u ⟨hu.1.le,hu.2.le⟩]
  abel

end Asakura.FullAudit
