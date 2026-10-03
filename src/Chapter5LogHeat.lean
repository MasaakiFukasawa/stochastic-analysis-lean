import FullAuditHeatKernel
import Chapter5ColeHopf

open MeasureTheory ProbabilityTheory
namespace Asakura.Chapter5
open Asakura.FullAudit
set_option maxHeartbeats 1000000

/-- The positive lower bound needed before taking logarithms is proved for
 the actual Gaussian integral. -/
theorem heatAverage_lower_bound (g : ℝ → ℝ) (hg : Continuous g)
    (B c : ℝ) (hb : ∀ x, ‖g x‖ ≤ B) (hl : ∀ x, c ≤ g x) (x t : ℝ) :
    c ≤ heatAverage g x t := by
  have hi : Integrable (fun z => g (x+Real.sqrt t*z)) (gaussianReal 0 1) :=
    Integrable.of_bound (hg.comp (by fun_prop)).aestronglyMeasurable B (ae_of_all _ fun z => hb _)
  simpa [heatAverage] using integral_mono (integrable_const c) hi (fun z => hl (x+Real.sqrt t*z))

noncomputable def logHeat (a : ℝ) (g : ℝ → ℝ) (x t : ℝ) : ℝ :=
  Real.log (heatAverage g x t)/a

/-- The Cole-Hopf formula satisfies the nonlinear heat equation using its
actual first and second derivatives. Gaussian differentiation and positivity
are derived; only the original bounded derivatives of g are assumed. -/
theorem logHeat_pde (g dg ddg : ℝ → ℝ)
    (hd : ∀ x, HasDerivAt g (dg x) x)
    (hdd : ∀ x, HasDerivAt dg (ddg x) x) (hcdd : Continuous ddg)
    (B D E c a : ℝ) (hg : ∀ x, ‖g x‖ ≤ B)
    (hdg : ∀ x, ‖dg x‖ ≤ D) (hddg : ∀ x, ‖ddg x‖ ≤ E)
    (hc : 0 < c) (hpos : ∀ x, c ≤ g x) (ha : a ≠ 0)
    (x t : ℝ) (ht : 0 < t) :
    deriv (logHeat a g x) t =
      (deriv (fun y => deriv (fun z => logHeat a g z t) y) x)/2 +
        a/2*(deriv (fun y => logHeat a g y t) x)^2 := by
  have hcg : Continuous g := continuous_iff_continuousAt.2 (fun y => (hd y).continuousAt)
  have hcdg : Continuous dg := continuous_iff_continuousAt.2 (fun y => (hdd y).continuousAt)
  have hq y : 0 < heatAverage g y t := hc.trans_le (heatAverage_lower_bound g hcg B c hg hpos y t)
  have h0 y := heatAverage_space_derivative hd hcdg B D hg hdg y t
  have h1 y := heatAverage_space_derivative hdd hcdd D E hdg hddg y t
  have hw y : HasDerivAt (fun z => logHeat a g z t)
      (heatAverage dg y t/(a*heatAverage g y t)) y := by
    exact coleHopf_derivative a y (heatAverage dg y t) (fun z => heatAverage g z t) (h0 y) (hq y).ne'
  have he : (fun y => deriv (fun z => logHeat a g z t) y) =
      (fun y => heatAverage dg y t/(a*heatAverage g y t)) := by
    funext y;exact (hw y).deriv
  have hv : HasDerivAt (fun y => heatAverage dg y t/(a*heatAverage g y t))
      ((heatAverage ddg x t*heatAverage g x t-(heatAverage dg x t)^2)/
        (a*(heatAverage g x t)^2)) x := by
    convert (h1 x).div ((h0 x).const_mul a) (mul_ne_zero ha (hq x).ne') using 1
    field_simp
    <;> ring
  have htime := heatAverage_heat_equation hd hdd hcdd B D E hg hdg hddg x t ht
  have hwt : HasDerivAt (logHeat a g x)
      (((1/2)*heatAverage ddg x t)/(a*heatAverage g x t)) t :=
    coleHopf_derivative a t _ (heatAverage g x) htime (hq x).ne'
  rw [hwt.deriv,he,hv.deriv,(hw x).deriv]
  have hne := (hq x).ne'
  field_simp
  <;> ring

end Asakura.Chapter5
