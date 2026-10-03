import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL2
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

open MeasureTheory
open scoped InnerProductSpace
namespace Asakura.FullAudit

variable {Ω E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [CompleteSpace E]

/-- C2 makes the regression residual orthogonal to every measurable competitor. -/
theorem denoising_residual_orthogonal {m m0 : MeasurableSpace Ω}
    (P : @Measure Ω m0) (hm : m ≤ m0) (Z s : Lp E 2 P)
    (hs : AEStronglyMeasurable[m] s P) :
    ⟪Z - (condExpL2 E ℝ hm Z : Lp E 2 P),
      s - (condExpL2 E ℝ hm Z : Lp E 2 P)⟫_ℝ = 0 := by
  have hmeas := hs.sub (aestronglyMeasurable_condExpL2 (𝕜 := ℝ) hm Z)
  have hsub : AEStronglyMeasurable[m]
      (s - (condExpL2 E ℝ hm Z : Lp E 2 P)) P :=
    hmeas.congr (Lp.coeFn_sub s _).symm
  rw [inner_sub_left, inner_condExpL2_eq_inner_fun hm Z _ hsub, sub_self]

/-- The manuscript's exact Pythagorean argument, in L2 norm form. -/
theorem denoising_loss_identity {m m0 : MeasurableSpace Ω}
    (P : @Measure Ω m0) (hm : m ≤ m0) (Z s : Lp E 2 P)
    (hs : AEStronglyMeasurable[m] s P) :
    ‖s-Z‖^2 = ‖s-(condExpL2 E ℝ hm Z : Lp E 2 P)‖^2 +
      ‖Z-(condExpL2 E ℝ hm Z : Lp E 2 P)‖^2 := by
  have h := denoising_residual_orthogonal P hm Z s hs
  have hid : s-Z = (s-(condExpL2 E ℝ hm Z : Lp E 2 P)) -
      (Z-(condExpL2 E ℝ hm Z : Lp E 2 P)) := by abel
  rw [hid, norm_sub_sq_real, real_inner_comm, h]
  ring

/-- Minimization follows from the nonnegative squared error, as in the text. -/
theorem denoising_loss_minimum {m m0 : MeasurableSpace Ω}
    (P : @Measure Ω m0) (hm : m ≤ m0) (Z s : Lp E 2 P)
    (hs : AEStronglyMeasurable[m] s P) :
    ‖(condExpL2 E ℝ hm Z : Lp E 2 P)-Z‖^2 ≤ ‖s-Z‖^2 := by
  rw [denoising_loss_identity P hm Z s hs, norm_sub_rev]
  exact le_add_of_nonneg_left (sq_nonneg _)

/-- Converts the Hilbert space norm used above to the expected squared norm. -/
theorem l2_squared_norm_integral [MeasurableSpace Ω] (P : Measure Ω) (f : Lp E 2 P) :
    ‖f‖^2 = ∫ ω, ‖f ω‖^2 ∂P := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  congr 1
  funext ω
  exact real_inner_self_eq_norm_sq (f ω)

end Asakura.FullAudit
