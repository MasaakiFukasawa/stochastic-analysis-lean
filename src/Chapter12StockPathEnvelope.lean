import Chapter12BrownianMaximumMoments
import Chapter12AsianDenominatorBound

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

noncomputable def stockPathValue (x σ r T : ℝ)
    (f : C(Icc (0:ℝ) T,ℝ)) (t : Icc (0:ℝ) T) : ℝ :=
  x*Real.exp ((r-σ^2/2)*t.val+σ*f t)

theorem stock_path_upper_bound (x σ r T : ℝ)
    (f : C(Icc (0:ℝ) T,ℝ)) (t : Icc (0:ℝ) T) :
    |stockPathValue x σ r T f t| ≤
      |x| *Real.exp (|r-σ^2/2| *T+|σ| *‖f‖) := by
  dsimp only [stockPathValue]
  rw [abs_mul,abs_of_pos (Real.exp_pos _)]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg x)
  apply Real.exp_le_exp.mpr
  have h1 : (r-σ^2/2)*t.val ≤ |r-σ^2/2| *T :=
    (mul_le_mul_of_nonneg_right (le_abs_self _) t.property.1).trans
      (mul_le_mul_of_nonneg_left t.property.2 (abs_nonneg _))
  have h2 : σ*f t ≤ |σ| *‖f‖ := by
    apply (le_abs_self _).trans
    rw [abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg σ)
    simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm t
  linarith

theorem stock_path_joint_measurable {Ω : Type*} [MeasurableSpace Ω]
    (x σ r T : ℝ) (X : Ω → C(Icc (0:ℝ) T,ℝ)) (hX : Measurable X) :
    Measurable (fun z : Icc (0:ℝ) T × Ω => stockPathValue x σ r T (X z.2) z.1) := by
  let f := fun z : Icc (0:ℝ) T × C(Icc (0:ℝ) T,ℝ) => stockPathValue x σ r T z.2 z.1
  have hf : Continuous f := by unfold f stockPathValue; fun_prop
  exact hf.measurable.comp (measurable_fst.prodMk (hX.comp measurable_snd))

/-- A common finite-Lp envelope for all stock values up to T, obtained
from the already verified Brownian maximal exponential moments. -/
theorem stock_path_common_envelope {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hc : ∀ w, Continuous (fun t => B t w)) (T : ℝ≥0)
    (X : Ω → C(Icc (0:ℝ) T,ℝ)) (hXm : Measurable X)
    (he : ∀ w (s : Icc (0:ℝ) T), X w s = B ⟨s.val,s.property.1⟩ w)
    (x σ r : ℝ) (p : ℝ≥0∞) (hp : p ≠ ⊤) :
    ∃ G : Ω → ℝ, MemLp G p P ∧
      (∀ t : Icc (0:ℝ) T, ∀ w, ‖stockPathValue x σ r T (X w) t‖ ≤ ‖G w‖) ∧
      ∀ t : Icc (0:ℝ) T, MemLp (fun w => stockPathValue x σ r T (X w) t) p P := by
  let G := fun w => (|x| *Real.exp (|r-σ^2/2| *T))*Real.exp (|σ| *‖X w‖)
  have hG : MemLp G p P :=
    (brownian_path_exponential_memLp P B hB hm hc T X hXm he |σ| p hp).const_mul _
  have hb (t : Icc (0:ℝ) T) (w : Ω) : ‖stockPathValue x σ r T (X w) t‖ ≤ ‖G w‖ := by
    rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ G w by dsimp [G]; positivity)]
    dsimp only [G]
    rw [mul_assoc,← Real.exp_add]
    exact stock_path_upper_bound x σ r T (X w) t
  refine ⟨G,hG,hb,fun t => ?_⟩
  apply hG.of_le
  · exact ((stock_path_joint_measurable x σ r T X hXm).comp measurable_prodMk_left).aestronglyMeasurable
  · exact ae_of_all P (hb t)

end Asakura.Chapter12
