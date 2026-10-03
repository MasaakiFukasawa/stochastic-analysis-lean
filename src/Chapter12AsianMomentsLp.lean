import Chapter12AsianVegaMoments
import Chapter12ParameterIntegralMoments

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

theorem asian_moment_memLp {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (p : ℝ≥0∞) (T : ℝ) (hT : 0 ≤ T)
    (X : Ω → C(Icc (0:ℝ) T,ℝ)) (hXm : Measurable X)
    (x σ r : ℝ) (j : ℕ) (G : Ω → ℝ) (hG : MemLp G p P)
    (hSb : ∀ t, ∀ w, ‖stockPathValue x σ r T (X w) t‖ ≤ ‖G w‖) :
    MemLp (fun w => asianMoment T hT x σ r j (X w)) p P := by
  let F := fun z : Icc (0:ℝ) T × Ω => z.1.val^j*stockPathValue x σ r T (X z.2) z.1
  have hm : Measurable F := ((measurable_subtype_coe.comp measurable_fst).pow_const j).mul
    (stock_path_joint_measurable x σ r T X hXm)
  apply parameter_integral_memLp (compactTimeMeasure T hT) P p F hm (fun w => T^j*G w) (hG.const_mul (T^j))
  intro w t
  dsimp only [F]
  rw [norm_mul (t.val^j),norm_mul (T^j)]
  rw [show ‖t.val^j‖ = t.val^j from Real.norm_of_nonneg (pow_nonneg t.property.1 j),
    show ‖T^j‖ = T^j from Real.norm_of_nonneg (pow_nonneg hT j)]
  exact mul_le_mul (pow_le_pow_left₀ t.property.1 t.property.2 j) (hSb t w) (norm_nonneg _) (pow_nonneg hT j)

theorem asian_vega_moment_memLp {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (p : ℝ≥0∞) (T : ℝ) (hT : 0 ≤ T)
    (X : Ω → C(Icc (0:ℝ) T,ℝ)) (hXm : Measurable X)
    (x σ r : ℝ) (j : ℕ) (G : Ω → ℝ) (hG : MemLp G p P)
    (hSb : ∀ t, ∀ w, ‖stockPathValue x σ r T (X w) t*(X w t-σ*t.val)‖ ≤ ‖G w‖) :
    MemLp (fun w => asianVegaMoment T hT x σ r j (X w)) p P := by
  let F := fun z : Icc (0:ℝ) T × Ω => z.1.val^j*(stockPathValue x σ r T (X z.2) z.1*(X z.2 z.1-σ*z.1.val))
  have hm : Measurable F := by
    let f := fun z : Icc (0:ℝ) T × C(Icc (0:ℝ) T,ℝ) => z.1.val^j*(stockPathValue x σ r T z.2 z.1*(z.2 z.1-σ*z.1.val))
    have hf : Continuous f := by unfold f stockPathValue; fun_prop
    exact hf.measurable.comp (measurable_fst.prodMk (hXm.comp measurable_snd))
  have hi := parameter_integral_memLp (compactTimeMeasure T hT) P p F hm (fun w => T^j*G w) (hG.const_mul (T^j))
    (fun w t => by
      dsimp only [F]
      rw [norm_mul (t.val^j),norm_mul (T^j)]
      rw [show ‖t.val^j‖ = t.val^j from Real.norm_of_nonneg (pow_nonneg t.property.1 j),
        show ‖T^j‖ = T^j from Real.norm_of_nonneg (pow_nonneg hT j)]
      exact mul_le_mul (pow_le_pow_left₀ t.property.1 t.property.2 j) (hSb t w) (norm_nonneg _) (pow_nonneg hT j))
  simpa only [F,asianVegaMoment,mul_assoc] using hi

end Asakura.Chapter12
