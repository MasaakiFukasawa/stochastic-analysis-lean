import Chapter12AsianMomentGraphs

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

/-- All required moments of the time-integrated derivative follow from
stock-path moments, independently of an operator at the higher exponent. -/
theorem asian_moment_gradient_memLp {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp2 : 2 ≤ p)
    (T : ℝ) (hT : 0 ≤ T) (X : Ω → C(Icc (0:ℝ) T,ℝ)) (hXm : Measurable X)
    (h : Icc (0:ℝ) T → H) (hh : Continuous h)
    (x σ r : ℝ) (j : ℕ) (G : Ω → ℝ) (hG : MemLp G p P)
    (hSb : ∀ t, ∀ᵐ w ∂P, ‖stockPathValue x σ r T (X w) t‖ ≤ ‖G w‖) :
    MemLp (fun w => asianMomentGradient T hT x σ r j h (X w)) p P := by
  let V := fun z : Icc (0:ℝ) T × Ω => z.1.val^j*stockPathValue x σ r T (X z.2) z.1
  have hVm : Measurable V :=
    ((measurable_subtype_coe.comp measurable_fst).pow_const j).mul
      (stock_path_joint_measurable x σ r T X hXm)
  have hVc (w) : Continuous (fun t => V (t,w)) := by unfold V stockPathValue; fun_prop
  have hb (t) : ∀ᵐ w ∂P, ‖V (t,w)‖ ≤ ‖T^j*G w‖ := by
    filter_upwards [hSb t] with w hw
    dsimp only [V]
    rw [norm_mul,norm_mul]
    rw [show ‖t.val^j‖ = t.val^j from Real.norm_of_nonneg (pow_nonneg t.property.1 j),
      show ‖T^j‖ = T^j from Real.norm_of_nonneg (pow_nonneg hT j)]
    exact mul_le_mul (pow_le_pow_left₀ t.property.1 t.property.2 j) hw (norm_nonneg _) (pow_nonneg hT j)
  have hL (t) : MemLp (fun w => V (t,w)) p P :=
    (hG.const_mul (T^j)).of_le (hVm.comp measurable_prodMk_left).aestronglyMeasurable (hb t)
  have he := scalar_direction_integral_pointwise (compactTimeMeasure T hT) P p hp hp2 V hVm hL hVc
    (fun t => σ • h t) (hh.const_smul σ) (fun w => T^j*G w) (hG.const_mul (T^j)) hb
  exact (Lp.memLp (∫ t,(ContinuousLinearMap.toSpanSingleton ℝ (σ • h t)).compLp ((hL t).toLp _)
    ∂compactTimeMeasure T hT)).ae_eq he

end Asakura.Chapter12
