import Chapter2ElementaryIntegral

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- The elementary martingale argument only needs second moments of the
products, which follow from Brownian independence for unbounded L2 weights. -/
theorem predictable_scalar_delayed_martingale_of_product_moment
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (W : ClosedTime T → Ω → ℝ) (hW : ContinuousM2Witness P F W)
    (a : ClosedTime T) (hzero : ∀ t, t ≤ a → W t = 0)
    (G : Ω → ℝ) (hGm : Measurable[F a] G) (hprod : ∀ t,MemLp (fun w => G w*W t w) 2 P) :
    ContinuousM2Witness P F (fun t ω => G ω * W t ω) := by
  let Z := fun t ω => G ω * W t ω
  have hZzero (t) (ht : t ≤ a) : Z t = 0 := by
    funext ω
    simp only [Z,hzero t ht,Pi.zero_apply,mul_zero]
  have hZm (t) : Measurable[F t] (Z t) := by
    by_cases hat : a ≤ t
    · exact (hGm.mono (hF hat) le_rfl).mul (hW.adapted t)
    · rw [hZzero t (le_of_not_ge hat)]
      exact measurable_const
  have hZLp (t) : MemLp (Z t) 2 P := hprod t
  have hZi (t) : Integrable (Z t) P := (hZLp t).integrable (by norm_num)
  have hafter (s t) (has : a ≤ s) (hst : s ≤ t) : P[Z t | F s] =ᵐ[P] Z s := by
    have h := condExp_mul_of_stronglyMeasurable_left
      (hGm.mono (hF has) le_rfl).stronglyMeasurable (hZi t)
      ((hW.moment t).integrable (by norm_num))
    exact h.trans (Filter.EventuallyEq.mul Filter.EventuallyEq.rfl (hW.martingale s t hst))
  refine ⟨hZm,hZLp,fun ω => continuous_const.mul (hW.path ω),?_,?_⟩
  · intro s t hst
    change P[Z t | F s] =ᵐ[P] Z s
    by_cases has : a ≤ s
    · exact hafter s t has hst
    have hsa : s ≤ a := le_of_not_ge has
    by_cases hta : t ≤ a
    · simp only [hZzero t hta,hZzero s hsa,condExp_zero]
      exact Filter.EventuallyEq.rfl
    · have ha := hafter a t le_rfl (le_of_not_ge hta)
      rw [hZzero a le_rfl] at ha
      have h := (condExp_condExp_of_le (hF hsa) (hle a) (f := Z t)).symm.trans (condExp_congr_ae ha)
      simpa only [condExp_zero,hZzero s hsa] using h
  · change Z ⊥ =ᵐ[P] 0
    rw [hZzero ⊥ bot_le]

end Asakura.Chapter4
