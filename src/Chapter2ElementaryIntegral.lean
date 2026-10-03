import Chapter2StoppedCovariance
import Chapter2LocalProcess
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

/-- The elementary integral G 1_[a,b) against a bounded continuous
martingale is itself a bounded continuous martingale. Both cases in the
printed proof (conditioning before a, and at/after a) are checked. -/
theorem elementary_integral_bounded_martingale
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (X : boundedMProcess P F) (a b : ClosedTime T) (hab : a ≤ b)
    (G : Ω → ℝ) (hGm : Measurable[F a] G) (hG : MemLp G ∞ P) :
    (fun t ω => G ω * (X.val (min b t) ω - X.val (min a t) ω)) ∈ boundedMProcess P F := by
  let Xa := stopBounded P F hF hle X (fun _ => a) (fun t => by by_cases h : a ≤ t <;> simp [h])
  let Xb := stopBounded P F hF hle X (fun _ => b) (fun t => by by_cases h : b ≤ t <;> simp [h])
  let W := Xb-Xa
  let Z := fun t ω => G ω * W.val t ω
  have hWval (t ω) : W.val t ω = X.val (min b t) ω-X.val (min a t) ω := rfl
  have hZzero (t) (ht : t ≤ a) : Z t = 0 := by
    funext ω
    simp only [Z,hWval,min_eq_right ht,min_eq_right (ht.trans hab),sub_self,mul_zero,Pi.zero_apply]
  have hZm (t) : Measurable[F t] (Z t) := by
    by_cases hat : a ≤ t
    · exact (hGm.mono (hF hat) le_rfl).mul (W.property.1.adapted t)
    · rw [hZzero t (le_of_not_ge hat)]
      exact measurable_const
  have hZLp (t) : MemLp (Z t) ∞ P := hG.mul (W.property.2 t)
  have hZi (t) : Integrable (Z t) P := (hZLp t).integrable le_top
  have hafter (s t) (has : a ≤ s) (hst : s ≤ t) : P[Z t | F s] =ᵐ[P] Z s := by
    have h := condExp_mul_of_stronglyMeasurable_left
      (hGm.mono (hF has) le_rfl).stronglyMeasurable (hZi t)
      ((W.property.1.moment t).integrable (by norm_num))
    exact h.trans (Filter.EventuallyEq.mul Filter.EventuallyEq.rfl (W.property.1.martingale s t hst))
  have hmart (s t) (hst : s ≤ t) : P[Z t | F s] =ᵐ[P] Z s := by
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
  refine ⟨⟨hZm,fun t => (hZLp t).mono_exponent le_top,
    fun ω => continuous_const.mul (W.property.1.path ω),hmart,?_⟩,hZLp⟩
  change Z ⊥ =ᵐ[P] 0
  rw [hZzero ⊥ bot_le]

/-- Multiplying a square-integrable martingale that vanishes up to a by
an F_a-measurable bounded random variable preserves M2. -/
theorem predictable_scalar_delayed_martingale
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (W : ClosedTime T → Ω → ℝ) (hW : ContinuousM2Witness P F W)
    (a : ClosedTime T) (hzero : ∀ t, t ≤ a → W t = 0)
    (G : Ω → ℝ) (hGm : Measurable[F a] G) (hG : MemLp G ∞ P) :
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
  have hZLp (t) : MemLp (Z t) 2 P := hG.mul (hW.moment t)
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

/-- Elementary stochastic integration preserves M2, with no boundedness
assumption on the integrator. -/
theorem elementary_integral_m2
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (X : ClosedTime T → Ω → ℝ) (hX : ContinuousM2Witness P F X)
    (a b : ClosedTime T) (hab : a ≤ b)
    (G : Ω → ℝ) (hGm : Measurable[F a] G) (hG : MemLp G ∞ P) :
    ContinuousM2Witness P F (fun t ω => G ω * (X (min b t) ω-X (min a t) ω)) := by
  have ha := continuous_m2_stopped P F hF hle X hX (fun _ => a)
    (fun t => by by_cases h : a ≤ t <;> simp [h])
  have hb := continuous_m2_stopped P F hF hle X hX (fun _ => b)
    (fun t => by by_cases h : b ≤ t <;> simp [h])
  have hW : ContinuousM2Witness P F (fun t ω => X (min b t) ω-X (min a t) ω) := by
    convert hb.add P F (ha.smul P F (-1)) using 1
    funext t ω
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,neg_one_mul,sub_eq_add_neg]
  apply predictable_scalar_delayed_martingale P F hF hle _ hW a _ G hGm hG
  intro t ht
  funext ω
  simp only [min_eq_right ht,min_eq_right (ht.trans hab),sub_self,Pi.zero_apply]

/-- The same elementary integral against an actual local martingale is
local, using its original bounded localizers and commutation of stopping. -/
theorem elementary_integral_local_martingale
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (X : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (a b : ClosedTime T) (hab : a ≤ b)
    (G : Ω → ℝ) (hGm : Measurable[F a] G) (hG : MemLp G ∞ P) :
    LocalMProcessWitness P F (fun t ω => G ω * (X (min b t) ω-X (min a t) ω)) := by
  obtain ⟨τ,ht,hm,hb,hc,hXτ⟩ := hX.localizers
  refine ⟨τ,ht,hm,hb,hc,?_⟩
  intro n
  have h := elementary_integral_bounded_martingale P F hF hle ⟨_,hXτ n⟩ a b hab G hGm hG
  convert h using 1
  funext t ω
  change G ω * (X (min b (min (τ n ω) t)) ω-X (min a (min (τ n ω) t)) ω) =
    G ω * (X (min (τ n ω) (min b t)) ω-X (min (τ n ω) (min a t)) ω)
  rw [min_left_comm b, min_left_comm a]

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.elementary_integral_bounded_martingale
#print axioms Asakura.Chapter2Complete.elementary_integral_local_martingale

#print axioms Asakura.Chapter2Complete.predictable_scalar_delayed_martingale
#print axioms Asakura.Chapter2Complete.elementary_integral_m2
