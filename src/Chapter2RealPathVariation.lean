import Chapter2ItoCovarianceCharacterization
import Chapter2LocalTotalVariation

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

theorem real_time_clamp_image_Icc
    {T : EReal} [Fact (0 ≤ T)] (d : ℝ) (hd : 0 ≤ d) (hdT : (d:EReal) < T) :
    realTimeClamp (T := T) '' Icc 0 d = Iic (realTimeClamp d) := by
  ext t
  constructor
  · rintro ⟨r,hr,rfl⟩
    exact real_time_clamp_mono hr.2
  · intro ht
    have hdt : realTimeClamp (T := T) d < ⊤ := by
      change (realTimeClamp d : EReal) < T
      rw [real_time_clamp_eq d hd hdT.le]
      exact hdT
    obtain ⟨r,hr,hrT,he⟩ := finite_closed_time_real t (ht.trans_lt hdt)
    refine ⟨r,⟨hr,?_⟩,he⟩
    have hh : (realTimeClamp (T := T) r : EReal) ≤ (realTimeClamp (T := T) d : EReal) := by
      rw [he]; exact ht
    rw [real_time_clamp_eq r hr hrT.le,real_time_clamp_eq d hd hdT.le] at hh
    exact EReal.coe_le_coe_iff.mp hh

theorem real_path_variation_identity
    {T : EReal} [Fact (0 ≤ T)] (f : ClosedTime T → ℝ)
    (d : ℝ) (hd : 0 ≤ d) (hdT : (d:EReal) < T) :
    (eVariationOn (fun r => f (realTimeClamp r)) (Icc 0 d)).toReal =
      pathVariation f (realTimeClamp d) := by
  have he := eVariationOn.comp_eq_of_monotoneOn f (realTimeClamp (T := T))
    (t := Icc 0 d) (real_time_clamp_mono.monotoneOn (Icc 0 d))
  rw [real_time_clamp_image_Icc d hd hdT] at he
  exact congrArg ENNReal.toReal he

/-- Cofinal monotone stopped paths imply monotonicity on all finite times. -/
theorem monotone_on_of_cofinal_stops
    {ι : Type*} [LinearOrder ι] [OrderTop ι]
    (f : ι → ℝ) (τ : ℕ → ι)
    (hc : ∀ t, t < ⊤ → ∃ n, t < τ n)
    (hm : ∀ n, Monotone (fun t => f (min (τ n) t))) : MonotoneOn f (Iio ⊤) := by
  intro s hs t ht hst
  obtain ⟨n,hn⟩ := hc t ht
  have h := hm n hst
  simpa only [min_eq_right hn.le,min_eq_right (hst.trans hn.le)] using h

theorem local_variation_jordan_regular
    {Ω : Type*} {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F)
    (A : ClosedTime T → Ω → ℝ) (hA : AdaptedLocalVariationWitness F A) :
    let V := fun t ω => pathVariation (fun s => A s ω) t
    let U := fun t ω => (V t ω+A t ω)/2
    let W := fun t ω => (V t ω-A t ω)/2
    AdaptedLocalVariationWitness F U ∧ AdaptedLocalVariationWitness F W ∧
      (∀ ω, MonotoneOn (fun t => U t ω) (Iio ⊤) ∧ MonotoneOn (fun t => W t ω) (Iio ⊤)) := by
  intro V U W
  obtain ⟨hV,hP,hQ,τ,hs,hm,ht,hc,hmon⟩ := adapted_local_total_variation hA hF
  refine ⟨?_,?_,?_⟩
  · simpa only [one_div,mul_comm (2:ℝ)⁻¹,← div_eq_mul_inv] using hP.smul (1/2)
  · simpa only [one_div,mul_comm (2:ℝ)⁻¹,← div_eq_mul_inv] using hQ.smul (1/2)
  · intro ω
    constructor
    · apply monotone_on_of_cofinal_stops _ (fun n => τ n ω) (hc ω)
      intro n s t hst
      exact div_le_div_of_nonneg_right ((hmon n ω).2.1 hst) (by norm_num)
    · apply monotone_on_of_cofinal_stops _ (fun n => τ n ω) (hc ω)
      intro n s t hst
      exact div_le_div_of_nonneg_right ((hmon n ω).2.2 hst) (by norm_num)

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.real_path_variation_identity
#print axioms Asakura.Chapter2Complete.local_variation_jordan_regular
