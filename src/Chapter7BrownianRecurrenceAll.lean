import Chapter7BrownianRecurrence

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter4
set_option maxHeartbeats 1800000

/-- Reflection preserves the actual Brownian covariance characterization. -/
def reflectedBrownian
    {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    (B : BrownianSystem P 1) : BrownianSystem P 1 where
  F := B.F
  mono := B.mono
  le := B.le
  null := B.null
  W := fun j t w => -B.W j t w
  C := B.C
  martingale := fun j => by simpa only [neg_one_mul] using (B.martingale j).smul P B.F (-1)
  cov := fun j k => ⟨by simpa only [neg_mul_neg] using (B.cov j k).defect,(B.cov j k).variation⟩
  clock := B.clock

theorem brownian_hits_zero
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (B : BrownianSystem P 1) (x : ℝ) :
    ∀ᵐ w ∂P,∃ r : ℝ,0 ≤ r ∧ x+B.W 0 (realTimeClamp r) w = 0 := by
  by_cases hx : 0 ≤ x
  · exact brownian_hits_zero_from_nonnegative P B x hx
  · have h := brownian_hits_zero_from_nonnegative P (reflectedBrownian B) (-x) (by linarith)
    filter_upwards [h] with w hw
    obtain ⟨r,hr,he⟩ := hw
    refine ⟨r,hr,?_⟩
    change -x + -B.W 0 (realTimeClamp r) w = 0 at he
    linarith

/-- Continuity upgrades recurrence at countably many integer levels to
simultaneous hitting of every real level. This also allows a random
starting position in the recurrence argument, without any additional
independence assumption. -/
theorem continuous_path_hits_all_levels
    (f : ℝ → ℝ) (hf : Continuous f)
    (h : ∀ z : ℤ,∃ t : ℝ,0 ≤ t ∧ f t = z) :
    ∀ x : ℝ,∃ t : ℝ,0 ≤ t ∧ f t = x := by
  intro x
  obtain ⟨a,ha,hea⟩ := h ⌊x⌋
  obtain ⟨b,hb,heb⟩ := h (⌊x⌋+1)
  have hlo : (⌊x⌋ : ℝ) ≤ x := Int.floor_le x
  have hhi : x ≤ ((⌊x⌋+1:ℤ):ℝ) := by exact_mod_cast (Int.lt_floor_add_one x).le
  rcases le_total a b with hab | hba
  · obtain ⟨t,ht,het⟩ := intermediate_value_Icc hab hf.continuousOn ⟨by simpa [hea] using hlo,by simpa [heb] using hhi⟩
    exact ⟨t,ha.trans ht.1,het⟩
  · obtain ⟨t,ht,het⟩ := intermediate_value_Icc' hba hf.continuousOn ⟨by simpa [hea] using hlo,by simpa [heb] using hhi⟩
    exact ⟨t,hb.trans ht.1,het⟩

end Asakura.Chapter7
