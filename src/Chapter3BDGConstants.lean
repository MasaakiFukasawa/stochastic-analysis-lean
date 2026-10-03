import Chapter3BDGUpperSmallPAE
import Chapter3BDGReverseSmallP
import Chapter3BDGUpperLargeP
import Chapter3BDGReverseLargeP
import Chapter3BDGTwoMoments

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

noncomputable def bdgUpperMomentConstant (p : ℝ) : ℝ :=
  if p < 2 then 2^(2*p)*(2/p)^(p/2)
  else if p = 2 then 4 else ((p/(p-1))^p*(p*(p-1)/2))^(p/2)
noncomputable def bdgReverseMomentConstant (p : ℝ) : ℝ :=
  if p < 2 then (2/p)^p else if p = 2 then 1 else (2*p)^(p/2)

theorem bdg_moment_constants_positive (p : ℝ) (hp : 0 < p) :
    0 < bdgUpperMomentConstant p ∧ 0 < bdgReverseMomentConstant p := by
  by_cases h : p < 2
  · simp only [bdgUpperMomentConstant,bdgReverseMomentConstant,if_pos h]
    constructor <;> positivity
  · by_cases he : p = 2
    · simp [bdgUpperMomentConstant,bdgReverseMomentConstant,he]
    · have hp1 : 0 < p-1 := by linarith
      simp only [bdgUpperMomentConstant,bdgReverseMomentConstant,if_neg h,if_neg he]
      constructor <;> positivity

/-- All bounded-stage branches of the manuscript's BDG proof, uniformly in p. -/
theorem bounded_bdg_moments
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X A : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X) (hA : LocalCovarianceWitness P F X X A)
    (hAm : ∀ ω, MonotoneOn (fun t => A t ω) (Iio ⊤))
    (hAc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => A s ω) t)
    (hA0 : ∀ ω, A ⊥ ω = 0)
    (p : ℝ) (hp : 0 < p) (b : ClosedTime T) (hb : b < ⊤)
    (K L : ℝ) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hbound : ∀ᵐ ω ∂P, A b ω ≤ K)
    (hXbound : ∀ᵐ ω ∂P, ∀ s, s ≤ b → |X s ω| ≤ L) :
    Integrable (fun ω => runningMaximum X (hX.path P F) b ω^p) P ∧
    Integrable (fun ω => A b ω^(p/2)) P ∧
    (∫ ω, runningMaximum X (hX.path P F) b ω^p ∂P) ≤
      bdgUpperMomentConstant p*(∫ ω, A b ω^(p/2) ∂P) ∧
    (∫ ω, A b ω^(p/2) ∂P) ≤
      bdgReverseMomentConstant p*(∫ ω, runningMaximum X (hX.path P F) b ω^p ∂P) := by
  by_cases hsmall : p < 2
  · have hl := bdg_reverse_small_p_bounded P hT F hF hle hnull X A hX hA hAm hAc hA0
      p hp hsmall b hb K hK hbound L hL hXbound
    obtain ⟨hx,hi,hu⟩ := bdg_upper_small_p_bounded_variation_ae P hT F hF hle hnull X A hX hA hAm hAc hA0
      p hp hsmall b hb K hK hbound
    have he := runningMaximum_eq_path_norm X (hX.path P F) b hb hx
    simp only [← he] at hu
    simpa only [bdgUpperMomentConstant,bdgReverseMomentConstant,if_pos hsmall] using
      And.intro hl.1 (And.intro hl.2.1 (And.intro hu hl.2.2))
  · by_cases heq : p = 2
    · subst p
      have hAp ω : 0 ≤ A b ω := by rw [← hA0 ω]; exact hAm ω hT hb bot_le
      have hAi : Integrable (A b) P := by
        apply (integrable_const K).mono'
          ((hA.adapted P F hX hX b hb).mono (hle b) le_rfl).aestronglyMeasurable
        filter_upwards [hbound] with ω hω
        simpa only [Real.norm_eq_abs,abs_of_nonneg (hAp ω)] using hω
      have h := bdg_two_moments P F hF hle hnull X A hX hA b hb hAi
      simpa [bdgUpperMomentConstant,bdgReverseMomentConstant] using ⟨h.1,hAi,h.2.2,h.2.1⟩
    · have hlarge : 2 < p := lt_of_le_of_ne (le_of_not_gt hsmall) (Ne.symm heq)
      obtain ⟨hx,hSi,hQi,hl⟩ := bdg_reverse_large_p_bounded P hT F hF hle hnull X A hX hA hAm hAc hA0
        p hlarge b hb K hK hbound L hL hXbound
      obtain ⟨hx',_,hu⟩ := bdg_upper_large_p_bounded P hT F hF hle hnull X A hX hA hAm hAc hA0
        p hlarge b hb K hK hbound L hL hXbound
      have he := runningMaximum_eq_path_norm X (hX.path P F) b hb hx
      have he' := runningMaximum_eq_path_norm X (hX.path P F) b hb hx'
      simp only [← he] at hSi hl
      simp only [← he'] at hu
      simpa only [bdgUpperMomentConstant,bdgReverseMomentConstant,if_neg hsmall,if_neg heq] using
        And.intro hSi (And.intro hQi (And.intro hu hl))

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.bdg_moment_constants_positive
#print axioms Asakura.Chapter3Complete.bounded_bdg_moments
