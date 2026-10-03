import Chapter2OrthogonalFiniteVariation

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter2Written
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/-- Reindex the already proved finite-variation martingale theorem to a
finite real time interval, as used by the integrand density argument. -/
theorem real_finite_variation_zero_of_orthogonal_past_tests
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (b : ℝ) (hb : 0 < b) [Fact (0 ≤ b)]
    (F : Icc (0:ℝ) b → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (N : Icc (0:ℝ) b → Ω → ℝ) (hm : ∀ t, Measurable[F t] (N t))
    (h2 : ∀ t, MemLp (N t) 2 P) (hc : ∀ ω, Continuous (fun t => N t ω))
    (hBV : ∀ ω, ∃ U V : Icc (0:ℝ) b → ℝ, Monotone U ∧ Monotone V ∧ ∀ t, N t ω = U t-V t)
    (hz : N ⊥ =ᵐ[P] 0)
    (horth : ∀ s t, s ≤ t → ∀ Z : Ω → ℝ,
      Measurable[F s] Z → MemLp Z ∞ P → (∫ ω, Z ω * (N t ω-N s ω) ∂P) = 0) :
    ∀ᵐ ω ∂P, ∀ t, N t ω = 0 := by
  letI : Fact (0 ≤ (1:EReal)) := ⟨by norm_num⟩
  let e : ClosedTime (1:EReal) ≃o Icc (0:ℝ) b :=
    (closedTimeUnitIso (by norm_num : (0:EReal) < 1)).symm.trans (positiveIntervalScale b hb)
  have hc' (ω) : Continuous (fun t => N (e t) ω) := (hc ω).comp e.continuous
  have hv' (ω) : ∃ U V : ClosedTime (1:EReal) → ℝ, Monotone U ∧ Monotone V ∧
      ∀ t, N (e t) ω = U t-V t := by
    obtain ⟨U,V,hU,hV,hUV⟩ := hBV ω
    exact ⟨U ∘ e,V ∘ e,hU.comp e.monotone,hV.comp e.monotone,fun t => hUV (e t)⟩
  have hz' : (fun ω => N (e ⊥) ω) =ᵐ[P] 0 := by simpa only [e.map_bot] using hz
  have h := finite_variation_zero_of_orthogonal_past_tests P (fun t => F (e t))
    (hF.comp e.monotone) (fun t => hle (e t)) (fun t => N (e t))
    (fun t => hm (e t)) (fun t => h2 (e t)) hc' hv' hz'
    (fun s t hst Z hZ hZ2 => horth (e s) (e t) (e.monotone hst) Z hZ hZ2)
  filter_upwards [h] with ω hω
  intro t
  simpa only [e.apply_symm_apply] using hω (e.symm t)

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.real_finite_variation_zero_of_orthogonal_past_tests
