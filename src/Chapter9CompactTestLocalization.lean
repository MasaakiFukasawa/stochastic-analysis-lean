import Chapter9StateExitLocalizers
import Chapter9StoppedGeneratorCutoff
import Chapter2LocalStopping

open MeasureTheory Set
open scoped ContDiff
namespace Asakura.Chapter9
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

noncomputable def reverseCompensated {Ω : Type*} {d : ℕ}
    (μ : Measure (Fin d → ℝ)) (T : ℝ) (Z : ℝ → Ω → Fin d → ℝ)
    (f : (Fin d → ℝ) → ℝ) (r : ℝ) (w : Ω) : ℝ :=
  f (Z r w)-f (Z 0 w)-∫ u in 0..r,ouReverseGenerator μ f (T-u,Z u w)

/-- Compact-test martingales imply the localized identities for every
 smooth function, in particular coordinates and coordinate products. -/
theorem compact_test_localization {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ}
    (μ : Measure (Fin d → ℝ)) (T b : ℝ) (hb : 0≤b)
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (Z : ℝ → Ω → Fin d → ℝ)
    (hm : ∀ t,Measurable[F t] (Z (finitePrefixTime b hb t).val))
    (hc : ∀ w,Continuous (fun t : HalfClosedTime => Z (finitePrefixTime b hb t).val w))
    (hM : ∀ f,ContDiff ℝ ∞ f → HasCompactSupport f →
      (fun (t : HalfClosedTime) w => reverseCompensated μ T Z f (finitePrefixTime b hb t).val w) ∈
        boundedMProcess P F)
    (q : (Fin d → ℝ) → ℝ) (hq : ContDiff ℝ ∞ q) :
    LocalMProcessWitness P F
      (fun t w => reverseCompensated μ T Z q (finitePrefixTime b hb t).val w) := by
  obtain ⟨τ,hτ,hmono,htop,hcofinal,houtside,hinside⟩ :=
    continuous_state_exit_localizers F hF (fun t w => Z (finitePrefixTime b hb t).val w) hm hc
  refine ⟨τ,hτ,hmono,htop,hcofinal,?_⟩
  intro n
  obtain ⟨f,hf,hfc,hnear⟩ := smooth_compact_replacement q hq (n:ℝ) (Nat.cast_nonneg n)
  have hs := bounded_martingale_stopped P F hF hle
    ⟨_,hM f hf hfc⟩ (τ n) (hτ n)
  have he : (fun t w => reverseCompensated μ T Z f (finitePrefixTime b hb (min (τ n w) t)).val w)=
      (fun t w => reverseCompensated μ T Z q (finitePrefixTime b hb (min (τ n w) t)).val w) := by
    funext t w
    apply stopped_generator_cutoff_identity μ (fun r => Z r w) T b (n:ℝ) hb f q hnear
    by_cases hw : ‖Z (finitePrefixTime (T := (⊤:EReal)) b hb ⊥).val w‖≤(n:ℝ)
    · exact Or.inr (hinside n w hw)
    · exact Or.inl (houtside n w (lt_of_not_ge hw))
  change (fun t w => reverseCompensated μ T Z f (finitePrefixTime b hb (min (τ n w) t)).val w) ∈ _ at hs
  rw [he] at hs
  exact hs
end Asakura.Chapter9
