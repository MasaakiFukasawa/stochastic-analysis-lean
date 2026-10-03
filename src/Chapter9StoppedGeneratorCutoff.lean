import Chapter9GeneratorCutoffs
import Chapter9FiniteIntervalMartingale
import Chapter5ClippedDriftIntegral

open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace Asakura.Chapter9
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter5
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

 theorem finite_prefix_bot (b : ℝ) (hb : 0≤b) :
    (finitePrefixTime (T := (⊤:EReal)) b hb ⊥).val=0 := by
  change (min (0:EReal) (b:EReal)).toReal=0
  rw [min_eq_left (by exact_mod_cast hb)]
  rfl

/-- Before the state exits the localization ball, the stopped compensated
 compact test equals the uncompacted coordinate or coordinate product. -/
theorem stopped_generator_cutoff_identity {d : ℕ}
    (μ : Measure (Fin d → ℝ)) (Z : ℝ → Fin d → ℝ)
    (T b R : ℝ) (hb : 0≤b) (f q : (Fin d → ℝ) → ℝ)
    (hnear : ∀ x,‖x‖≤R → f=ᶠ[𝓝 x] q)
    (τ t : HalfClosedTime)
    (hstop : τ=⊥ ∨ ∀ u≤τ,‖Z (finitePrefixTime b hb u).val‖≤R) :
    f (Z (finitePrefixTime b hb (min τ t)).val)-f (Z 0)-
      (∫ r in 0..(finitePrefixTime b hb (min τ t)).val,ouReverseGenerator μ f (T-r,Z r))=
    q (Z (finitePrefixTime b hb (min τ t)).val)-q (Z 0)-
      (∫ r in 0..(finitePrefixTime b hb (min τ t)).val,ouReverseGenerator μ q (T-r,Z r)) := by
  rcases hstop with rfl | hstop
  · simp only [min_bot_left,finite_prefix_bot,intervalIntegral.integral_same,sub_self,sub_zero]
  let p := fun u : HalfClosedTime => (finitePrefixTime b hb u).val
  have hzero : ‖Z 0‖≤R := by simpa only [finite_prefix_bot] using hstop ⊥ bot_le
  have hend : ‖Z (p (min τ t))‖≤R := hstop _ (min_le_left _ _)
  rw [(hnear _ hend).eq_of_nhds,(hnear _ hzero).eq_of_nhds]
  congr 1
  apply intervalIntegral.integral_congr_ae_restrict
  have hp : 0≤p (min τ t) := (finitePrefixTime b hb (min τ t)).property.1
  rw [uIoc_of_le hp]
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with r hr
  have hrb : r≤b := hr.2.trans (finitePrefixTime b hb (min τ t)).property.2
  have hpr : (finitePrefixTime (T := (⊤:EReal)) b hb (realTimeClamp r)).val=r := by
    rw [finite_prefix_time_min b r hb hr.1.le le_top,min_eq_left hrb]
  have htime : realTimeClamp r≤τ := by
    have hh : realTimeClamp (T := (⊤:EReal)) r≤realTimeClamp (p (min τ t)) := by
      change (realTimeClamp r:EReal)≤(realTimeClamp (p (min τ t)):EReal)
      rw [real_time_clamp_eq r hr.1.le le_top,real_time_clamp_eq _ hp le_top]
      exact EReal.coe_le_coe hr.2
    exact hh.trans ((by rw [finite_prefix_time_clamp b hb le_top];exact min_le_right _ _ :
      realTimeClamp (p (min τ t))≤min τ t).trans (min_le_left _ _))
  have hnorm : ‖Z r‖≤R := by simpa only [hpr] using hstop (realTimeClamp r) htime
  exact reverse_generator_congr_near μ (T-r) (hnear _ hnorm)
end Asakura.Chapter9
