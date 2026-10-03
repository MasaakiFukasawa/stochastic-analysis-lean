import Chapter12C1Approximation
import Chapter12DominatedLpLimit
import Chapter12ChainLimit
import Chapter12GraphClosure

open MeasureTheory Filter Set
open scoped ENNReal Topology ContDiff
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

/-- Smoothing a C1 outer function passes a smooth chain rule to the
closed graph. The dominating functions are derived from the bounded
derivative, not assumed for the approximations. -/
theorem bounded_C1_chain_by_closed_graph {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (D : Lp ℝ p P →ₗ.[ℝ] Lp H p P) (hD : D.IsClosed)
    (F : Ω → ℝ) (hF : Measurable F) (hFi : MemLp F p P)
    (u : Ω → H) (hu : MemLp u p P)
    (f df : ℝ → ℝ) (hd : ∀ x, HasDerivAt f (df x) x) (hdc : Continuous df)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ x, |df x| ≤ C)
    (hchain : ∀ (g dg : ℝ → ℝ), ContDiff ℝ ∞ g → (∀ x, HasDerivAt g (dg x) x) →
      (∀ k : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∃ a : ℕ, ∀ x,
        ‖iteratedFDeriv ℝ k g x‖ ≤ K*(1+‖x‖)^a) →
      ∀ (hi : MemLp (fun w => g (F w)) p P)
        (hdi : MemLp (fun w => dg (F w) • u w) p P),
      (hi.toLp _,hdi.toLp _) ∈ D.graph) :
    ∃ (hi : MemLp (fun w => f (F w)) p P)
      (hdi : MemLp (fun w => df (F w) • u w) p P),
      (hi.toLp _,hdi.toLp _) ∈ D.graph := by
  obtain ⟨g,dg,hg,hdg,hdb,hgb,hgrowth,ht,hdt⟩ := bounded_C1_smooth_approximation f df hd hdc C hC hb
  have hfc : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)
  have hdcg n : Continuous (dg n) := by
    have he : deriv (g n) = dg n := funext (fun x => (hdg n x).deriv)
    rw [← he]
    exact (hg n).continuous_deriv (by simp)
  let B := fun w => |f 0|+3*C*|F w|
  have hB : MemLp B p P := (memLp_const (μ := P) (p := p) |f 0|).add (hFi.norm.const_mul (3*C))
  have hBp w : 0 ≤ B w := by dsimp only [B]; positivity
  have hfb x : |f x| ≤ |f 0|+3*C*|x| :=
    le_of_tendsto ((ht x).abs) (Eventually.of_forall fun n => hgb n x)
  have hi : MemLp (fun w => f (F w)) p P := hB.of_le (hfc.measurable.comp hF).aestronglyMeasurable
    (ae_of_all P fun w => by simpa only [Real.norm_eq_abs,abs_of_nonneg (hBp w)] using hfb (F w))
  have hin n : MemLp (fun w => g n (F w)) p P := hB.of_le ((hg n).continuous.measurable.comp hF).aestronglyMeasurable
    (ae_of_all P fun w => by simpa only [Real.norm_eq_abs,abs_of_nonneg (hBp w)] using hgb n (F w))
  have hdi : MemLp (fun w => df (F w) • u w) p P := (hu.const_smul C).of_le
    ((hdc.measurable.comp hF).aestronglyMeasurable.smul hu.aestronglyMeasurable) (ae_of_all P fun w => by
      change ‖df (F w) • u w‖ ≤ ‖C • u w‖
      simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg hC]
      exact mul_le_mul_of_nonneg_right (hb (F w)) (norm_nonneg (u w)))
  have hdin n : MemLp (fun w => dg n (F w) • u w) p P := (hu.const_smul (3*C)).of_le
    (((hdcg n).measurable.comp hF).aestronglyMeasurable.smul hu.aestronglyMeasurable) (ae_of_all P fun w => by
      change ‖dg n (F w) • u w‖ ≤ ‖(3*C) • u w‖
      simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ 3*C by positivity)]
      exact mul_le_mul_of_nonneg_right (hdb n (F w)) (norm_nonneg (u w)))
  have hv := dominated_Lp_limit P p (Fact.out : 1 ≤ p) hp
    (fun n w => g n (F w)) (fun w => f (F w)) B hB
    (fun n => (hin n).aestronglyMeasurable) hi
    (fun n => ae_of_all P fun w => by
      simpa only [Real.norm_eq_abs,abs_of_nonneg (hBp w)] using hgb n (F w))
    (ae_of_all P fun w => ht (F w))
  have hder := bounded_multiplier_Lp_limit P p (Fact.out : 1 ≤ p) hp u hu
    (fun n w => dg n (F w)) (fun w => df (F w))
    (fun n => ((hdcg n).measurable.comp hF).aestronglyMeasurable)
    ((hdc.measurable.comp hF).aestronglyMeasurable) (3*C) (by positivity)
    (fun n => ae_of_all P fun w => hdb n (F w))
    (ae_of_all P fun w => (hb (F w)).trans (by linarith)) (ae_of_all P fun w => hdt (F w))
  refine ⟨hi,hdi,?_⟩
  apply hD.mem_of_tendsto (((Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ hin _ hi).mpr hv).prodMk_nhds
    ((Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ hdin _ hdi).mpr hder))
  exact Eventually.of_forall fun n => hchain (g n) (dg n) (hg n) (hdg n) (hgrowth n) (hin n) (hdin n)

end Asakura.Chapter12
