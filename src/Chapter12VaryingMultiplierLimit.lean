import Chapter12ChainLimit

open MeasureTheory Filter
open scoped ENNReal Topology
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

/-- A uniformly bounded scalar multiplier may vary with the Lp-convergent
vector factor. This is the second limit in the closed chain rule. -/
theorem varying_bounded_multiplier_Lp_limit {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hpt : p ≠ ⊤)
    (u : ℕ → Ω → H) (v : Ω → H) (hu : ∀ n, MemLp (u n) p P) (hv : MemLp v p P)
    (hut : Tendsto (fun n => eLpNorm (u n-v) p P) atTop (𝓝 0))
    (a : ℕ → Ω → ℝ) (b : Ω → ℝ)
    (ha : ∀ n, AEStronglyMeasurable (a n) P) (hb : AEStronglyMeasurable b P)
    (C : ℝ) (hC : 0 ≤ C)
    (hab : ∀ n, ∀ᵐ w ∂P, |a n w| ≤ C) (hbb : ∀ᵐ w ∂P, |b w| ≤ C)
    (ht : ∀ᵐ w ∂P, Tendsto (fun n => a n w) atTop (𝓝 (b w))) :
    Tendsto (fun n => eLpNorm (fun w => a n w • u n w-b w • v w) p P) atTop (𝓝 0) := by
  have hfixed := bounded_multiplier_Lp_limit P p hp hpt v hv a b ha hb C hC hab hbb ht
  let F := fun n w => a n w • (u n w-v w)
  have hbound n : eLpNorm (F n) p P ≤ ‖C‖ₑ*eLpNorm (u n-v) p P := by
    calc
      _ ≤ eLpNorm (C • (u n-v)) p P := eLpNorm_mono_ae
        ((ha n).smul ((hu n).aestronglyMeasurable.sub hv.aestronglyMeasurable)) (by
          filter_upwards [hab n] with w hw
          change ‖a n w • (u n w-v w)‖ ≤ ‖C • (u n w-v w)‖
          simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg hC]
          exact mul_le_mul_of_nonneg_right hw (norm_nonneg (u n w-v w)))
      _ = _ := eLpNorm_const_smul C (u n-v) p P
  have hsmall : Tendsto (fun n => eLpNorm (F n) p P) atTop (𝓝 0) := by
    have hh := ENNReal.Tendsto.const_mul (a := ‖C‖ₑ) hut (Or.inr (by simp))
    simp only [mul_zero] at hh
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hh
      (fun _ => bot_le) hbound
  have he n : (fun w => a n w • u n w-b w • v w) =
      F n+(fun w => a n w • v w-b w • v w) := by
    funext w
    dsimp only [F,Pi.add_apply]
    rw [smul_sub]
    abel
  have hsum : Tendsto (fun n => eLpNorm (F n) p P+
      eLpNorm (fun w => a n w • v w-b w • v w) p P) atTop (𝓝 0) := by
    simpa only [zero_add] using hsmall.add hfixed
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => bot_le)
  intro n
  dsimp only
  rw [he]
  exact eLpNorm_add_le hp

end Asakura.Chapter12
