import Chapter7FiniteTimeCLT

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter4
set_option maxHeartbeats 1800000

/-- The degenerate horizon consists of one point. Zero initial values give
the Dirac law at the zero path for every n and for Brownian motion. -/
theorem zero_horizon_path_limit
    {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
    (P : Measure Ω) (Q : Measure Γ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (X : ℕ → Ω → C(Icc (0:ℝ≥0) 0,ℝ))
    (hX : ∀ n,∀ᵐ w ∂P,X n w ⟨0,by simp⟩ = 0)
    (B : BrownianSystem Q 1) :
    TendstoInDistribution X atTop (fun z => pathRestriction 0 (brownianContinuousPath B z)) (fun _ => P) Q := by
  have hx n : X n =ᵐ[P] fun _ => (0 : C(Icc (0:ℝ≥0) 0,ℝ)) := by
    filter_upwards [hX n] with w hw
    ext t
    have ht : t = ⟨0,by simp⟩ := Subtype.ext (le_antisymm t.property.2 t.property.1)
    simpa only [ht,ContinuousMap.zero_apply] using hw
  have hb : (fun z => pathRestriction 0 (brownianContinuousPath B z)) =ᵐ[Q]
      fun _ => (0 : C(Icc (0:ℝ≥0) 0,ℝ)) := by
    filter_upwards [(B.martingale 0).initial Q B.F] with w hw
    ext t
    have ht : t.val = 0 := le_antisymm t.property.2 t.property.1
    change B.W 0 (realTimeClamp t.val) w = 0
    rw [ht]
    have hz : (realTimeClamp (T := (⊤:EReal)) 0 : HalfClosedTime) = ⊥ := by
      apply Subtype.ext
      exact real_time_clamp_eq 0 le_rfl le_top
    change B.W 0 (realTimeClamp (0:ℝ)) w = 0
    rw [hz]
    exact hw
  have hxm n : AEMeasurable (X n) P := aemeasurable_const.congr (hx n).symm
  have hbm : AEMeasurable (fun z => pathRestriction 0 (brownianContinuousPath B z)) Q := aemeasurable_const.congr hb.symm
  apply (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ hxm hbm).mpr
  intro f
  have he n : (∫ w,f (X n w) ∂P) = f 0 := by
    rw [integral_congr_ae ((hx n).mono fun w hw => congrArg f hw)]
    simp
  have heB : (∫ w,f (pathRestriction 0 (brownianContinuousPath B w)) ∂Q) = f 0 := by
    rw [integral_congr_ae (hb.mono fun w hw => congrArg f hw)]
    simp
  simp only [he,heB]
  exact tendsto_const_nhds

end Asakura.Chapter7
