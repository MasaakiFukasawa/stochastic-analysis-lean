import FullAuditBayes

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.FullAudit
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

/-- Fatou applied to the localized wealth plus its fixed lower bound.
 This derives terminal integrability rather than assuming it. -/
theorem localized_wealth_fatou {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q] (Y : ℕ → Ω → ℝ) (V : Ω → ℝ)
    (hY : ∀ n, Integrable (Y n) Q) (hmean : ∀ n, (∫ ω, Y n ω ∂Q) = 0)
    (a : ℝ) (hbound : ∀ n, ∀ᵐ ω ∂Q, -a ≤ Y n ω)
    (hlim : ∀ᵐ ω ∂Q, Tendsto (fun n => Y n ω) atTop (nhds (V ω))) :
    Integrable V Q ∧ (∫ ω, V ω ∂Q) ≤ 0 := by
  let F := fun n ω => a+Y n ω
  let v := fun ω => a+V ω
  have hFi (n : ℕ) : Integrable (F n) Q := (integrable_const a).add (hY n)
  have hFn (n : ℕ) : 0 ≤ᵐ[Q] F n := by
    filter_upwards [hbound n] with ω hω
    dsimp [F]
    linarith
  have hFlim : ∀ᵐ ω ∂Q, Tendsto (fun n => F n ω) atTop (nhds (v ω)) := by
    filter_upwards [hlim] with ω hω
    exact tendsto_const_nhds.add hω
  have hvn : 0 ≤ᵐ[Q] v := by
    filter_upwards [hFlim,ae_all_iff.mpr hFn] with ω hl hn
    exact ge_of_tendsto' hl hn
  have hvm : AEStronglyMeasurable v Q :=
    aestronglyMeasurable_of_tendsto_ae _ (fun n => (hFi n).aestronglyMeasurable) hFlim
  have hmass (n : ℕ) : (∫⁻ ω, ENNReal.ofReal (F n ω) ∂Q) = ENNReal.ofReal a := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hFi n) (hFn n)]
    simp only [F,integral_add (integrable_const a) (hY n),integral_const,probReal_univ,
      one_smul,hmean n,add_zero]
  have hfatou : (∫⁻ ω, ENNReal.ofReal (v ω) ∂Q) ≤ ENNReal.ofReal a := by
    have he : (∫⁻ ω, ENNReal.ofReal (v ω) ∂Q) =
        ∫⁻ ω, liminf (fun n => ENNReal.ofReal (F n ω)) atTop ∂Q := by
      apply lintegral_congr_ae
      filter_upwards [hFlim] with ω hω
      exact ((ENNReal.continuous_ofReal.tendsto (v ω)).comp hω).liminf_eq.symm
    rw [he]
    have h := lintegral_liminf_le' (u := (atTop : Filter ℕ)) (fun n => (hFi n).aemeasurable.ennreal_ofReal)
    simpa only [hmass,liminf_const] using h
  have hvi : Integrable v Q := ⟨hvm,(hasFiniteIntegral_iff_ofReal hvn).mpr
    (lt_of_le_of_lt hfatou ENNReal.ofReal_lt_top)⟩
  have hVi : Integrable V Q := by
    have h := hvi.sub (integrable_const a)
    change Integrable (fun ω => (a+V ω)-a) Q at h
    simpa only [add_sub_cancel_left] using h
  have hle : (∫ ω, v ω ∂Q) ≤ a := by
    rw [← ofReal_integral_eq_lintegral_ofReal hvi hvn] at hfatou
    have ha : 0 ≤ a := by
      have hz := integral_nonneg_of_ae (hFn 0)
      simpa only [F,integral_add (integrable_const a) (hY 0),integral_const,probReal_univ,
        one_smul,hmean 0,add_zero] using hz
    exact (ENNReal.ofReal_le_ofReal_iff ha).mp hfatou
  refine ⟨hVi,?_⟩
  simp only [v,integral_add (integrable_const a) hVi,integral_const,probReal_univ,one_smul] at hle
  linarith

/-- A nonnegative terminal payoff of a lower-bounded localized zero-cost
 wealth must vanish. Absolute continuity transfers this from Q back to P. -/
theorem no_arbitrage_from_localized_wealth {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure Q] (hPQ : P ≪ Q)
    (Y : ℕ → Ω → ℝ) (V : Ω → ℝ)
    (hY : ∀ n, Integrable (Y n) Q) (hmean : ∀ n, (∫ ω, Y n ω ∂Q) = 0)
    (a : ℝ) (hbound : ∀ n, ∀ᵐ ω ∂Q, -a ≤ Y n ω)
    (hlim : ∀ᵐ ω ∂Q, Tendsto (fun n => Y n ω) atTop (nhds (V ω)))
    (hnonneg : 0 ≤ᵐ[Q] V) : V =ᵐ[P] 0 := by
  obtain ⟨hi,hle⟩ := localized_wealth_fatou Q Y V hY hmean a hbound hlim
  have hz : (∫ ω, V ω ∂Q) = 0 := le_antisymm hle (integral_nonneg_of_ae hnonneg)
  have hzero := (integral_eq_zero_iff_of_nonneg_ae hnonneg hi).mp hz
  exact hPQ.ae_le hzero

end Asakura.FullAudit
