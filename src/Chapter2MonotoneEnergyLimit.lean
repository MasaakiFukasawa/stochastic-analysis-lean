import Chapter2ConditionalFatou

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
set_option maxHeartbeats 600000

/-- Monotone convergence also proves integrability of the limit when the
integrals have a finite real limit. This is the energy step of prop244. -/
theorem integrable_monotone_limit_of_integral_limit
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (f : ℕ → Ω → ℝ) (v : Ω → ℝ) (a : ℝ)
    (hi : ∀ n, Integrable (f n) P) (hn : ∀ n, 0 ≤ᵐ[P] f n)
    (hm : ∀ᵐ ω ∂P, Monotone (fun n => f n ω))
    (hv : ∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 (v ω)))
    (hInt : Tendsto (fun n => ∫ ω, f n ω ∂P) atTop (𝓝 a)) :
    Integrable v P ∧ (∫ ω, v ω ∂P) = a := by
  have hvn : 0 ≤ᵐ[P] v := by
    filter_upwards [hv,ae_all_iff.2 hn] with ω hω hnω
    exact ge_of_tendsto' hω hnω
  have hvm := aestronglyMeasurable_of_tendsto_ae _ (fun n => (hi n).aestronglyMeasurable) hv
  have hmass := lintegral_tendsto_of_tendsto_of_monotone
    (μ := P) (fun n => (hi n).aemeasurable.ennreal_ofReal)
    (hm.mono fun ω hω n k hnk => ENNReal.ofReal_le_ofReal (hω hnk))
    (hv.mono fun ω hω => ENNReal.continuous_ofReal.continuousAt.tendsto.comp hω)
  have he : (∫⁻ ω, ENNReal.ofReal (v ω) ∂P) = ENNReal.ofReal a := by
    have hlim := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hInt
    have hid (n) := ofReal_integral_eq_lintegral_ofReal (hi n) (hn n)
    simp only [Function.comp_def,hid] at hlim
    exact tendsto_nhds_unique hmass hlim
  have hvi : Integrable v P := ⟨hvm,(hasFiniteIntegral_iff_ofReal hvn).2 (by rw [he]; exact ENNReal.ofReal_lt_top)⟩
  exact ⟨hvi,tendsto_nhds_unique
    (integral_tendsto_of_tendsto_of_monotone hi hvi hm hv) hInt⟩

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.integrable_monotone_limit_of_integral_limit
