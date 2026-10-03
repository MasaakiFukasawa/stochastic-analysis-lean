import Chapter3PositiveVariationIntegral
import Chapter3RegularizedWeightRegularity

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- A lower bound for an actual Stieltjes integral from a lower bound on its integrand. -/
theorem positive_variation_integral_lower_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {T : EReal} [Fact (0 ≤ T)]
    (A I : ClosedTime T → Ω → ℝ) (H : Ω × ℝ → ℝ) (w : Ω → ℝ)
    (hAm : ∀ ω, MonotoneOn (fun t => A t ω) (Iio ⊤))
    (hAc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => A s ω) t)
    (hHc : ∀ d : ℝ, 0 ≤ d → (d:EReal) < T → ∀ ω, ContinuousOn (fun r => H (ω,r)) (Icc 0 d))
    (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (hcT : ∀ n, (c n:EReal) < T)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < realTimeClamp (T := T) (c n))
    (hI : VariationIntegralFormula P c hc A H I)
    (b : ClosedTime T) (hb : b < ⊤)
    (hbound : ∀ ω (r : ℝ), 0 ≤ r → (r:EReal) < T → realTimeClamp r ≤ b → w ω ≤ H (ω,r)) :
    ∀ᵐ ω ∂P, w ω*(A b ω-A ⊥ ω) ≤ I b ω := by
  obtain ⟨d,hd,hdT,hdb⟩ := finite_closed_time_real b hb
  obtain ⟨j,hj⟩ := hcc b hb
  have hdc : d ≤ c j := by
    rw [← hdb] at hj
    change (realTimeClamp d : EReal) < (realTimeClamp (c j) : EReal) at hj
    rw [real_time_clamp_eq d hd hdT.le,real_time_clamp_eq (c j) (hc j) (hcT j).le] at hj
    exact (EReal.coe_le_coe_iff.mp hj.le)
  have hreg n := regular_covariance_on_real_intervals A hAm hAc (c n) (hc n) (hcT n)
  have hdreg := regular_covariance_on_real_intervals A hAm hAc d hd hdT
  have heI := positive_variation_integral_at_time P A I H c hc hcT (fun n => (hreg n).1)
    (fun n => (hreg n).2) hI j d hd hdc hdreg.1 hdreg.2
  filter_upwards [heI] with ω hi
  rw [hdb] at hi
  rw [hi]
  let μ := (intervalStieltjes 0 d hd (fun r => A (realTimeClamp r) ω) (hdreg.1 ω)
    (fun r hr => (hdreg.2 ω r hr).mono inter_subset_left)).measure
  letI : IsFiniteMeasure μ := intervalStieltjes_finite _ _ _ _ _ _
  have hs : ∀ᵐ r ∂μ, r ∈ Icc 0 d :=
    (interval_stieltjes_ae_mem_Ioc _ _ _ _ _ _).mono (fun r hr => ⟨hr.1.le,hr.2⟩)
  have hHi := continuous_integrable_compact_support μ 0 d (fun r => H (ω,r)) (hHc d hd hdT ω) hs
  have hmass : μ.real univ = A b ω-A ⊥ ω := by
    dsimp [μ]
    rw [Measure.real,interval_stieltjes_total_mass 0 d hd (fun ω r => A (realTimeClamp r) ω)
      hdreg.1 (fun ω r hr => (hdreg.2 ω r hr).mono inter_subset_left),hdb]
    have hz : realTimeClamp (T := T) 0 = ⊥ := by
      apply Subtype.ext
      exact real_time_clamp_eq 0 le_rfl (Fact.out : (0:EReal) ≤ T)
    rw [hz,ENNReal.toReal_ofReal (sub_nonneg.mpr (hAm ω (by exact lt_of_le_of_lt bot_le hb) hb bot_le))]
  calc
    _ = ∫ r, w ω ∂μ := by rw [integral_const,smul_eq_mul,hmass]; ring
    _ ≤ _ := integral_mono_ae (integrable_const _) hHi (hs.mono (fun r hr =>
      hbound ω r hr.1 ((EReal.coe_le_coe hr.2).trans_lt hdT)
        (by rw [← hdb]; exact real_time_clamp_mono hr.2)))

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.positive_variation_integral_lower_bound
