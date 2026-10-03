import Chapter2LocalCovarianceRules
import FullAuditQVPolynomial

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/-- The increasing property of local quadratic variation is derived from
the actual bounded square compensators along localizers and uniqueness. -/
theorem local_quadratic_variation_monotone
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X C : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (hC : LocalCovarianceWitness P F X X C) :
    ∀ᵐ ω ∂P, MonotoneOn (fun t => C t ω) (Iio ⊤) := by
  obtain ⟨τ,ht,hm,htt,hc,hx⟩ := hX.localizers
  obtain ⟨Q,hQm,hQc,hQbv,hQM,hstop⟩ := local_covariation_exists_along_localizers
    P F hF hle hnull X X τ ht hm htt hc hx hx
  have hQ : LocalCovarianceWitness P F X X Q :=
    ⟨m2_localization_implies_local P F hF hle _ τ ht hm htt hc hQM,
      ⟨τ,ht,hm,htt,hc,hQbv⟩⟩
  have he := hC.unique P F hF hle hQ
  have hdiag (n) := bounded_cov_diagonal P F hF hle hnull ⟨_,hx n⟩
  filter_upwards [he,hstop,ae_all_iff.2 hdiag] with ω heω hsω hdω
  intro s hs t ht' hst
  obtain ⟨n,hn⟩ := hc ω t ht'
  have hsn : s ≤ τ n ω := hst.trans hn.le
  have hsQ := hsω n s
  have htQ := hsω n t
  simp only [min_eq_right hsn] at hsQ
  simp only [min_eq_right hn.le] at htQ
  change C s ω ≤ C t ω
  rw [heω s hs,heω t ht',hsQ,htQ,hdω n s,hdω n t]
  exact (boundedQV_properties P F hF hle hnull ⟨_,hx n⟩).2.2.1 ω hst

/-- Local witnesses retain the chapter's zero initial value. -/
theorem LocalMProcessWitness.initial
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    {X : ClosedTime T → Ω → ℝ} (hX : LocalMProcessWitness P F X) : X ⊥ =ᵐ[P] 0 := by
  obtain ⟨τ,_,_,_,_,hXτ⟩ := hX.localizers
  simpa only [min_bot_right] using (hXτ 0).1.initial

theorem local_quadratic_variation_initial
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (X C : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (hC : LocalCovarianceWitness P F X X C) : C ⊥ =ᵐ[P] 0 := by
  filter_upwards [hX.initial P F,hC.defect.initial P F] with ω hx hc
  simp only [hx,Pi.zero_apply,zero_mul,zero_sub,neg_eq_zero] at hc
  exact hc

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.local_quadratic_variation_monotone
#print axioms Asakura.Chapter2Complete.LocalMProcessWitness.initial
#print axioms Asakura.Chapter2Complete.local_quadratic_variation_initial
