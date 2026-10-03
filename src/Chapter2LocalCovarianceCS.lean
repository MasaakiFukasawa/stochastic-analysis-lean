import Chapter2LocalCovarianceIdentification
import FullAuditCovarianceIntervals

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

/-- The local interval Cauchy-Schwarz bound, for the actual constructed
covariations and one common exceptional null set. -/
theorem local_covariance_interval_cs
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X Y A B C : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X) (hY : LocalMProcessWitness P F Y)
    (hA : LocalCovarianceWitness P F X X A) (hB : LocalCovarianceWitness P F Y Y B)
    (hC : LocalCovarianceWitness P F X Y C) :
    ∀ᵐ ω ∂P, ∀ s t, s ≤ t → t < ⊤ →
      |C t ω-C s ω| ≤ Real.sqrt (A t ω-A s ω)*Real.sqrt (B t ω-B s ω) := by
  obtain ⟨τ,ht,htm,htt,htc,hx⟩ := hX.localizers
  obtain ⟨σ,hs,hsm,hst,hsc,hy⟩ := hY.localizers
  let κ := fun n ω => min (τ n ω) (σ n ω)
  have hk (n) : ∀ t, MeasurableSet[F t] {ω | κ n ω ≤ t} :=
    (written_stopping_min_max F (τ n) (σ n) (ht n) (hs n)).1
  have hkm (ω) : Monotone (fun n => κ n ω) := (htm ω).min (hsm ω)
  have hkt (n ω) : κ n ω < ⊤ := (min_le_left _ _).trans_lt (htt n ω)
  have hkc (ω t) (htop : t < ⊤) : ∃ n, t < κ n ω :=
    (common_localizers_cofinal (fun n => τ n ω) (fun n => σ n ω)
      (htm ω) (hsm ω) (htc ω) (hsc ω)).2 t htop
  have hxk (n) : (fun t ω => X (min (κ n ω) t) ω) ∈ boundedMProcess P F :=
    bounded_at_minimum P F hF hle X (τ n) (σ n) (hs n) (hx n)
  have hyk (n) : (fun t ω => Y (min (κ n ω) t) ω) ∈ boundedMProcess P F := by
    simpa only [κ,min_comm] using bounded_at_minimum P F hF hle Y (σ n) (τ n) (ht n) (hy n)
  let Xk (n) : boundedMProcess P F := ⟨_,hxk n⟩
  let Yk (n) : boundedMProcess P F := ⟨_,hyk n⟩
  have ha := local_covariance_matches_bounded_localizers P F hF hle hnull X X A hA κ hk hkm hkt hkc hxk hxk
  have hb := local_covariance_matches_bounded_localizers P F hF hle hnull Y Y B hB κ hk hkm hkt hkc hyk hyk
  have hc := local_covariance_matches_bounded_localizers P F hF hle hnull X Y C hC κ hk hkm hkt hkc hxk hyk
  have hdX (n) := bounded_cov_diagonal P F hF hle hnull (Xk n)
  have hdY (n) := bounded_cov_diagonal P F hF hle hnull (Yk n)
  have hkw n := bounded_cov_interval_cs P F hF hle hnull (Xk n) (Yk n)
  filter_upwards [ha,hb,hc,ae_all_iff.2 hdX,ae_all_iff.2 hdY,ae_all_iff.2 hkw]
    with ω haω hbω hcω hdXω hdYω hkwω
  intro s t hst ht
  obtain ⟨n,hn⟩ := hkc ω t ht
  have hAe r (hr : r ≤ t) : A r ω = boundedQV P F hF hle hnull (Xk n) r ω := by
    have h := haω n r
    rw [min_eq_right (hr.trans hn.le)] at h
    exact h.trans (hdXω n r)
  have hBe r (hr : r ≤ t) : B r ω = boundedQV P F hF hle hnull (Yk n) r ω := by
    have h := hbω n r
    rw [min_eq_right (hr.trans hn.le)] at h
    exact h.trans (hdYω n r)
  have hCe r (hr : r ≤ t) : C r ω = boundedCov P F hF hle hnull (Xk n) (Yk n) r ω := by
    have h := hcω n r
    simpa only [min_eq_right (hr.trans hn.le)] using h
  rw [hAe t le_rfl,hAe s hst,hBe t le_rfl,hBe s hst,hCe t le_rfl,hCe s hst]
  exact hkwω n s t hst

/-- The pointwise bound used to pass covariance identities to limits. -/
theorem local_covariance_point_cs
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X Y A B C : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X) (hY : LocalMProcessWitness P F Y)
    (hA : LocalCovarianceWitness P F X X A) (hB : LocalCovarianceWitness P F Y Y B)
    (hC : LocalCovarianceWitness P F X Y C) :
    ∀ᵐ ω ∂P, ∀ t, t < ⊤ → |C t ω| ≤ Real.sqrt (A t ω)*Real.sqrt (B t ω) := by
  have hi := local_covariance_interval_cs P F hF hle hnull X Y A B C hX hY hA hB hC
  have hc0 : C ⊥ =ᵐ[P] 0 := by
    filter_upwards [hX.initial P F,hY.initial P F,hC.defect.initial P F] with ω hx hy hd
    change X ⊥ ω*Y ⊥ ω-C ⊥ ω = 0 at hd
    change C ⊥ ω = 0
    simpa only [hx,Pi.zero_apply,zero_mul,zero_sub,neg_eq_zero] using hd
  filter_upwards [hi,local_quadratic_variation_initial P F X A hX hA,
    local_quadratic_variation_initial P F Y B hY hB,hc0] with ω hω ha hb hc
  intro t ht
  have h := hω ⊥ t bot_le ht
  simpa only [ha,hb,hc,Pi.zero_apply,sub_zero] using h

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.local_covariance_interval_cs
#print axioms Asakura.Chapter2Complete.local_covariance_point_cs
