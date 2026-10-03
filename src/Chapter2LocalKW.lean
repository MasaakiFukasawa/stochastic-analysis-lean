import Chapter2LocalCovarianceIdentification
import FullAuditBoundedKW

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- Local Kunita-Watanabe, on all finite intervals simultaneously. The
measures are identified by interval increments of the actual local
quadratic variations and covariance; total variation is retained. -/
theorem local_kw_stieltjes
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X Y A B C : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X) (hY : LocalMProcessWitness P F Y)
    (hA : LocalCovarianceWitness P F X X A) (hB : LocalCovarianceWitness P F Y Y B)
    (hC : LocalCovarianceWitness P F X Y C) :
    ∀ᵐ ω ∂P, ∀ b : ℝ, 0 ≤ b → (b:EReal) < T →
      ∃ (α β : Measure ℝ) (ν : SignedMeasure ℝ),
      IsFiniteMeasure α ∧ IsFiniteMeasure β ∧
      (∀ s t, 0 ≤ s → s ≤ t → t ≤ b →
        α.real (Ioc s t) = A (realTimeClamp t) ω-A (realTimeClamp s) ω ∧
        β.real (Ioc s t) = B (realTimeClamp t) ω-B (realTimeClamp s) ω ∧
        ν (Ioc s t) = C (realTimeClamp t) ω-C (realTimeClamp s) ω) ∧
      (∀ f g : ℝ → ℝ, Measurable f → Measurable g →
        (∫⁻ x, ENNReal.ofReal |f x*g x| ∂ν.totalVariation) ≤
          (∫⁻ x, ENNReal.ofReal (f x^2) ∂α)^(1/2:ℝ)*
          (∫⁻ x, ENNReal.ofReal (g x^2) ∂β)^(1/2:ℝ)) := by
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
  have hkw (n) := bounded_kw_stieltjes P F hF hle hnull (Xk n) (Yk n)
  filter_upwards [ha,hb,hc,ae_all_iff.2 hdX,ae_all_iff.2 hdY,ae_all_iff.2 hkw]
    with ω haω hbω hcω hdXω hdYω hkwω
  intro b hb0 hbT
  have hbtop : realTimeClamp (T := T) b < ⊤ := by
    change (realTimeClamp b : EReal) < T
    rw [real_time_clamp_eq b hb0 hbT.le]
    exact hbT
  obtain ⟨n,hn⟩ := hkc ω (realTimeClamp b) hbtop
  obtain ⟨α,β,ν,hα,hβ,hi,hineq⟩ := hkwω n b hb0
  have hrt (r : ℝ) (hr : r ≤ b) : realTimeClamp r ≤ κ n ω :=
    (real_time_clamp_mono hr).trans hn.le
  have hAe (r : ℝ) (hr : r ≤ b) : A (realTimeClamp r) ω =
      boundedQV P F hF hle hnull (Xk n) (realTimeClamp r) ω := by
    have hh := haω n (realTimeClamp r)
    rw [min_eq_right (hrt r hr)] at hh
    exact hh.trans (hdXω n _)
  have hBe (r : ℝ) (hr : r ≤ b) : B (realTimeClamp r) ω =
      boundedQV P F hF hle hnull (Yk n) (realTimeClamp r) ω := by
    have hh := hbω n (realTimeClamp r)
    rw [min_eq_right (hrt r hr)] at hh
    exact hh.trans (hdYω n _)
  have hCe (r : ℝ) (hr : r ≤ b) : C (realTimeClamp r) ω =
      boundedCov P F hF hle hnull (Xk n) (Yk n) (realTimeClamp r) ω := by
    have hh := hcω n (realTimeClamp r)
    simpa only [min_eq_right (hrt r hr)] using hh
  refine ⟨α,β,ν,hα,hβ,?_,hineq⟩
  intro s t hs0 hst htb
  rw [hAe t htb,hAe s (hst.trans htb),hBe t htb,hBe s (hst.trans htb),hCe t htb,hCe s (hst.trans htb)]
  exact hi s t hs0 hst htb

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.local_kw_stieltjes
