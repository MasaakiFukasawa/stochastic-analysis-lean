import Chapter2EnergyNorm
import FullAuditLpComplete

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- (i) => (ii) of prop244. The path supremum is represented by the norm
of a continuous map. Localized Doob bounds and Fatou give its L2 membership. -/
theorem local_stop_path_memLp_of_integrable_variation
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X C : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (hC : LocalCovarianceWitness P F X X C)
    (σ : Ω → ClosedTime T) (hσ : ∀ t, MeasurableSet[F t] {ω | σ ω ≤ t})
    (hσtop : ∀ ω, σ ω < ⊤) (hCi : Integrable (fun ω => C (σ ω) ω) P) :
    ∃ hc : ∀ ω, Continuous (fun t => X (min (σ ω) t) ω),
      MemLp (continuousPath (fun t ω => X (min (σ ω) t) ω) hc) 2 P ∧
      eLpNorm (continuousPath (fun t ω => X (min (σ ω) t) ω) hc) 2 P ≤
        2 * (ENNReal.ofReal (∫ ω, C (σ ω) ω ∂P)) ^ (1/(2:ℝ)) := by
  obtain ⟨τ,ht,htm,htt,htc,hx⟩ := hX.localizers
  obtain ⟨ρ,hr,hrm,hrt,hrc,hd⟩ := hC.defect.localizers
  let κ := fun n ω => min (τ n ω) (ρ n ω)
  have hκm (ω) : Monotone (fun n => κ n ω) := (htm ω).min (hrm ω)
  have hκc (ω t) (htop : t < ⊤) : ∃ n, t < κ n ω :=
    (common_localizers_cofinal (fun n => τ n ω) (fun n => ρ n ω)
      (htm ω) (hrm ω) (htc ω) (hrc ω)).2 t htop
  have hκtop (n ω) : κ n ω < ⊤ := (min_le_left _ _).trans_lt (htt n ω)
  let Z := fun n t ω => X (min (κ n ω) (min (σ ω) t)) ω
  let D := fun n t ω => X (min (κ n ω) (min (σ ω) t)) ω *
      X (min (κ n ω) (min (σ ω) t)) ω-C (min (κ n ω) (min (σ ω) t)) ω
  have hZ (n) : ContinuousM2Witness P F (Z n) :=
    continuous_m2_stopped P F hF hle _
      (bounded_at_minimum P F hF hle X (τ n) (ρ n) (hr n) (hx n)).1 σ hσ
  have hD (n) : ContinuousM2Witness P F (D n) := by
    have h := bounded_at_minimum P F hF hle (fun t ω => X t ω*X t ω-C t ω)
      (ρ n) (τ n) (ht n) (hd n)
    have hh := continuous_m2_stopped P F hF hle _ h.1 σ hσ
    simpa only [D,κ,min_comm] using hh
  let q := fun n ω => C (min (κ n ω) (σ ω)) ω
  have hsq (n) : Integrable (fun ω => Z n ⊤ ω ^ 2) P :=
    (memLp_two_iff_integrable_sq ((hZ n).moment ⊤).aestronglyMeasurable).1 ((hZ n).moment ⊤)
  have hqi (n) : Integrable (q n) P := by
    have hi := (hsq n).sub (((hD n).moment ⊤).integrable (by norm_num))
    convert hi using 1
    funext ω
    simp only [q,Z,D,min_top_right,Pi.sub_apply]
    ring
  have henergy (n) : (∫ ω, q n ω ∂P) = ∫ ω, Z n ⊤ ω ^ 2 ∂P := by
    have h := integral_congr_ae (((hD n).martingale ⊥ ⊤ le_top).trans (hD n).initial)
    rw [integral_condExp (hle ⊥)] at h
    have hid : D n ⊤ = (fun ω => Z n ⊤ ω ^ 2-q n ω) := by
      funext ω
      simp only [D,Z,q,min_top_right]
      ring
    rw [hid,integral_sub (hsq n) (hqi n)] at h
    simp only [Pi.zero_apply,integral_zero] at h
    linarith
  have he (ω) : ∀ᶠ n in atTop, min (κ n ω) (σ ω) = σ ω := by
    obtain ⟨n,hn⟩ := hκc ω (σ ω) (hσtop ω)
    exact eventually_atTop.2 ⟨n,fun k hk => min_eq_right (hn.le.trans (hκm ω hk))⟩

  let Y := fun t ω => X (min (σ ω) t) ω
  have hYc (ω) : Continuous (fun t => Y t ω) := by
    apply continuous_iff_continuousAt.2
    intro t
    exact (hX.path P F ω _ ((min_le_left _ _).trans_lt (hσtop ω))).comp
      (continuous_const.min continuous_id).continuousAt
  have hconv (ω) : ∀ᶠ n in atTop, continuousPath (Z n) (hZ n).path ω = continuousPath Y hYc ω := by
    filter_upwards [he ω] with n hn
    apply ContinuousMap.ext
    intro t
    change X (min (κ n ω) (min (σ ω) t)) ω = X (min (σ ω) t) ω
    rw [← min_assoc,hn]
  have hmZ (n) := continuous_path_measurable (Z n) (hZ n).path
    (fun t => ((hZ n).adapted t).mono (hle t) le_rfl)
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun n => continuousPath (Z n) (hZ n).path ω) atTop
      (𝓝 (continuousPath Y hYc ω)) :=
    .of_forall fun ω => tendsto_const_nhds.congr' ((hconv ω).mono fun n hn => hn.symm)
  have hmY := aestronglyMeasurable_of_tendsto_ae _ (fun n => (hmZ n).aestronglyMeasurable) hlim
  have hmono := local_quadratic_variation_monotone P F hF hle hnull X C hX hC
  have hqle (n) : q n ≤ᵐ[P] (fun ω => C (σ ω) ω) := by
    filter_upwards [hmono] with ω hm
    exact hm ((min_le_left _ _).trans_lt (hκtop n ω)) (hσtop ω) (min_le_right _ _)
  have hnorm (n) : eLpNorm (continuousPath (Z n) (hZ n).path) 2 P ≤
      2 * (ENNReal.ofReal (∫ ω, C (σ ω) ω ∂P)) ^ (1/(2:ℝ)) := by
    have hd := continuous_martingale_path_norm P F hF hle (Z n)
      (hZ n).adapted (hZ n).moment (hZ n).path (hZ n).martingale
    rw [real_eLpNorm_two_energy P (Z n ⊤) ((hZ n).moment ⊤),← henergy n] at hd
    exact hd.trans (mul_le_mul' le_rfl (ENNReal.rpow_le_rpow
      (ENNReal.ofReal_le_ofReal (integral_mono_ae (hqi n) hCi (hqle n))) (by norm_num)))
  have hnormY := current_lp_eLpNorm_le_of_ae_tendsto (.of_forall hnorm)
    (fun n => (hmZ n).aestronglyMeasurable) hmY hlim
  refine ⟨hYc,?_,hnormY⟩
  exact hnormY.trans_lt (ENNReal.mul_lt_top (by norm_num)
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top))

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.local_stop_path_memLp_of_integrable_variation
