import Chapter2MonotoneEnergyLimit
import Chapter2LocalQuadraticVariation
import Chapter2SquareIntegrableStop

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false

/-- The energy equality in (ii) => (iii) of prop244, from actual local
quadratic variation. Dominated convergence handles the squares, and
monotone convergence proves integrability of the quadratic variation. -/
theorem stopped_local_energy_of_square_integrable_bound
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X C : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (hC : LocalCovarianceWitness P F X X C)
    (σ : Ω → ClosedTime T) (hσ : ∀ t, MeasurableSet[F t] {ω | σ ω ≤ t})
    (hσtop : ∀ ω, σ ω < ⊤)
    (B : Ω → ℝ) (hB : MemLp B 2 P)
    (hbound : ∀ᵐ ω ∂P, ∀ t, ‖X (min (σ ω) t) ω‖ ≤ B ω) :
    Integrable (fun ω => C (σ ω) ω) P ∧
    (∫ ω, X (σ ω) ω ^ 2 ∂P) = ∫ ω, C (σ ω) ω ∂P := by
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
  have hconv : ∀ᵐ ω ∂P, Tendsto (fun n => q n ω) atTop (𝓝 (C (σ ω) ω)) :=
    .of_forall fun ω => tendsto_const_nhds.congr' ((he ω).mono fun n hn => by simp only [q,hn])
  have hmono := local_quadratic_variation_monotone P F hF hle hnull X C hX hC
  have hzero := local_quadratic_variation_initial P F X C hX hC
  have hn (n) : 0 ≤ᵐ[P] q n := by
    filter_upwards [hmono,hzero] with ω hm hz
    have ht0 : (⊥ : ClosedTime T) < ⊤ := bot_le.trans_lt (hσtop ω)
    have h : C ⊥ ω ≤ C (min (κ n ω) (σ ω)) ω :=
      hm ht0 ((min_le_left _ _).trans_lt (hκtop n ω)) bot_le
    simpa only [q,hz,Pi.zero_apply] using h
  have hqm : ∀ᵐ ω ∂P, Monotone (fun n => q n ω) := by
    filter_upwards [hmono] with ω hm
    intro n k hnk
    exact hm ((min_le_left _ _).trans_lt (hκtop n ω))
      ((min_le_left _ _).trans_lt (hκtop k ω)) (min_le_min_right _ (hκm ω hnk))
  have hBsq : Integrable (fun ω => B ω ^ 2) P :=
    (memLp_two_iff_integrable_sq hB.aestronglyMeasurable).1 hB
  have hlim : Tendsto (fun n => ∫ ω, Z n ⊤ ω ^ 2 ∂P) atTop
      (𝓝 (∫ ω, X (σ ω) ω ^ 2 ∂P)) := by
    apply tendsto_integral_of_dominated_convergence (fun ω => B ω ^ 2)
      (fun n => (hsq n).aestronglyMeasurable) hBsq
    · intro n
      filter_upwards [hbound] with ω hω
      have h := hω (κ n ω)
      simp only [Z,min_top_right,min_comm] at h ⊢
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      simpa only [Real.norm_eq_abs,sq_abs] using pow_le_pow_left₀ (norm_nonneg _) h 2
    · exact .of_forall fun ω => tendsto_const_nhds.congr' ((he ω).mono fun n hn => by simp only [Z,min_top_right,hn])
  have hqInt : Tendsto (fun n => ∫ ω, q n ω ∂P) atTop
      (𝓝 (∫ ω, X (σ ω) ω ^ 2 ∂P)) := by simpa only [henergy] using hlim
  obtain ⟨hi,heq⟩ := integrable_monotone_limit_of_integral_limit P q
    (fun ω => C (σ ω) ω) _ hqi hn hqm hconv hqInt
  exact ⟨hi,heq.symm⟩

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.stopped_local_energy_of_square_integrable_bound
