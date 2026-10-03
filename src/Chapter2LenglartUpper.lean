import Chapter2SquareDoob
import Chapter2StoppedRegularity

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

noncomputable def localStoppedPath
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    {X : ClosedTime T → Ω → ℝ} (hX : LocalMProcessWitness P F X)
    (σ : Ω → ClosedTime T) (hσ : ∀ t, MeasurableSet[F t] {ω | σ ω ≤ t})
    (hσtop : ∀ ω, σ ω < ⊤) (ω : Ω) : C(ClosedTime T,ℝ) :=
  continuousPath (fun t ω => X (min (σ ω) t) ω)
    (hX.stopped_regular P F hF hle σ hσ hσtop).2 ω

/-- The second Lenglart inequality, using the actual first crossing of
|X|, the stopped energy identity, and Markov's inequality. -/
theorem local_lenglart_upper
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X C : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (hC : LocalCovarianceWitness P F X X C)
    (σ : Ω → ClosedTime T) (hσ : ∀ t, MeasurableSet[F t] {ω | σ ω ≤ t})
    (hσtop : ∀ ω, σ ω < ⊤) (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    P.real {ω | δ ≤ C (σ ω) ω} ≤ ε ^ 2 / δ +
      P.real {ω | ε ≤ ‖localStoppedPath P F hF hle hX σ hσ hσtop ω‖} := by
  let Y := fun t ω => X (min (σ ω) t) ω
  obtain ⟨hYm,hYc⟩ := hX.stopped_regular P F hF hle σ hσ hσtop
  let ξ := fun ω => sInf {t | ε ≤ |Y t ω|}
  let β := fun ω => min (ξ ω) (σ ω)
  have hξ : ∀ t, MeasurableSet[F t] {ω | ξ ω ≤ t} := by
    apply continuous_hitting_stopping_written F hF (fun t ω => |Y t ω|)
      (fun t => by
        letI : MeasurableSpace Ω := F t
        simpa only [Real.norm_eq_abs] using (hYm t).norm) (fun ω => (hYc ω).abs) (Ici ε) isClosed_Ici
  have hβ : ∀ t, MeasurableSet[F t] {ω | β ω ≤ t} :=
    (written_stopping_min_max F ξ σ hξ hσ).1
  have hβσ (ω) : β ω ≤ σ ω := min_le_right _ _
  have hβtop (ω) : β ω < ⊤ := (hβσ ω).trans_lt (hσtop ω)
  have hb : ∀ᵐ ω ∂P, ∀ t, ‖X (min (β ω) t) ω‖ ≤ ε := by
    filter_upwards [hX.initial P F] with ω hz
    intro t
    have hzY : |Y ⊥ ω| ≤ ε := by simpa only [Y,min_bot_right,hz,Pi.zero_apply,abs_zero] using hε.le
    have hh := continuous_level_stop_bound (fun s => |Y s ω|) (hYc ω).abs ε hzY
      (min (β ω) t) ((min_le_left _ _).trans (min_le_left _ _))
    have he : min (σ ω) (min (β ω) t) = min (β ω) t :=
      min_eq_right ((min_le_left _ _).trans (hβσ ω))
    simpa only [Y,he,Real.norm_eq_abs] using hh
  have hM := local_stop_is_m2_of_square_integrable_bound P F hF hle X hX β hβ hβtop
    (fun _ => ε) (memLp_const ε) hb
  obtain ⟨hCi,henergy⟩ := stopped_M2_energy P F hF hle hnull X C hX hC β hβ hβtop hM
  have hCn : 0 ≤ᵐ[P] (fun ω => C (β ω) ω) := by
    filter_upwards [local_quadratic_variation_monotone P F hF hle hnull X C hX hC,
      local_quadratic_variation_initial P F X C hX hC] with ω hm hz
    have hh := hm (bot_le.trans_lt (hβtop ω)) (hβtop ω) bot_le
    simpa only [hz,Pi.zero_apply] using hh
  have hEsq : (∫ ω, X (β ω) ω ^ 2 ∂P) ≤ ε ^ 2 := by
    have hi : Integrable (fun ω => X (β ω) ω ^ 2) P := by
      simpa only [min_top_right] using
        (memLp_two_iff_integrable_sq (hM.moment ⊤).aestronglyMeasurable).1 (hM.moment ⊤)
    have hh : (fun ω => X (β ω) ω ^ 2) ≤ᵐ[P] (fun _ => ε ^ 2) := by
      filter_upwards [hb] with ω hω
      have h := hω ⊤
      simp only [min_top_right] at h
      simpa only [Real.norm_eq_abs,sq_abs] using pow_le_pow_left₀ (norm_nonneg _) h 2
    simpa only [integral_const,probReal_univ,one_smul] using integral_mono_ae hi (integrable_const _) hh
  have hmarkov : P.real {ω | δ ≤ C (β ω) ω} ≤ ε ^ 2 / δ := by
    apply (le_div_iff₀ hδ).2
    have h := mul_meas_ge_le_integral_of_nonneg hCn hCi δ
    rw [← henergy] at h
    simpa only [mul_comm] using h.trans hEsq
  have hsub : {ω | δ ≤ C (σ ω) ω} ⊆ {ω | δ ≤ C (β ω) ω} ∪
      {ω | ε ≤ ‖localStoppedPath P F hF hle hX σ hσ hσtop ω‖} := by
    intro ω hω
    by_cases he : β ω = σ ω
    · exact Or.inl (by simpa only [mem_setOf_eq,he] using hω)
    · right
      have hlt : β ω < σ ω := lt_of_le_of_ne (hβσ ω) he
      have hh : ξ ω < σ ω := (min_lt_iff.1 hlt).resolve_right (lt_irrefl _)
      obtain ⟨s,hs,hhit⟩ := (closed_hitting_lower_event (fun t => |Y t ω|)
        (hYc ω).abs (Ici ε) isClosed_Ici (σ ω) (hσtop ω)).1 hh.le
      exact hhit.trans (by simpa only [localStoppedPath,continuousPath,ContinuousMap.coe_mk,Real.norm_eq_abs]
        using (localStoppedPath P F hF hle hX σ hσ hσtop ω).norm_coe_le_norm s)
  exact ((measureReal_mono hsub).trans (measureReal_union_le _ _)).trans
    (add_le_add hmarkov le_rfl)

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.local_lenglart_upper
