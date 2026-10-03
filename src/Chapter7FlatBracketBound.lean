import Chapter2LenglartLower

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter7
open Asakura.Chapter2Complete Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- The first Lenglart inequality, using the actual first crossing of
quadratic variation and the square maximal inequality. -/
theorem local_small_bracket_large_path_probability
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X C : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (hC : LocalCovarianceWitness P F X X C)
    (σ : Ω → ClosedTime T) (hσ : ∀ t, MeasurableSet[F t] {ω | σ ω ≤ t})
    (hσtop : ∀ ω, σ ω < ⊤) (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    P.real {ω | ε ≤ ‖localStoppedPath P F hF hle hX σ hσ hσtop ω‖ ∧ C (σ ω) ω < δ} ≤ δ / ε ^ 2 := by
  let Q := fun t ω => C (min (σ ω) t) ω
  obtain ⟨hQm,hQc⟩ := hC.stopped_regular P F hF hle hX hX σ hσ hσtop
  let ξ := fun ω => sInf {t | δ ≤ Q t ω}
  let β := fun ω => min (ξ ω) (σ ω)
  have hξ : ∀ t, MeasurableSet[F t] {ω | ξ ω ≤ t} :=
    continuous_hitting_stopping_written F hF Q hQm hQc (Ici δ) isClosed_Ici
  have hβ : ∀ t, MeasurableSet[F t] {ω | β ω ≤ t} :=
    (written_stopping_min_max F ξ σ hξ hσ).1
  have hβσ (ω) : β ω ≤ σ ω := min_le_right _ _
  have hβtop (ω) : β ω < ⊤ := (hβσ ω).trans_lt (hσtop ω)
  have hmono := local_quadratic_variation_monotone P F hF hle hnull X C hX hC
  have hzero := local_quadratic_variation_initial P F X C hX hC
  have hb : ∀ᵐ ω ∂P, C (β ω) ω ∈ Icc 0 δ := by
    filter_upwards [hmono,hzero] with ω hm hz
    constructor
    · have hh : C ⊥ ω ≤ C (β ω) ω :=
        hm (bot_le.trans_lt (hβtop ω)) (hβtop ω) bot_le
      simpa only [hz,Pi.zero_apply] using hh
    · have hzQ : Q ⊥ ω ≤ δ := by simpa only [Q,min_bot_right,hz,Pi.zero_apply] using hδ.le
      have hh := continuous_level_stop_bound (fun t => Q t ω) (hQc ω) δ hzQ
        (β ω) (min_le_left _ _)
      simpa only [Q,min_eq_right (hβσ ω)] using hh
  have hCm : Measurable[m] (fun ω => C (β ω) ω) := by
    have hh := (hC.stopped_regular P F hF hle hX hX β hβ hβtop).1 ⊤
    simpa only [min_top_right] using hh.mono (hle ⊤) le_rfl
  have hCi : Integrable (fun ω => C (β ω) ω) P :=
    Integrable.of_mem_Icc 0 δ hCm.aemeasurable hb
  obtain ⟨B,hB,hbound⟩ := (stopped_local_M2_equivalences P F hF hle hnull X C hX hC β hβ hβtop).1.mp hCi
  have hM := local_stop_is_m2_of_square_integrable_bound P F hF hle X hX β hβ hβtop B hB hbound
  have henergy := (stopped_M2_energy P F hF hle hnull X C hX hC β hβ hβtop hM).2
  have hEC : (∫ ω, C (β ω) ω ∂P) ≤ δ := by
    simpa only [integral_const,probReal_univ,one_smul] using
      integral_mono_ae hCi (integrable_const δ) (hb.mono fun ω hω => hω.2)
  have hmax : P.real {ω | ε ≤ ‖localStoppedPath P F hF hle hX β hβ hβtop ω‖} ≤ δ / ε ^ 2 := by
    have hh := continuous_m2_square_maximal P F hF hle _ hM ε hε
    simp only [min_top_right] at hh
    rw [henergy] at hh
    have hfin := hh.trans (mul_le_mul_of_nonneg_left hEC (inv_nonneg.2 (sq_nonneg ε)))
    simpa only [localStoppedPath,div_eq_mul_inv,mul_comm] using hfin
  have hsub : ∀ᵐ ω ∂P,
      ω ∈ {ω | ε ≤ ‖localStoppedPath P F hF hle hX σ hσ hσtop ω‖} →
      ω ∈ {ω | ε ≤ ‖localStoppedPath P F hF hle hX β hβ hβtop ω‖} ∪ {ω | δ ≤ C (σ ω) ω} := by
    filter_upwards [hmono] with ω hm
    intro hω
    by_cases he : β ω = σ ω
    · left
      have heq : localStoppedPath P F hF hle hX β hβ hβtop ω =
          localStoppedPath P F hF hle hX σ hσ hσtop ω := by
        ext t
        simp only [localStoppedPath,continuousPath,ContinuousMap.coe_mk,he]
      simpa only [mem_setOf_eq,heq] using hω
    · right
      have hlt : β ω < σ ω := lt_of_le_of_ne (hβσ ω) he
      have hh : ξ ω < σ ω := (min_lt_iff.1 hlt).resolve_right (lt_irrefl _)
      obtain ⟨s,hs,hhit⟩ := (closed_hitting_lower_event (fun t => Q t ω)
        (hQc ω) (Ici δ) isClosed_Ici (σ ω) (hσtop ω)).1 hh.le
      have hleC := hm ((min_le_left _ _).trans_lt (hσtop ω)) (hσtop ω) (min_le_left (σ ω) s)
      exact hhit.trans hleC
  have hprob : P.real {ω | ε ≤ ‖localStoppedPath P F hF hle hX σ hσ hσtop ω‖ ∧ C (σ ω) ω < δ} ≤
      P.real {ω | ε ≤ ‖localStoppedPath P F hF hle hX β hβ hβtop ω‖} := by
    apply ENNReal.toReal_mono (measure_ne_top P _)
    apply measure_mono_ae
    filter_upwards [hsub] with ω hω
    intro he
    exact (hω he.1).resolve_right (not_le.mpr he.2)
  exact hprob.trans hmax

end Asakura.Chapter7
