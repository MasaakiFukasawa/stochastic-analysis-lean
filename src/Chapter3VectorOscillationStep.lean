import Chapter2LevelLocalization
import FullAuditStoppedContinuous

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

/-- One actual step of the oscillation partition, including its increment
bound and attainment of the prescribed oscillation when the cap is inactive. -/
theorem vector_oscillation_step_path
    {E : Type*} [NormedAddCommGroup E]
    {ι : Type*} [CompleteLinearOrder ι] [DenselyOrdered ι]
    [TopologicalSpace ι] [OrderTopology ι]
    (X : ι → E) (hX : Continuous X) (σ c : ι) (hσc : σ ≤ c)
    (δ : ℝ) (hδ : 0 < δ) :
    let Y := fun t => ‖X t-X (min σ t)‖
    let ρ := min (sInf {t | δ ≤ Y t}) c
    σ ≤ ρ ∧ ρ ≤ c ∧
      (∀ t, ‖X (min ρ t)-X (min σ t)‖ ≤ δ) ∧
      (ρ < c → δ ≤ ‖X ρ-X σ‖) := by
  intro Y ρ
  have hc : Continuous Y := (hX.sub (hX.comp (continuous_const.min continuous_id))).norm
  have hhit : σ ≤ sInf {t | δ ≤ Y t} := by
    apply le_sInf
    intro t ht
    by_contra hn
    have htσ : t ≤ σ := (le_of_not_ge hn)
    have hy : Y t = 0 := by simp only [Y,min_eq_right htσ,sub_self,norm_zero]
    exact (not_le_of_gt hδ) (hy ▸ ht)
  have hσρ : σ ≤ ρ := le_min hhit hσc
  have hb : ∀ t, Y (min ρ t) ≤ δ := by
    intro t
    apply continuous_level_stop_bound Y hc δ
    · simpa only [Y,min_eq_right bot_le,sub_self,norm_zero] using hδ.le
    · exact (min_le_left _ _).trans (min_le_left _ _)
  refine ⟨hσρ,min_le_right _ _,?_,?_⟩
  · intro t
    have hm : min σ (min ρ t) = min σ t := by rw [← min_assoc,min_eq_left hσρ]
    simpa only [Y,hm] using hb t
  · intro hρc
    have hρtop : ρ < ⊤ := hρc.trans_le le_top
    have hh : sInf {t | δ ≤ Y t} < c :=
      (min_lt_iff.mp hρc).resolve_right (lt_irrefl _)
    have he : ρ = sInf {t | δ ≤ Y t} := min_eq_left hh.le
    have hne : {t | δ ≤ Y t}.Nonempty := by
      by_contra hn
      rw [not_nonempty_iff_eq_empty.mp hn,sInf_empty] at hh
      exact not_lt_of_ge le_top hh
    have hmem := IsClosed.sInf_mem hne (isClosed_Ici.preimage hc)
    have hlevel : δ ≤ Y ρ := by rw [he]; exact hmem
    simpa only [Y,min_eq_left hσρ] using hlevel

/-- The first oscillation time is a stopping time. Adaptedness of the
stopped process is derived from the existing stopped-value theorem. -/
theorem finite_vector_oscillation_step_stopping
    {J : Type*} [Fintype J]
    {Ω : Type*} {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F)
    (X : ClosedTime T → Ω → (J → ℝ))
    (hm : ∀ i t, Measurable[F t] (fun ω => X t ω i))
    (hc : ∀ ω, Continuous (fun t => X t ω))
    (σ : Ω → ClosedTime T) (hσ : ∀ t, MeasurableSet[F t] {ω | σ ω ≤ t})
    (c : ClosedTime T) (δ : ℝ) :
    ∀ t, MeasurableSet[F t]
      {ω | min (sInf {s | δ ≤ ‖X s ω-X (min (σ ω) s) ω‖}) c ≤ t} := by
  have hsm i := stopped_min_value_measurable F hF σ hσ (fun t ω => X t ω i) (hm i)
    (fun ω t => ((continuous_apply i).comp (hc ω)).continuousAt.continuousWithinAt)
  have hh := continuous_hitting_stopping_written F hF
    (fun t ω => ‖X t ω-X (min (σ ω) t) ω‖)
    (fun t => by
      letI : MeasurableSpace Ω := F t
      exact (measurable_pi_lambda (fun i => (hm i t).sub (hsm i t))).norm)
    (fun ω => ((hc ω).sub ((hc ω).comp (continuous_const.min continuous_id))).norm)
    (Ici δ) isClosed_Ici
  exact (written_stopping_min_max F _ (fun _ => c) hh
    (fun t => by by_cases h : c ≤ t <;> simp [h])).1

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.vector_oscillation_step_path
#print axioms Asakura.Chapter3Complete.finite_vector_oscillation_step_stopping
