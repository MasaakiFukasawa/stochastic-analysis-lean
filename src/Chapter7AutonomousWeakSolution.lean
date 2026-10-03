import Chapter7AutonomousClock
import Chapter7AutonomousClockDivergence
import Chapter7ItoCommonIntegrand

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

/-- The drift-free autonomous weak SDE is constructed for every continuous
nonzero coefficient. The divergent clock comes from the just-proved
Brownian occupation lemma, not from an additional nonexplosion assumption. -/
theorem autonomous_weak_solution_written
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsPreBrownianReal B P)
    (hm : ∀ t,Measurable (B t)) (hc : ∀ w,Continuous (fun t => B t w))
    (σ : ℝ → ℝ) (hσ : Continuous σ) (hn : ∀ x,σ x ≠ 0) :
    ∃ W : BrownianSystem P 1,∃ Y : HalfClosedTime → Ω → ℝ,
      LocalMProcessWitness P W.F Y ∧
      ItoCovarianceFormula P W.F (W.W 0) (fun z => σ (Y (realTimeClamp z.2) z.1)) Y := by
  obtain ⟨BB,hdiv⟩ := autonomous_clock_divergent_brownian P B hB hm hc σ hσ hn
  obtain ⟨A,hAa,hAc,hA0,hAu,hode⟩ := autonomous_clock_constructed P BB σ hσ hn hdiv
  have ht := time_change_sde_written P BB (fun _ => 0) measurable_const
    (fun x _ => σ x) (hσ.comp continuous_fst) (fun x _ => hn x) A hAa hAc hA0 hAu
    (by simpa only [zero_add] using hode)
  dsimp only at ht
  obtain ⟨hτ,hτfin,W,hWF,hXa,hXc,hInverse,Z,hZ,hIto,he⟩ := ht
  refine ⟨W,Z,hZ,?_⟩
  apply ito_integrand_common_ae P W.F (W.W 0) Z _ _ hIto
  filter_upwards [he] with w hw
  intro r
  have hrfin : realTimeClamp (T := (⊤:EReal)) r < ⊤ :=
    lt_of_le_of_lt (real_time_clamp_mono (le_max_right 0 r)) (changed_time_finite _ (le_max_left _ _))
  have hh := hw (realTimeClamp r) hrfin
  simp only [zero_add] at hh ⊢
  rw [hh]

end Asakura.Chapter7
