import Chapter2ConditionalFatou

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/-- The supermartingale step in prop:fatou, directly from bounded
localizers and conditional Fatou, with all stopped integrability proved. -/
theorem lower_bounded_local_stopped_supermartingale
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (X : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (σ : Ω → ClosedTime T) (hσ : ∀ t, MeasurableSet[F t] {ω | σ ω ≤ t})
    (hσtop : ∀ ω, σ ω < ⊤) (a : ℝ)
    (hbound : ∀ᵐ ω ∂P, ∀ t, t < ⊤ → -a ≤ X t ω) :
    (∀ t, Measurable[F t] (fun ω => X (min (σ ω) t) ω)) ∧
    (∀ t, Integrable (fun ω => X (min (σ ω) t) ω) P) ∧
    (∀ ω, Continuous (fun t => X (min (σ ω) t) ω)) ∧
    ((fun ω => X (min (σ ω) ⊥) ω) =ᵐ[P] 0) ∧
    (∀ s t, s ≤ t → ∀ A, MeasurableSet[F s] A →
      (∫ ω in A, X (min (σ ω) t) ω ∂P) ≤ ∫ ω in A, X (min (σ ω) s) ω ∂P) := by
  obtain ⟨τ,ht,hm,htt,hc,hXτ⟩ := hX.localizers
  let Z := fun n t ω => X (min (τ n ω) (min (σ ω) t)) ω
  let Y := fun t ω => X (min (σ ω) t) ω
  have hZ (n) : ContinuousM2Witness P F (Z n) :=
    continuous_m2_stopped P F hF hle (fun t ω => X (min (τ n ω) t) ω)
      (hXτ n).1 σ hσ
  have he (ω t) : ∀ᶠ n in atTop, Z n t ω = Y t ω := by
    obtain ⟨n,hn⟩ := hc ω (σ ω) (hσtop ω)
    refine eventually_atTop.2 ⟨n,fun k hk => ?_⟩
    dsimp [Z,Y]
    rw [← min_assoc,min_eq_right (hn.le.trans (hm ω hk))]
  have hconv (t) : ∀ᵐ ω ∂P, Tendsto (fun n => Z n t ω) atTop (𝓝 (Y t ω)) :=
    .of_forall fun ω => tendsto_const_nhds.congr' ((he ω t).mono fun n hn => hn.symm)
  have hYi (t) : Integrable (Y t) P := by
    apply (localized_wealth_fatou P (fun n => Z n t) (Y t)
      (fun n => ((hZ n).moment t).integrable (by norm_num)) (fun n => ?_) a
      (fun n => ?_) (hconv t)).1
    · have h := integral_congr_ae (((hZ n).martingale ⊥ t bot_le).trans (hZ n).initial)
      rw [integral_condExp (hle ⊥)] at h
      simpa only [Pi.zero_apply,integral_zero] using h
    · exact hbound.mono fun ω hω => hω _ ((min_le_left _ _).trans_lt (htt n ω))
  refine ⟨?_,hYi,?_,?_,?_⟩
  · intro t
    exact @glued_value_measurable Ω (F t) (fun n ω => Z n t ω)
      (fun n => (hZ n).adapted t) _ (fun ω => he ω t)
  · intro ω
    apply continuous_iff_continuousAt.2
    intro t
    exact (hX.path P F ω _ ((min_le_left _ _).trans_lt (hσtop ω))).comp
      (continuous_const.min continuous_id).continuousAt
  · simpa only [Z,min_bot_right] using (hZ 0).initial
  · intro s t hst A hA
    apply conditional_fatou_set_integral P (F s) (hle s) (fun n => Z n t) (Y t) (Y s)
      (fun n => ((hZ n).moment t).integrable (by norm_num)) (hYi t) (hYi s) (-a)
      (hbound.mono fun ω hω n => hω _ ((min_le_left _ _).trans_lt (htt n ω))) (hconv t) ?_ A hA
    filter_upwards [ae_all_iff.2 (fun n => (hZ n).martingale s t hst),hconv s] with ω hω hlim
    simpa only [hω] using hlim

/-- The final expectation comparison in prop:fatou. The output includes
adaptedness, L1 integrability, continuity, the martingale identity and X_0=0. -/
theorem lower_bounded_local_zero_terminal_mean_is_martingale
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (X : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (σ : Ω → ClosedTime T) (hσ : ∀ t, MeasurableSet[F t] {ω | σ ω ≤ t})
    (hσtop : ∀ ω, σ ω < ⊤) (a : ℝ)
    (hbound : ∀ᵐ ω ∂P, ∀ t, t < ⊤ → -a ≤ X t ω)
    (hmean : (∫ ω, X (σ ω) ω ∂P) = 0) :
    (∀ t, Measurable[F t] (fun ω => X (min (σ ω) t) ω)) ∧
    (∀ t, Integrable (fun ω => X (min (σ ω) t) ω) P) ∧
    (∀ ω, Continuous (fun t => X (min (σ ω) t) ω)) ∧
    (∀ s t, s ≤ t → P[(fun ω => X (min (σ ω) t) ω)|F s] =ᵐ[P]
      (fun ω => X (min (σ ω) s) ω)) ∧
    ((fun ω => X (min (σ ω) ⊥) ω) =ᵐ[P] 0) := by
  obtain ⟨hYm,hYi,hYc,hY0,hineq⟩ :=
    lower_bounded_local_stopped_supermartingale P F hF hle X hX σ hσ hσtop a hbound
  let Y := fun t ω => X (min (σ ω) t) ω
  have hzero (t) : (∫ ω, Y t ω ∂P) = 0 := by
    have hlo := hineq t ⊤ le_top univ MeasurableSet.univ
    have hup := hineq ⊥ t bot_le univ MeasurableSet.univ
    have hbot : (∫ ω, X (min (σ ω) ⊥) ω ∂P) = 0 := by
      simpa only [Pi.zero_apply,integral_zero] using integral_congr_ae hY0
    simp only [setIntegral_univ,min_top_right,hmean,hbot] at hlo hup
    exact le_antisymm hup hlo
  refine ⟨hYm,hYi,hYc,?_,hY0⟩
  intro s t hst
  apply Filter.EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq (hle s) (hYi t)
    (fun _ _ _ => (hYi s).integrableOn) _ (hYm s).stronglyMeasurable.aestronglyMeasurable
  intro A hA _
  have hi := hineq s t hst A hA
  have hc := hineq s t hst Aᶜ hA.compl
  have hs := integral_add_compl (hle s _ hA) (hYi s)
  have ht := integral_add_compl (hle s _ hA) (hYi t)
  change (∫ ω in A, Y s ω ∂P)+(∫ ω in Aᶜ, Y s ω ∂P) = ∫ ω, Y s ω ∂P at hs
  change (∫ ω in A, Y t ω ∂P)+(∫ ω in Aᶜ, Y t ω ∂P) = ∫ ω, Y t ω ∂P at ht
  rw [hzero s] at hs
  rw [hzero t] at ht
  change (∫ ω in A, Y s ω ∂P) = ∫ ω in A, Y t ω ∂P
  change (∫ ω in A, Y t ω ∂P) ≤ ∫ ω in A, Y s ω ∂P at hi
  change (∫ ω in Aᶜ, Y t ω ∂P) ≤ ∫ ω in Aᶜ, Y s ω ∂P at hc
  linarith

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.lower_bounded_local_stopped_supermartingale
#print axioms Asakura.Chapter2Complete.lower_bounded_local_zero_terminal_mean_is_martingale
