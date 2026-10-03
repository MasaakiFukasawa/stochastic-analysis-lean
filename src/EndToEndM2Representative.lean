import EndToEndContinuousPathRepresentative
import Chapter13M2Evaluation

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.EndToEnd
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter13
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- Strongly measurable M2-valued families have jointly measurable,
continuous, adapted process representatives. Joint measurability is a conclusion. -/
theorem m2_joint_representative {E Ω : Type*} [MeasurableSpace E] {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hle : ∀ t,F t ≤ m)
    (hnull : ∀ t A, MeasurableSet[m] A → P A=0 → MeasurableSet[F t] A)
    (Z : E → continuousM2Terminal P F) (hs : StronglyMeasurable Z) :
    ∃ N : E → ClosedTime T → Ω → ℝ,
      Measurable (fun z : E × (Ω × ClosedTime T) => N z.1 z.2.2 z.2.1) ∧
      ∀ x, ∃ hN : ContinuousM2Witness P F (N x), m2TerminalOfProcess P F (N x) hN=Z x := by
  classical
  let X := fun x => m2ProcessOfTerminal P F (Z x)
  have hX x := (m2_process_of_terminal_spec P F (Z x)).1
  have hXs t : StronglyMeasurable (fun x => ((hX x).moment t).toLp (X x t)) := by
    obtain ⟨L,hL⟩ := m2_evaluation_operator P F hle t
    have he x : L (Z x)=((hX x).moment t).toLp (X x t) := by
      apply Lp.ext
      have hh := (hL _ (hX x)).trans ((hX x).moment t).coeFn_toLp.symm
      simpa only [m2_process_terminal_value] using hh
    simpa only [Function.comp_def,he] using L.continuous.comp_stronglyMeasurable hs
  obtain ⟨R,hRm,hRe⟩ := continuous_path_joint_representative P X
    (fun x => (hX x).path) (fun x => (hX x).moment) hXs
  let N := fun x t w => R (x,w) t
  have hNm : Measurable (fun z : E × (Ω × ClosedTime T) => N z.1 z.2.2 z.2.1) := by
    have he : Continuous (fun z : C(ClosedTime T,ℝ) × ClosedTime T => z.1 z.2) :=
      continuous_fst.eval continuous_snd
    exact he.measurable.comp ((hRm.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).prodMk
      (measurable_snd.comp measurable_snd))
  refine ⟨N,hNm,?_⟩
  intro x
  have he t : N x t=ᵐ[P] X x t := (hRe x).mono (fun w hw => hw t)
  have hm t : Measurable (N x t) := (ContinuousMap.measurable_eval t).comp
    (hRm.comp measurable_prodMk_left)
  have hN : ContinuousM2Witness P F (N x) := by
    refine ⟨fun t => measurable_of_augmented_ae P (hle t) (hnull t) _ _ (hm t) ((hX x).adapted t) (he t),
      fun t => ((hX x).moment t).ae_eq (he t).symm,
      fun w => (R (x,w)).continuous,?_,?_⟩
    · intro s t hst
      exact (condExp_congr_ae (he t)).trans (((hX x).martingale s t hst).trans (he s).symm)
    · exact (he ⊥).trans (hX x).initial
  refine ⟨hN,?_⟩
  apply Subtype.ext
  apply Lp.ext
  exact (hN.moment ⊤).coeFn_toLp.trans ((he ⊤).trans (m2_process_of_terminal_spec P F (Z x)).2)

/-- Bochner-integrable families need only be represented for almost every
parameter, as required by the stochastic Fubini theorem. -/
theorem m2_joint_representative_ae {E Ω : Type*} [MeasurableSpace E] {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hle : ∀ t,F t ≤ m)
    (hnull : ∀ t A, MeasurableSet[m] A → P A=0 → MeasurableSet[F t] A)
    (μ : Measure E) (Z : E → continuousM2Terminal P F) (hs : AEStronglyMeasurable Z μ) :
    ∃ N : E → ClosedTime T → Ω → ℝ,
      Measurable (fun z : E × (Ω × ClosedTime T) => N z.1 z.2.2 z.2.1) ∧
      (∀ x,ContinuousM2Witness P F (N x)) ∧
      ∀ᵐ x ∂μ, ∃ hN : ContinuousM2Witness P F (N x), m2TerminalOfProcess P F (N x) hN=Z x := by
  obtain ⟨N,hm,hN⟩ := m2_joint_representative P F hle hnull (hs.mk Z) hs.stronglyMeasurable_mk
  refine ⟨N,hm,fun x => (hN x).choose,?_⟩
  filter_upwards [hs.ae_eq_mk] with x hx
  obtain ⟨h,he⟩ := hN x
  exact ⟨h,he.trans hx.symm⟩

#print axioms m2_joint_representative
#print axioms m2_joint_representative_ae
end Asakura.EndToEnd
