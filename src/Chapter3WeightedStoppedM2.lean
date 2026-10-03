import Chapter3StoppedWeights

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

/-- The weighted square-defect process in prop:qcv really is M2. The
conditioning before/after the random starting time is proved by splitting
each test event, rather than assuming the weighted process is a martingale. -/
theorem bounded_stopped_weight_m2
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (Y : ClosedTime T → Ω → ℝ) (hY : ContinuousM2Witness P F Y)
    (σ : Ω → ClosedTime T) (hσ : ∀ t, MeasurableSet[F t] {ω | σ ω ≤ t})
    (hz : ∀ ω t, t ≤ σ ω → Y t ω = 0)
    (A : Ω → ℝ) (hA : Measurable[writtenStoppedSpace m F σ hσ] A)
    (hAb : MemLp A ∞ P) :
    ContinuousM2Witness P F (fun t ω => A ω*Y t ω) := by
  let Z := fun t ω => A ω*Y t ω
  have hm := stopped_weight_product_adapted F σ hσ Y hY.adapted hz A hA
  have h2 (t) : MemLp (Z t) 2 P := hAb.mul (hY.moment t)
  refine ⟨hm,h2,fun ω => continuous_const.mul (hY.path ω),?_,?_⟩
  · intro s t hst
    apply Filter.EventuallyEq.symm
    apply ae_eq_condExp_of_forall_setIntegral_eq (hle s) ((h2 t).integrable (by norm_num))
      (fun _ _ _ => ((h2 s).integrable (by norm_num)).integrableOn) _
      (hm s).stronglyMeasurable.aestronglyMeasurable
    intro E hE _
    let B := {ω | σ ω ≤ s}
    let G0 := E.indicator (B.indicator A)
    let G1 := (E ∩ Bᶜ).indicator A
    have hEm := hle s _ hE
    have hBm : MeasurableSet B := hle s _ (hσ s)
    have hG0m : Measurable[F s] G0 :=
      (stopped_weight_indicator_measurable F σ hσ A hA s).indicator hE
    have hG1m : Measurable[writtenStoppedSpace m F σ hσ] G1 :=
      hA.indicator (past_event_before_stop_measurable F hF hle σ hσ s E hE)
    have hG0 : MemLp G0 ∞ P := (hAb.indicator hBm).indicator hEm
    have hG1 : MemLp G1 ∞ P := hAb.indicator (hEm.inter hBm.compl)
    have hi0 (r) : Integrable (fun ω => G0 ω*Y r ω) P :=
      (hG0.mul (hY.moment r) : MemLp _ 2 P).integrable (by norm_num)
    have hi1 (r) : Integrable (fun ω => G1 ω*Y r ω) P :=
      (hG1.mul (hY.moment r) : MemLp _ 2 P).integrable (by norm_num)
    have he0 : (∫ ω, G0 ω*Y s ω ∂P) = ∫ ω, G0 ω*Y t ω ∂P := by
      have hp := unbounded_pullout_by_restriction P (hle s) G0 (Y t)
        hG0m.stronglyMeasurable (hi0 t) ((hY.moment t).integrable (by norm_num))
      have he : P[G0*Y t | F s] =ᵐ[P] (fun ω => G0 ω*Y s ω) := by
        filter_upwards [hp,hY.martingale s t hst] with ω hp hy
        simpa only [Pi.mul_apply,hy] using hp
      have hi := integral_congr_ae he
      rw [integral_condExp (hle s)] at hi
      exact hi.symm
    have he1 (r) : (∫ ω, G1 ω*Y r ω ∂P) = 0 :=
      stopped_zero_pairing_at_time P F hF hle Y hY σ hσ hz G1 hG1m
        (hG1.mono_exponent le_top) r
    have hsplit (r) : (∫ ω in E, Z r ω ∂P) =
        (∫ ω, G0 ω*Y r ω ∂P)+(∫ ω, G1 ω*Y r ω ∂P) := by
      rw [← integral_indicator hEm,← integral_add (hi0 r) (hi1 r)]
      apply integral_congr_ae
      exact .of_forall fun ω => by
        by_cases he : ω ∈ E <;> by_cases hb : ω ∈ B <;>
          simp [G0,G1,Z,Set.indicator,he,hb]
    rw [hsplit s,hsplit t,he1 s,he1 t,he0]
  · exact .of_forall fun ω => by
      dsimp only [Z]
      rw [hz ω ⊥ bot_le,mul_zero]
      rfl

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.bounded_stopped_weight_m2
