import EndToEndLocalItoPaths
import Chapter3OpenProcessRegularity
import Chapter3SemimartingaleFiniteSums
import Chapter2StochasticFubiniPrinted

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.EndToEnd
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter13
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false

/-- Actual local Ito integrals with jointly measurable parameter and time,
constructed up to the parameter-null sets inherent in parameter integration. -/
theorem local_ito_joint_representative {Ω E : Type} {m : MeasurableSpace Ω} [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d) (i : Fin d)
    (μ : Measure E) [IsFiniteMeasure μ]
    (H : E × (Ω × ℝ) → ℝ) (hm : Measurable H)
    (hp : ∀ b,0<b → @Measurable _ _
      ((inferInstance : MeasurableSpace E).prod (progressiveSpace (fun t : Icc (0:ℝ) b => B.F (realTimeClamp t.val)))) inferInstance
      (fun z : E × (Ω × Icc (0:ℝ) b) => H (z.1,(z.2.1,z.2.2.val))))
    (hb : ∀ w b,0≤b → ∃ K : ℝ,0≤K ∧ ∀ x r,r∈Icc 0 b → |H (x,(w,r))|≤K)
    (N : E → HalfClosedTime → Ω → ℝ) (hN : ∀ x,LocalMProcessWitness P B.F (N x))
    (hNI : ∀ x,ItoCovarianceFormula P B.F (B.W i) (fun z => H (x,z)) (N x)) :
    ∃ V : E → HalfClosedTime → Ω → ℝ,
      Measurable (fun z : E × (Ω × HalfClosedTime) => V z.1 z.2.2 z.2.1) ∧
      (∀ x,LocalMProcessWitness P B.F (V x)) ∧
      ∀ᵐ x ∂μ, ItoCovarianceFormula P B.F (B.W i) (fun z => H (x,z)) (V x) ∧
        ∀ᵐ w ∂P, ∀ t,t<⊤ → V x t w=N x t w := by
  classical
  obtain ⟨R,hRm,hRe⟩ := local_ito_joint_paths P B i μ H hm hp hb N hN hNI
  let Bad := {x | ¬ ∀ᵐ w ∂P, ∀ r, R (x,w) r=N x (realTimeClamp r) w}
  have hBad : μ Bad=0 := ae_iff.mp hRe
  let S := (toMeasurable μ Bad)ᶜ
  have hSm : MeasurableSet S := (measurableSet_toMeasurable μ Bad).compl
  have hS : ∀ᵐ x ∂μ, x∈S := by
    rw [ae_iff]
    simpa only [S,mem_compl_iff,not_not,Set.ofPred_mem_eq] using (measure_toMeasurable (μ:=μ) Bad).trans hBad
  have hgood x (hx : x∈S) : ∀ᵐ w ∂P, ∀ r, R (x,w) r=N x (realTimeClamp r) w := by
    by_contra hn
    exact hx (subset_toMeasurable μ Bad hn)
  let V := fun x (t : HalfClosedTime) w => if x∈S then R (x,w) (t:EReal).toReal else 0
  have hVm : Measurable (fun z : E × (Ω × HalfClosedTime) => V z.1 z.2.2 z.2.1) := by
    have he : Continuous (fun z : C(ℝ,ℝ) × ℝ => z.1 z.2) := continuous_fst.eval continuous_snd
    apply Measurable.ite (hSm.preimage measurable_fst) ?_ measurable_const
    exact he.measurable.comp ((hRm.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).prodMk
      (measurable_ereal_toReal.comp (measurable_subtype_coe.comp (measurable_snd.comp measurable_snd))))
  have he x (hx : x∈S) : ∀ᵐ w ∂P, ∀ t,t<⊤ → V x t w=N x t w := by
    filter_upwards [hgood x hx] with w hw
    intro t ht
    obtain ⟨r,hr,_,hrt⟩ := finite_closed_time_real t ht
    rw [← hrt]
    simp only [V,if_pos hx,real_time_clamp_eq r hr le_top,EReal.toReal_coe]
    exact hw r
  have hVa x : LocalMProcessWitness P B.F (V x) := by
    by_cases hx : x∈S
    · have hm t : Measurable (V x t) :=
        hVm.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
      have ha t (ht : t<⊤) : Measurable[B.F t] (V x t) :=
        measurable_of_augmented_ae P (B.le t) (B.null t) _ _ (hm t)
          ((hN x).adapted P B.F t ht) ((he x hx).mono (fun w hw => hw t ht))
      have hc w t (ht : t<⊤) : ContinuousAt (fun s => V x s w) t := by
        simp only [V,if_pos hx]
        exact (R (x,w)).continuous.continuousAt.comp
          ((EReal.tendsto_toReal (ne_of_lt (show (t:EReal)<⊤ from ht))
            (ne_of_gt ((EReal.bot_lt_coe 0).trans_le t.property.1))).comp continuous_subtype_val.continuousAt)
      exact Asakura.Chapter3Complete.LocalMProcessWitness.congr_ae_open P B.F B.mono (hN x) ha hc
        ((he x hx).mono (fun w hw t ht => (hw t ht).symm))
    · simpa only [V,if_neg hx] using zero_local_process P (by simp : (0:EReal)<⊤) B.F
  refine ⟨V,hVm,hVa,?_⟩
  filter_upwards [hS] with x hx
  refine ⟨?_,he x hx⟩
  exact ItoCovarianceFormula.congr_integral P B.F B.mono B.le (B.W i) (N x) (V x) _
    (hN x) (hVa x) ((he x hx).mono (fun w hw t ht => (hw t ht).symm)) (hNI x)

#print axioms local_ito_joint_representative
end Asakura.EndToEnd
