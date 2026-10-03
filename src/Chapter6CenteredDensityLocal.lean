import Chapter6OpenMartingale
import Chapter6GirsanovProduct

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- A conditional density is centered at its possibly random initial value.
No triviality of the initial sigma algebra is imposed. -/
theorem centered_density_local {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (D : Ω → ℝ) (hD : Integrable D P) (M : ClosedTime T → Ω → ℝ)
    (hMa : ∀ t,Measurable[F t] (M t))
    (hMc : ∀ w t,t<⊤ → ContinuousAt (fun s => M s w) t)
    (hME : ∀ t,M t=ᵐ[P] P[D|F t]) :
    LocalMProcessWitness P F (fun t w => M t w-M ⊥ w) := by
  have hi t : Integrable (M t) P := integrable_condExp.congr (hME t).symm
  obtain ⟨u,_,_,_,hum,hut,huc⟩ := positive_real_time_exhaustion hT
  apply open_continuous_martingale_is_local P hT F hF hle _
    (fun t => (hMa t).sub ((hMa ⊥).mono (hF bot_le) le_rfl))
    (fun w t ht => (hMc w t ht).sub continuousAt_const)
    (fun t _ => (hi t).sub (hi ⊥)) _ _
    (fun n => realTimeClamp (u n)) hum.monotone hut huc
  · intro s t hst _
    have he : P[M t|F s]=ᵐ[P] M s :=
      (condExp_congr_ae (hME t)).trans ((condExp_condExp_of_le (hF hst) (hle t)).trans (hME s).symm)
    have hz : P[M ⊥|F s]=ᵐ[P] M ⊥ := by
      exact Filter.EventuallyEq.of_eq (condExp_of_stronglyMeasurable (hle s)
        (((hMa ⊥).mono (hF bot_le) le_rfl).stronglyMeasurable) (hi ⊥))
    exact (condExp_sub (hi t) (hi ⊥) (F s)).trans (he.sub hz)
  · exact ae_of_all P (fun w => sub_self _)

end Asakura.Chapter6
