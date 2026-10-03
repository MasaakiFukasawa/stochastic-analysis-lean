import Chapter6DensityL2Transfer
import Chapter2LocalProcess

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- An integrable bound on a finite time interval suffices to remove the
localizers in the conditional martingale identity. -/
theorem integrable_local_conditional {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {T : EReal} [Fact (0≤T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hle : ∀ t,F t≤m)
    (N : ClosedTime T → Ω → ℝ) (hN : LocalMProcessWitness P F N)
    (R : ClosedTime T) (hR : R<⊤) (B : Ω → ℝ) (hB : Integrable B P)
    (hb : ∀ᵐ w ∂P,∀ t,t≤R → ‖N t w‖≤B w) (s : ClosedTime T) (hs : s≤R) :
    P[N R|F s]=ᵐ[P] N s := by
  have hi t (ht : t≤R) : Integrable (N t) P :=
    hB.mono' (((hN.adapted P F t (ht.trans_lt hR)).mono (hle t) le_rfl).aestronglyMeasurable)
      (hb.mono (fun w hw => hw t ht))
  obtain ⟨τ,_,hm,_,hco,hτ⟩ := hN.localizers
  apply Filter.EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq (hle s) (hi R le_rfl)
    (fun _ _ _ => (hi s hs).integrableOn) _
    (hN.adapted P F s (hs.trans_lt hR)).stronglyMeasurable.aestronglyMeasurable
  intro A hA _
  have hAm := hle s _ hA
  have hlim t (ht : t≤R) : Tendsto (fun n => ∫ w in A,N (min (τ n w) t) w ∂P) atTop
      (𝓝 (∫ w in A,N t w ∂P)) := by
    apply tendsto_integral_of_dominated_convergence B
    · intro n
      exact ((hτ n).1.moment t).aestronglyMeasurable.restrict
    · exact hB.integrableOn
    · intro n
      exact ae_restrict_of_ae (hb.mono (fun w hw => hw _ ((min_le_right _ _).trans ht)))
    · apply ae_restrict_of_ae
      apply ae_of_all
      intro w
      obtain ⟨k,hk⟩ := hco w t (ht.trans_lt hR)
      apply tendsto_const_nhds.congr'
      apply eventually_atTop.mpr
      refine ⟨k,?_⟩
      intro n hn
      change N t w=N (min (τ n w) t) w
      rw [min_eq_right (hk.le.trans (hm w hn))]
  have he n : (∫ w in A,N (min (τ n w) s) w ∂P)=∫ w in A,N (min (τ n w) R) w ∂P := by
    calc
      _ = ∫ w in A,P[(fun w => N (min (τ n w) R) w)|F s] w ∂P :=
        setIntegral_congr_ae hAm (((hτ n).1.martingale s R hs).symm.mono (fun w hw _ => hw))
      _ = _ := setIntegral_condExp (hle s) (((hτ n).1.moment R).integrable (by norm_num)) hA
  have hl := hlim s hs
  simp only [he] at hl
  exact tendsto_nhds_unique hl (hlim R le_rfl)

end Asakura.Chapter6
