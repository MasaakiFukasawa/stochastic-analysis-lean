import Chapter6SemimartingaleForward
import Chapter6InverseDensity

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- Equivalence of semimartingale membership, by reversing the actual
conditional density only after the forward implication has been proved. -/
theorem semimartingale_density_equivalence {Ω : Type*} {m : MeasurableSpace Ω}
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t N,MeasurableSet[m] N → P N=0 → MeasurableSet[F t] N)
    (d : Ω → ℝ≥0) (hd : Measurable d) (hdi : Integrable (fun w => (d w:ℝ)) P)
    (hp : ∀ᵐ w ∂P,0<(d w:ℝ)) (hQ : Q=P.withDensity (fun w => (d w:ℝ≥0∞)))
    (M : ClosedTime T → Ω → ℝ) (hMa : ∀ t,Measurable[F t] (M t))
    (hMc : ∀ w t,t<⊤ → ContinuousAt (fun s => M s w) t) (hMp : ∀ t w,0<M t w)
    (hME : ∀ t,M t=ᵐ[P] P[(fun w => (d w:ℝ))|F t]) (X : ClosedTime T → Ω → ℝ) :
    (∃ A Y,SemimartingaleDecomposition P F X A Y) ↔
      (∃ V N,SemimartingaleDecomposition Q F X V N) := by
  constructor
  · rintro ⟨A,Y,hX⟩
    exact semimartingale_density_forward P Q hT F hF hle hnull d hd hdi hp hQ M hMa hMc hMp hME X A Y hX
  · rintro ⟨V,N,hX⟩
    have hae (p : Ω → Prop) : (∀ᵐ w ∂Q,p w) ↔ (∀ᵐ w ∂P,p w) := by
      rw [hQ]
      exact positive_density_ae_iff P d hd hp p
    have hnullQ t E (hmE : MeasurableSet[m] E) (hE : Q E=0) : MeasurableSet[F t] E := by
      apply hnull t E hmE
      have hh : ∀ᵐ w ∂Q,w∉E := by simpa only [ae_iff,not_not,Set.setOf_mem_eq] using hE
      have hh' := (hae _).mp hh
      simpa only [ae_iff,not_not,Set.setOf_mem_eq] using hh'
    have hi : Integrable (fun w => ((d w)⁻¹:ℝ)) Q := by
      simpa using inverse_density_integrable P Q d hd hp hQ
    have hp' : ∀ᵐ w ∂Q,0<((d w)⁻¹:ℝ) := by
      apply (hae _).mpr
      filter_upwards [hp] with w hw
      simpa using inv_pos.mpr hw
    have he : ∀ t,(fun w => (M t w)⁻¹)=ᵐ[Q] Q[(fun w => ((d w)⁻¹:ℝ))|F t] := by
      intro t
      apply (hae _).mpr
      have hh := inverse_density_conditional P Q (hle t) d hd hdi hp hQ
      filter_upwards [hh,hME t] with w hw hm
      simpa [hm] using hw.symm
    exact semimartingale_density_forward Q P hT F hF hle hnullQ
      (fun w => (d w)⁻¹) hd.inv hi hp' (inverse_nnreal_density_measure P Q d hd hp hQ)
      (fun t w => (M t w)⁻¹) (fun t => (hMa t).inv)
      (fun w t ht => (hMc w t ht).inv₀ (hMp t w).ne') (fun t w => inv_pos.mpr (hMp t w)) he X V N hX

end Asakura.Chapter6
