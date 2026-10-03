import Chapter6GeneralDensityTransform
import Chapter2SemimartingaleDecomposition

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- Prove P-to-Q semimartingale preservation first, so the reverse direction
does not presuppose that a Q-local martingale is a P-semimartingale. -/
theorem semimartingale_density_forward {Ω : Type*} {m : MeasurableSpace Ω}
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t N,MeasurableSet[m] N → P N=0 → MeasurableSet[F t] N)
    (d : Ω → ℝ≥0) (hd : Measurable d) (hdi : Integrable (fun w => (d w:ℝ)) P)
    (hp : ∀ᵐ w ∂P,0<(d w:ℝ)) (hQ : Q=P.withDensity (fun w => (d w:ℝ≥0∞)))
    (M : ClosedTime T → Ω → ℝ) (hMa : ∀ t,Measurable[F t] (M t))
    (hMc : ∀ w t,t<⊤ → ContinuousAt (fun s => M s w) t) (hMp : ∀ t w,0<M t w)
    (hME : ∀ t,M t=ᵐ[P] P[(fun w => (d w:ℝ))|F t])
    (X A Y : ClosedTime T → Ω → ℝ) (hX : SemimartingaleDecomposition P F X A Y) :
    ∃ V N,SemimartingaleDecomposition Q F X V N := by
  have hL := centered_density_local P hT F hF hle _ hdi M hMa hMc hME
  obtain ⟨C,hC⟩ := local_covariance_witness_exists P F hF hle hnull _ Y hL hX.martingale
  obtain ⟨c,hc,hcm,hcT,_,_,hcc⟩ := positive_real_time_exhaustion hT
  obtain ⟨K,hKv,hKc,hKI,hN⟩ := general_density_transform P Q hT F hF hle hnull
    d hd hdi hp hQ M hMa hMc hMp hME Y C hX.martingale hC c (fun n => (hc n).le) hcm.monotone hcT hcc
  refine ⟨(fun t w => A t w+K t w),(fun t w => Y t w-K t w),
    ⟨hX.variation.add hKv hF,hN,hX.continuous,?_⟩⟩
  intro t ht w
  rw [hX.decomposition t ht w]
  ring

end Asakura.Chapter6
