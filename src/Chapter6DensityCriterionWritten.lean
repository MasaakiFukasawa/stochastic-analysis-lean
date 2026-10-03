import Chapter6GeneralDensityTransform
import Chapter3LocalSemimartingale

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

/-- The density criterion for a given P-semimartingale, with the correction
constructed from its actual martingale part. Both implications follow from
the proved drift transform and uniqueness of the finite-variation part. -/
theorem density_criterion_written {Ω : Type*} {m : MeasurableSpace Ω}
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t N,MeasurableSet[m] N → P N=0 → MeasurableSet[F t] N)
    (d : Ω → ℝ≥0) (hd : Measurable d) (hdi : Integrable (fun w => (d w:ℝ)) P)
    (hp : ∀ᵐ w ∂P,0<(d w:ℝ)) (hQ : Q=P.withDensity (fun w => (d w:ℝ≥0∞)))
    (M : ClosedTime T → Ω → ℝ) (hMa : ∀ t,Measurable[F t] (M t))
    (hMc : ∀ w t,t<⊤ → ContinuousAt (fun s => M s w) t) (hMp : ∀ t w,0<M t w)
    (hME : ∀ t,M t=ᵐ[P] P[(fun w => (d w:ℝ))|F t])
    (X A Y C : ClosedTime T → Ω → ℝ) (hX : SemimartingaleDecomposition P F X A Y)
    (hC : LocalCovarianceWitness P F (fun t w => M t w-M ⊥ w) Y C)
    (c : ℕ → ℝ) (hc : ∀ n,0≤c n) (hcm : Monotone c) (hcT : ∀ n,(c n:EReal)<T)
    (hcc : ∀ t,t<⊤ → ∃ n,t<realTimeClamp (T := T) (c n)) :
    ∃ K,AdaptedLocalVariationWitness F K ∧
      (∀ w t,t<⊤ → ContinuousAt (fun s => K s w) t) ∧
      VariationIntegralFormula P c hc C (fun z => (M (realTimeClamp z.2) z.1)⁻¹) K ∧
      (LocalMProcessWitness Q F X ↔ LocalMProcessWitness P F (fun t w => X t w+K t w)) := by
  obtain ⟨K,hKv,hKc,hKI,hN⟩ := general_density_transform P Q hT F hF hle hnull
    d hd hdi hp hQ M hMa hMc hMp hME Y C hX.martingale hC c hc hcm hcT hcc
  have hae (p : Ω → Prop) : (∀ᵐ w ∂Q,p w) ↔ (∀ᵐ w ∂P,p w) := by
    rw [hQ]
    exact positive_density_ae_iff P d hd hp p
  have hXa t (ht : t<⊤) : Measurable[F t] (X t) := by
    have he : X t=(fun w => A t w+Y t w) := funext (hX.decomposition t ht)
    rw [he]
    exact (hX.variation.adapted t ht).add (hX.martingale.adapted P F t ht)
  have hDQ : SemimartingaleDecomposition Q F X (fun t w => A t w+K t w) (fun t w => Y t w-K t w) :=
    ⟨hX.variation.add hKv hF,hN,hX.continuous,fun t ht w => by rw [hX.decomposition t ht w]; ring⟩
  have hDP : SemimartingaleDecomposition P F (fun t w => X t w+K t w) (fun t w => A t w+K t w) Y :=
    ⟨hX.variation.add hKv hF,hX.martingale,fun w t ht => (hX.continuous w t ht).add (hKc w t ht),
      fun t ht w => by rw [hX.decomposition t ht w]; ring⟩
  refine ⟨K,hKv,hKc,hKI,?_⟩
  constructor
  · intro hlocal
    have hz := hDQ.unique Q F hF hle (local_martingale_semimartingale_decomposition Q hT F hF X hlocal)
    have hzP := (hae _).mp hz
    apply Asakura.Chapter3Complete.LocalMProcessWitness.congr_ae_open P F hF hX.martingale
    · intro t ht
      exact (hXa t ht).add (hKv.adapted t ht)
    · intro w t ht
      exact (hX.continuous w t ht).add (hKc w t ht)
    · filter_upwards [hzP] with w hw
      intro t ht
      have he := (hw t ht).1
      have hd := hX.decomposition t ht w
      change A t w+K t w=0 at he
      linarith
  · intro hlocal
    have hz := hDP.unique P F hF hle (local_martingale_semimartingale_decomposition P hT F hF _ hlocal)
    have hzQ := (hae _).mpr hz
    apply Asakura.Chapter3Complete.LocalMProcessWitness.congr_ae_open Q F hF hN hXa hX.continuous
    filter_upwards [hzQ] with w hw
    intro t ht
    have he := (hw t ht).1
    have hd := hX.decomposition t ht w
    change A t w+K t w=0 at he
    change Y t w-K t w=X t w
    linarith

end Asakura.Chapter6
