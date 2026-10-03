import Chapter10DeterministicIntegralHistory

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- Actual deterministic-coefficient semimartingale integrals are linear
in the integrator. A common oscillation partition proves the identity from
the previously proved stochastic integral approximation. -/
theorem deterministic_integral_add_integrator {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (X A M Y D N U V Z : HalfClosedTime → Ω → ℝ)
    (hX : SemimartingaleDecomposition P F X A M)
    (hY : SemimartingaleDecomposition P F Y D N)
    (hXY : SemimartingaleDecomposition P F (fun t w => X t w+Y t w)
      (fun t w => A t w+D t w) (fun t w => M t w+N t w))
    (H : HalfClosedTime → ℝ) (hH : ∀ t,t<⊤ → ContinuousAt H t)
    (c : ℕ → ℝ) (hc : ∀ k,0≤c k) (hcT : ∀ k,(c k:EReal)<⊤)
    (hcc : ∀ t : HalfClosedTime,t<⊤ → ∃ k,t<realTimeClamp (c k))
    (hU : SemimartingaleIntegralFormula P F c hc A M (fun z => H (realTimeClamp z.2)) U)
    (hV : SemimartingaleIntegralFormula P F c hc D N (fun z => H (realTimeClamp z.2)) V)
    (hZ : SemimartingaleIntegralFormula P F c hc (fun t w => A t w+D t w)
      (fun t w => M t w+N t w) (fun z => H (realTimeClamp z.2)) Z) :
    ∀ᵐ w ∂P,∀ t,t<⊤ → Z t w=U t w+V t w := by
  obtain ⟨τ,h0,hm,ht,hco,hbound⟩ := deterministic_oscillation_partitions H hH
  have hs : ∀ n j t,MeasurableSet[F t] {w : Ω | τ n j≤t} := by
    intro n j t
    by_cases h : τ n j≤t <;> simp [h]
  letI : Nonempty (Iio (⊤ : HalfClosedTime)) := ⟨⟨⊥,by change (0:EReal)<⊤; simp⟩⟩
  let q := TopologicalSpace.denseSeq (Iio (⊤ : HalfClosedTime))
  have hap (X A M Z : HalfClosedTime → Ω → ℝ)
      (hX : SemimartingaleDecomposition P F X A M)
      (hZ : SemimartingaleIntegralFormula P F c hc A M (fun z => H (realTimeClamp z.2)) Z)
      (b : HalfClosedTime) (hb : b<⊤) :
      ∀ᵐ w ∂P,TendstoUniformly
        (fun n t => ∑' j,H (τ n j)*(X (min (τ n (j+1)) (min b t)) w-X (min (τ n j) (min b t)) w))
        (fun t => Z (min b t) w) atTop := by
    exact semimartingale_integral_approximation P (by simp : (0:EReal)<⊤) F hF hle hnull
      X A M (fun t _ => H t) Z hX (fun _ _ => measurable_const) (fun _ t ht => hH t ht)
      c hc hcT hcc hZ (fun n j _ => τ n j) hs (fun n _ => hm n) (fun n j _ => ht n j)
      (fun n _ => h0 n) (fun n _ t ht => hco n t ht) q (TopologicalSpace.denseRange_denseSeq _)
      (by
        intro n j i
        simpa using eLpNorm_le_of_ae_bound (μ := P) (p := ∞) aestronglyMeasurable_const
          (ae_of_all _ fun _ => hbound n j (q i).val)) b hb
  have hlocal b (hb : b<⊤) : ∀ᵐ w ∂P,∀ t,Z (min b t) w=U (min b t) w+V (min b t) w := by
    filter_upwards [hap X A M U hX hU b hb,hap Y D N V hY hV b hb,
      hap _ _ _ Z hXY hZ b hb] with w hu hv hz
    intro t
    have he n := linear_partition_sum_add (fun t => X t w) (fun t => Y t w)
      (fun t => X t w+Y t w) H (τ n) (hm n) b hb (hco n) (fun _ _ => rfl) t
    have hh := (hu.tendsto_at t).add (hv.tendsto_at t)
    have hh' := hh.congr (fun n => (he n).symm)
    exact tendsto_nhds_unique (hz.tendsto_at t) hh'
  have hall : ∀ᵐ w ∂P,∀ k,∀ t,Z (min (realTimeClamp (c k)) t) w=
      U (min (realTimeClamp (c k)) t) w+V (min (realTimeClamp (c k)) t) w := by
    exact ae_all_iff.mpr (fun k => hlocal _ (real_time_below _ (hc k) (hcT k)))
  filter_upwards [hall] with w hw
  intro t ht
  obtain ⟨k,hk⟩ := hcc t ht
  simpa only [min_eq_right hk.le] using hw k t

end Asakura.Chapter10
