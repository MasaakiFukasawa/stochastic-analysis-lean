import Chapter10DeterministicIntegralLinearity

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- The unit semimartingale integral equals the integrator minus its initial
value. This supplies the identity step when undoing the observation matrix. -/
theorem deterministic_integral_stopped_integrator {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (X A M Z : HalfClosedTime → Ω → ℝ) (hX : SemimartingaleDecomposition P F X A M)
    (H : HalfClosedTime → ℝ) (hH : ∀ t,t<⊤ → ContinuousAt H t)
    (R : HalfClosedTime) (hstop : ∀ w t,X (min R t) w=X t w)
    (c : ℕ → ℝ) (hc : ∀ k,0≤c k) (hcT : ∀ k,(c k:EReal)<⊤)
    (hcc : ∀ t : HalfClosedTime,t<⊤ → ∃ k,t<realTimeClamp (c k))
    (hZ : SemimartingaleIntegralFormula P F c hc A M (fun z => H (realTimeClamp z.2)) Z) :
    ∀ᵐ w ∂P,∀ t,t<⊤ → Z t w=Z (min R t) w := by
  obtain ⟨τ,h0,hm,ht,hco,hbound⟩ := deterministic_oscillation_partitions H hH
  have hs : ∀ n j t,MeasurableSet[F t] {w : Ω | τ n j≤t} := by
    intro n j t
    by_cases h : τ n j≤t <;> simp [h]
  letI : Nonempty (Iio (⊤ : HalfClosedTime)) := ⟨⟨⊥,by change (0:EReal)<⊤; simp⟩⟩
  let q := TopologicalSpace.denseSeq (Iio (⊤ : HalfClosedTime))
  have hlocal b (hb : b<⊤) : ∀ᵐ w ∂P,∀ t,Z (min b t) w=Z (min b (min R t)) w := by
    have hap := semimartingale_integral_approximation P (by simp : (0:EReal)<⊤) F hF hle hnull
      X A M (fun t _ => H t) Z hX (fun _ _ => measurable_const) (fun _ => hH)
      c hc hcT hcc hZ (fun n j _ => τ n j) hs (fun n _ => hm n) (fun n j _ => ht n j)
      (fun n _ => h0 n) (fun n _ t ht => hco n t ht) q (TopologicalSpace.denseRange_denseSeq _)
      (by
        intro n j i
        simpa using eLpNorm_le_of_ae_bound (μ := P) (p := ∞) aestronglyMeasurable_const
          (ae_of_all _ fun _ => hbound n j (q i).val)) b hb
    filter_upwards [hap] with w hw
    intro t
    have hx a : X (min a (min b t)) w=X (min a (min b (min R t))) w := by
      rw [←hstop w (min a (min b t))]
      congr 1
      ac_rfl
    have he n : (∑' j,H (τ n j)*(X (min (τ n (j+1)) (min b t)) w-X (min (τ n j) (min b t)) w))=
        ∑' j,H (τ n j)*(X (min (τ n (j+1)) (min b (min R t))) w-X (min (τ n j) (min b (min R t))) w) := by
      apply tsum_congr
      intro j
      rw [hx,hx]
    exact tendsto_nhds_unique (hw.tendsto_at t)
      ((hw.tendsto_at (min R t)).congr (fun n => (he n).symm))
  have hall := ae_all_iff.mpr (fun k => hlocal (realTimeClamp (c k)) (real_time_below _ (hc k) (hcT k)))
  filter_upwards [hall] with w hw
  intro t ht
  obtain ⟨k,hk⟩ := hcc t ht
  simpa only [min_eq_right hk.le,min_eq_right ((min_le_right R t).trans hk.le)] using hw k t

end Asakura.Chapter10
