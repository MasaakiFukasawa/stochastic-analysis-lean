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
theorem deterministic_integral_identity {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (X A M Z : HalfClosedTime → Ω → ℝ) (hX : SemimartingaleDecomposition P F X A M)
    (c : ℕ → ℝ) (hc : ∀ k,0≤c k) (hcT : ∀ k,(c k:EReal)<⊤)
    (hcc : ∀ t : HalfClosedTime,t<⊤ → ∃ k,t<realTimeClamp (c k))
    (hZ : SemimartingaleIntegralFormula P F c hc A M (fun _ => 1) Z) :
    ∀ᵐ w ∂P,∀ t,t<⊤ → Z t w=X t w-X ⊥ w := by
  obtain ⟨τ,h0,hm,ht,hco,hbound⟩ := deterministic_oscillation_partitions (fun _ => 1)
    (fun _ _ => continuousAt_const)
  have hs : ∀ n j t,MeasurableSet[F t] {w : Ω | τ n j≤t} := by
    intro n j t
    by_cases h : τ n j≤t <;> simp [h]
  letI : Nonempty (Iio (⊤ : HalfClosedTime)) := ⟨⟨⊥,by change (0:EReal)<⊤; simp⟩⟩
  let q := TopologicalSpace.denseSeq (Iio (⊤ : HalfClosedTime))
  have hlocal b (hb : b<⊤) : ∀ᵐ w ∂P,∀ t,Z (min b t) w=X (min b t) w-X ⊥ w := by
    have hap := semimartingale_integral_approximation P (by simp : (0:EReal)<⊤) F hF hle hnull
      X A M (fun _ _ => 1) Z hX (fun _ _ => measurable_const) (fun _ _ _ => continuousAt_const)
      c hc hcT hcc hZ (fun n j _ => τ n j) hs (fun n _ => hm n) (fun n j _ => ht n j)
      (fun n _ => h0 n) (fun n _ t ht => hco n t ht) q (TopologicalSpace.denseRange_denseSeq _)
      (fun n j i => by simp) b hb
    filter_upwards [hap] with w hw
    intro t
    have he n : (∑' j,(1:ℝ)*(X (min (τ n (j+1)) (min b t)) w-X (min (τ n j) (min b t)) w))=
        X (min b t) w-X ⊥ w := by
      obtain ⟨N,hN⟩ := hco n b hb
      rw [partition_sum_truncates_before_endpoint (τ n) (hm n) (fun t => X t w)
        (fun _ => 1) N _ ((min_le_left _ _).trans hN.le)]
      simp only [one_mul]
      rw [Finset.sum_range_sub (fun j => X (min (τ n j) (min b t)) w),h0,min_bot_left,
        min_eq_right ((min_le_left b t).trans hN.le)]
    exact tendsto_nhds_unique (hw.tendsto_at t) (tendsto_const_nhds.congr (fun n => (he n).symm))
  have hall : ∀ᵐ w ∂P,∀ k,∀ t,Z (min (realTimeClamp (c k)) t) w=
      X (min (realTimeClamp (c k)) t) w-X ⊥ w :=
    ae_all_iff.mpr (fun k => hlocal _ (real_time_below _ (hc k) (hcT k)))
  filter_upwards [hall] with w hw
  intro t ht
  obtain ⟨k,hk⟩ := hcc t ht
  simpa only [min_eq_right hk.le] using hw k t

end Asakura.Chapter10
