import Chapter10DeterministicIntegralLinearity
import Chapter3CommonOscillationPartition

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- A finite linear identity between the left endpoint sums passes to the
actual stochastic integrals. This proves finite matrix integral linearity
in both coefficients and integrators with one common partition. -/
theorem finite_deterministic_integral_linearity_ae {Ω ι : Type*} [m : MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (X A M Z : ι → HalfClosedTime → Ω → ℝ)
    (Y D N U : HalfClosedTime → Ω → ℝ)
    (hX : ∀ i,SemimartingaleDecomposition P F (X i) (A i) (M i))
    (hY : SemimartingaleDecomposition P F Y D N)
    (H : ι → HalfClosedTime → ℝ) (G : HalfClosedTime → ℝ)
    (hH : ∀ i t,t<⊤ → ContinuousAt (H i) t) (hG : ∀ t,t<⊤ → ContinuousAt G t)
    (c : ℕ → ℝ) (hc : ∀ k,0≤c k) (hcT : ∀ k,(c k:EReal)<⊤)
    (hcc : ∀ t : HalfClosedTime,t<⊤ → ∃ k,t<realTimeClamp (c k))
    (hZ : ∀ i,SemimartingaleIntegralFormula P F c hc (A i) (M i) (fun z => H i (realTimeClamp z.2)) (Z i))
    (hU : SemimartingaleIntegralFormula P F c hc D N (fun z => G (realTimeClamp z.2)) U)
    (he : ∀ᵐ w ∂P,∀ s t,s<⊤ → t<⊤ → G s*(Y t w-Y s w)=∑ i,H i s*(X i t w-X i s w)) :
    ∀ᵐ w ∂P,∀ t,t<⊤ → U t w=∑ i,Z i t w := by
  classical
  obtain ⟨u,hu,hum,huT,_,_,huco⟩ := positive_real_time_exhaustion (T := (⊤:EReal)) (by simp)
  let V : Option ι → HalfClosedTime → Ω → ℝ := fun i t _ => i.elim (G t) (fun j => H j t)
  have hVc : ∀ i w t,t<⊤ → ContinuousAt (fun s => V i s w) t := by
    intro i w t ht
    cases i with
    | none => exact hG t ht
    | some i => exact hH i t ht
  obtain ⟨τ,h0,hs,hm,ht,hco,_,hb⟩ := common_oscillation_partition P F hF hle V
    (fun _ _ _ => measurable_const) hVc (fun n => realTimeClamp (u n))
    (fun i j hij => real_time_clamp_mono (hum.monotone hij))
    (fun n => real_time_below _ (hu n).le (huT n)) huco
  letI : Nonempty (Iio (⊤ : HalfClosedTime)) := ⟨⟨⊥,by change (0:EReal)<⊤; simp⟩⟩
  let q := TopologicalSpace.denseSeq (Iio (⊤ : HalfClosedTime))
  have hap (i : Option ι) (X A M Z : HalfClosedTime → Ω → ℝ)
      (hX : SemimartingaleDecomposition P F X A M)
      (hZ : SemimartingaleIntegralFormula P F c hc A M (fun z => V i (realTimeClamp z.2) z.1) Z)
      (b : HalfClosedTime) (hb' : b<⊤) :
      ∀ᵐ w ∂P,TendstoUniformly
        (fun n t => ∑' j,V i (τ n j w) w*(X (min (τ n (j+1) w) (min b t)) w-X (min (τ n j w) (min b t)) w))
        (fun t => Z (min b t) w) atTop := by
    exact semimartingale_integral_approximation P (by simp : (0:EReal)<⊤) F hF hle hnull
      X A M (V i) Z hX (fun _ _ => measurable_const) (hVc i)
      c hc hcT hcc hZ τ hs hm ht h0 hco q (TopologicalSpace.denseRange_denseSeq _)
      (fun n j k => hb i n j (q k).val) b hb'
  have hlocal b (hb' : b<⊤) : ∀ᵐ w ∂P,∀ t,U (min b t) w=∑ i,Z i (min b t) w := by
    have hZi := ae_all_iff.mpr (fun i => hap (some i) (X i) (A i) (M i) (Z i) (hX i) (hZ i) b hb')
    filter_upwards [hZi,hap none Y D N U hY hU b hb',he] with w hz hu hew
    intro t
    have heq n : (∑' j,G (τ n j w)*(Y (min (τ n (j+1) w) (min b t)) w-Y (min (τ n j w) (min b t)) w))=
        ∑ i,∑' j,H i (τ n j w)*(X i (min (τ n (j+1) w) (min b t)) w-X i (min (τ n j w) (min b t)) w) := by
      obtain ⟨N,hN⟩ := hco n w b hb'
      have hcut := (min_le_left b t).trans hN.le
      rw [partition_sum_truncates_before_endpoint _ (hm n w) (fun t => Y t w) (fun j => G (τ n j w)) N _ hcut]
      have htr i := partition_sum_truncates_before_endpoint (fun j => τ n j w) (hm n w)
        (fun t => X i t w) (fun j => H i (τ n j w)) N (min b t) hcut
      simp_rw [htr]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hleft : τ n j w≤min b t
      · have hs' : min (τ n j w) (min b t)<⊤ := (min_le_left _ _).trans_lt (ht n j w)
        have ht' : min (τ n (j+1) w) (min b t)<⊤ :=
          (min_le_right _ _).trans_lt ((min_le_left _ _).trans_lt hb')
        have hh := hew (min (τ n j w) (min b t)) (min (τ n (j+1) w) (min b t)) hs' ht'
        simpa only [min_eq_left hleft] using hh
      · have hjt : min b t≤τ n j w := le_of_lt (lt_of_not_ge hleft)
        have hjt' := hjt.trans (hm n w (Nat.le_succ j))
        simp only [min_eq_right hjt,min_eq_right hjt',sub_self,mul_zero,Finset.sum_const_zero]
    have hsum := tendsto_finset_sum Finset.univ (fun i _ => (hz i).tendsto_at t)
    exact tendsto_nhds_unique (hu.tendsto_at t) (hsum.congr (fun n => (heq n).symm))
  have hall : ∀ᵐ w ∂P,∀ k,∀ t,U (min (realTimeClamp (c k)) t) w=
      ∑ i,Z i (min (realTimeClamp (c k)) t) w :=
    ae_all_iff.mpr (fun k => hlocal _ (real_time_below _ (hc k) (hcT k)))
  filter_upwards [hall] with w hw
  intro t ht
  obtain ⟨k,hk⟩ := hcc t ht
  simpa only [min_eq_right hk.le] using hw k t

end Asakura.Chapter10
