import Chapter3ScalarItoPartition
import Chapter3CommonOscillationPartition

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- Scalar C² Ito formula with the common partition constructed internally.
Only the actual integrals defined in Chapter 2 are inputs. -/
theorem scalar_ito_formula
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X A M C Z J : ClosedTime T → Ω → ℝ)
    (hX : SemimartingaleDecomposition P F X A M)
    (hC : LocalCovarianceWitness P F M M C)
    (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (c : ℕ → ℝ) (hc : ∀ k, 0 ≤ c k) (hcT : ∀ k, (c k:EReal) < T)
    (hcc : ∀ t, t < ⊤ → ∃ k, t < realTimeClamp (T := T) (c k))
    (hZ : SemimartingaleIntegralFormula P F c hc A M
      (fun z => deriv f (X (realTimeClamp z.2) z.1)) Z)
    (hJ : VariationIntegralFormula P c hc C
      (fun z => iteratedDeriv 2 f (X (realTimeClamp z.2) z.1)) J) :
    ∀ᵐ ω ∂P, ∀ t, t < ⊤ → f (X t ω) = f (X ⊥ ω)+Z t ω+J t ω/2 := by
  have hXm t (ht : t < ⊤) : Measurable[F t] (X t) := by
    have heq : X t = fun ω => A t ω+M t ω := funext (hX.decomposition t ht)
    rw [heq]
    exact (hX.variation.adapted t ht).add (hX.martingale.adapted P F t ht)
  let D := fun t ω => deriv f (X t ω)
  let E := fun t ω => iteratedDeriv 2 f (X t ω)
  have hd : Continuous (deriv f) := hf.continuous_deriv (by norm_num)
  have he : Continuous (iteratedDeriv 2 f) := hf.continuous_iteratedDeriv 2 le_rfl
  have hdm t (ht : t < ⊤) : Measurable[F t] (D t) := hd.measurable.comp (hXm t ht)
  have hem t (ht : t < ⊤) : Measurable[F t] (E t) := he.measurable.comp (hXm t ht)
  have hdc ω t (ht : t < ⊤) : ContinuousAt (fun s => D s ω) t :=
    hd.continuousAt.comp (hX.continuous ω t ht)
  have hec ω t (ht : t < ⊤) : ContinuousAt (fun s => E s ω) t :=
    he.continuousAt.comp (hX.continuous ω t ht)
  let V : Fin 4 → ClosedTime T → Ω → ℝ := ![A,M,D,E]
  have hVm i t (ht : t < ⊤) : Measurable[F t] (V i t) := by
    fin_cases i
    · exact hX.variation.adapted t ht
    · exact hX.martingale.adapted P F t ht
    · exact hdm t ht
    · exact hem t ht
  have hVc i ω t (ht : t < ⊤) : ContinuousAt (fun s => V i s ω) t := by
    fin_cases i
    · exact hX.variation_continuous P F ω t ht
    · exact hX.martingale.path P F ω t ht
    · exact hdc ω t ht
    · exact hec ω t ht
  obtain ⟨u,_,_,_,hum,hut,huc⟩ := positive_real_time_exhaustion hT
  obtain ⟨τ,h0,hs,hm,ht,hco,hb,hL⟩ := common_oscillation_partition P F hF hle V hVm hVc
    (fun n => realTimeClamp (u n)) hum.monotone hut huc
  letI : Nonempty (Iio (⊤ : ClosedTime T)) := ⟨⟨⊥,hT⟩⟩
  let q := TopologicalSpace.denseSeq (Iio (⊤ : ClosedTime T))
  exact scalar_ito_from_common_partition P hT F hF hle hnull X A M C Z J hX hC f hf hXm
    c hc hcT hcc hZ hJ τ hs hm ht h0 hco q
    (TopologicalSpace.denseRange_denseSeq _) (fun n j i => hL 0 n j (q i).val)
    (fun n j i => hL 1 n j (q i).val) (fun n j i => hL 2 n j (q i).val)
    (fun n j i => hL 3 n j (q i).val)

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.scalar_ito_formula
