import Chapter3ItoCompositionDecomposition

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

theorem c2_ito_data_exists
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T) {d : ℕ}
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X A M : Fin d → ClosedTime T → Ω → ℝ)
    (C : Fin d → Fin d → ClosedTime T → Ω → ℝ)
    (hX : ∀ i, SemimartingaleDecomposition P F (X i) (A i) (M i))
    (hC : ∀ i j, LocalCovarianceWitness P F (M i) (M j) (C i j))
    (f : (Fin d → ℝ) → ℝ) (hf : ContDiff ℝ 2 f)
    (c : ℕ → ℝ) (hc : ∀ k, 0 ≤ c k) (hcm : Monotone c) (hcT : ∀ k, (c k:EReal) < T)
    (hcc : ∀ t, t < ⊤ → ∃ k, t < realTimeClamp (T := T) (c k)) :
    ∃ I N : Fin d → ClosedTime T → Ω → ℝ,
    ∃ J : Fin d → Fin d → ClosedTime T → Ω → ℝ,
      (∀ i, SemimartingaleDecomposition P F (fun t ω => I i t ω+N i t ω) (I i) (N i)) ∧
      (∀ i, VariationIntegralFormula P c hc (A i)
        (fun z => fderiv ℝ f (fun k => X k (realTimeClamp z.2) z.1) (Pi.single i 1)) (I i)) ∧
      (∀ i, ItoCovarianceFormula P F (M i)
        (fun z => fderiv ℝ f (fun k => X k (realTimeClamp z.2) z.1) (Pi.single i 1)) (N i)) ∧
      (∀ i j, AdaptedLocalVariationWitness F (J i j)) ∧
      (∀ i j ω t, t < ⊤ → ContinuousAt (fun s => J i j s ω) t) ∧
      (∀ i j, VariationIntegralFormula P c hc (C i j)
        (fun z => fderiv ℝ (fderiv ℝ f) (fun k => X k (realTimeClamp z.2) z.1)
          (Pi.single i 1) (Pi.single j 1)) (J i j)) := by
  classical
  let W := fun t ω i => X i t ω
  have hXm i t (ht : t < ⊤) : Measurable[F t] (X i t) := by
    have heq : X i t = fun ω => A i t ω+M i t ω := funext ((hX i).decomposition t ht)
    rw [heq]
    exact ((hX i).variation.adapted t ht).add ((hX i).martingale.adapted P F t ht)
  have hWm t (ht : t < ⊤) : Measurable[F t] (W t) := by
    letI : MeasurableSpace Ω := F t
    exact Measurable.of_eval (fun i => hXm i t ht)
  have hWc ω t (ht : t < ⊤) : ContinuousAt (fun s => W s ω) t :=
    continuousAt_pi.mpr (fun i => (hX i).continuous ω t ht)
  let D := fun i t ω => fderiv ℝ f (W t ω) (Pi.single i 1)
  let E := fun i j t ω => fderiv ℝ (fderiv ℝ f) (W t ω) (Pi.single i 1) (Pi.single j 1)
  have hdf := hf.continuous_fderiv (by norm_num)
  have hddf := (hf.fderiv_right (by norm_num : (1:WithTop ℕ∞)+1 ≤ 2)).continuous_fderiv (by norm_num)
  have hdfi i : Continuous (fun x => fderiv ℝ f x (Pi.single i 1)) := hdf.clm_apply continuous_const
  have hddfij i j : Continuous (fun x => fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1)) :=
    (hddf.clm_apply continuous_const).clm_apply continuous_const
  have hdm i t (ht : t < ⊤) : Measurable[F t] (D i t) := (hdfi i).measurable.comp (hWm t ht)
  have hem i j t (ht : t < ⊤) : Measurable[F t] (E i j t) := (hddfij i j).measurable.comp (hWm t ht)
  have hdc i ω t (ht : t < ⊤) : ContinuousAt (fun s => D i s ω) t :=
    (hdfi i).continuousAt.comp (hWc ω t ht)
  have hec i j ω t (ht : t < ⊤) : ContinuousAt (fun s => E i j s ω) t :=
    (hddfij i j).continuousAt.comp (hWc ω t ht)
  choose I N hIN hI hN using fun i => continuous_semimartingale_integral_exists P hT F hF hle hnull
    (X i) (A i) (M i) (D i) (hX i) (hdm i) (hdc i) c hc hcm hcT hcc
  have hj i j := continuous_adapted_variation_exists P F hF hnull c hc hcm hcT hcc (C i j)
    (covariance_adapted_variation P F hF hle (hX i).martingale (hX j).martingale (hC i j))
    (fun ω t ht => by
      have hh := (((hX i).martingale.path P F ω t ht).mul ((hX j).martingale.path P F ω t ht)).sub
        ((hC i j).defect.path P F ω t ht)
      convert hh using 1
      funext s
      simp only [Pi.sub_apply,Pi.mul_apply,sub_sub_cancel])
    (fun z => E i j (realTimeClamp z.2) z.1)
    (open_process_real_regularity F (E i j) (hem i j) (hec i j)).1
    (open_process_real_regularity F (E i j) (hem i j) (hec i j)).2
  choose J hJv hJc hJ using hj
  exact ⟨I,N,J,hIN,hI,hN,hJv,hJc,hJ⟩

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.c2_ito_data_exists
