import Chapter3MultivariateIto
import Chapter4ConstructedScalarIto

open MeasureTheory Set Filter
open scoped ENNReal Topology BigOperators
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false

/-- Multivariate Ito with all derivative integrals constructed from the
original semimartingales. This discharges the integral-existence premises
of the Chapter 3 formula. -/
theorem constructed_multivariate_ito
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T) {d : ℕ}
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X A M : Fin d → ClosedTime T → Ω → ℝ)
    (C : Fin d → Fin d → ClosedTime T → Ω → ℝ)
    (hX : ∀ i, SemimartingaleDecomposition P F (X i) (A i) (M i))
    (hC : ∀ i j, LocalCovarianceWitness P F (M i) (M j) (C i j))
    (f : (Fin d → ℝ) → ℝ) (hf : ContDiff ℝ 2 f)
    (c : ℕ → ℝ) (hc : ∀ k, 0 ≤ c k) (hcm : Monotone c)
    (hcT : ∀ k, (c k:EReal) < T)
    (hcc : ∀ t, t < ⊤ → ∃ k, t < realTimeClamp (T := T) (c k)) :
    ∃ (Z : Fin d → ClosedTime T → Ω → ℝ)
      (J : Fin d → Fin d → ClosedTime T → Ω → ℝ),
      (∀ i, SemimartingaleIntegralFormula P F c hc (A i) (M i)
        (fun z => fderiv ℝ f (fun k => X k (realTimeClamp z.2) z.1) (Pi.single i 1)) (Z i)) ∧
      (∀ i j, VariationIntegralFormula P c hc (C i j)
        (fun z => fderiv ℝ (fderiv ℝ f) (fun k => X k (realTimeClamp z.2) z.1)
          (Pi.single i 1) (Pi.single j 1)) (J i j)) ∧
      ∀ᵐ w ∂P, ∀ t, t < ⊤ →
        f (fun i => X i t w) = f (fun i => X i ⊥ w)+
          (∑ i, Z i t w)+(∑ i, ∑ j, J i j t w)/2 := by
  classical
  let W := fun t w i => X i t w
  have hXm i t (ht : t < ⊤) : Measurable[F t] (X i t) := by
    have he := funext ((hX i).decomposition t ht)
    rw [he]
    exact ((hX i).variation.adapted t ht).add ((hX i).martingale.adapted P F t ht)
  have hWm t (ht : t < ⊤) : Measurable[F t] (W t) := by
    letI : MeasurableSpace Ω := F t
    exact Measurable.of_eval fun i => hXm i t ht
  have hWc w t (ht : t < ⊤) : ContinuousAt (fun s => W s w) t :=
    continuousAt_pi.mpr fun i => (hX i).continuous w t ht
  have hd := hf.continuous_fderiv (by norm_num)
  have hdd := (hf.fderiv_right (by norm_num : (1:WithTop ℕ∞)+1 ≤ 2)).continuous_fderiv (by norm_num)
  let D := fun i t w => fderiv ℝ f (W t w) (Pi.single i 1)
  let E := fun i j t w => fderiv ℝ (fderiv ℝ f) (W t w) (Pi.single i 1) (Pi.single j 1)
  have hDm i t (ht : t < ⊤) : Measurable[F t] (D i t) :=
    (hd.clm_apply continuous_const).measurable.comp (hWm t ht)
  have hDc i w t (ht : t < ⊤) : ContinuousAt (fun s => D i s w) t :=
    (hd.clm_apply continuous_const).continuousAt.comp (hWc w t ht)
  have hEm i j t (ht : t < ⊤) : Measurable[F t] (E i j t) :=
    ((hdd.clm_apply continuous_const).clm_apply continuous_const).measurable.comp (hWm t ht)
  have hEc i j w t (ht : t < ⊤) : ContinuousAt (fun s => E i j s w) t :=
    ((hdd.clm_apply continuous_const).clm_apply continuous_const).continuousAt.comp (hWc w t ht)
  have hz i : ∃ Z, SemimartingaleIntegralFormula P F c hc (A i) (M i)
      (fun z => D i (realTimeClamp z.2) z.1) Z := by
    obtain ⟨I,N,hIN,hI,hN⟩ := continuous_semimartingale_integral_exists
      P hT F hF hle hnull (X i) (A i) (M i) (D i) (hX i) (hDm i) (hDc i) c hc hcm hcT hcc
    exact ⟨fun t w => I t w+N t w,I,N,hIN,hI,hN⟩
  have hj i j : ∃ J, VariationIntegralFormula P c hc (C i j)
      (fun z => E i j (realTimeClamp z.2) z.1) J := by
    have hCv := covariance_adapted_variation P F hF hle (hX i).martingale (hX j).martingale (hC i j)
    have hCc w t (ht : t < ⊤) : ContinuousAt (fun s => C i j s w) t := by
      have hh := (((hX i).martingale.path P F w t ht).mul
        ((hX j).martingale.path P F w t ht)).sub ((hC i j).defect.path P F w t ht)
      convert hh using 1
      funext s
      simp only [Pi.sub_apply,Pi.mul_apply,sub_sub_cancel]
    obtain ⟨J,_,_,hJ⟩ := continuous_adapted_variation_exists P F hF hnull c hc hcm hcT hcc
      (C i j) hCv hCc (fun z => E i j (realTimeClamp z.2) z.1)
      (open_process_real_regularity F (E i j) (hEm i j) (hEc i j)).1
      (open_process_real_regularity F (E i j) (hEm i j) (hEc i j)).2
    exact ⟨J,hJ⟩
  choose Z hZ using hz
  choose J hJ using hj
  exact ⟨Z,J,hZ,hJ,multivariate_ito_formula P hT F hF hle hnull X A M Z C J hX hC
    f hf c hc hcT hcc hZ hJ⟩

end Asakura.Chapter5
