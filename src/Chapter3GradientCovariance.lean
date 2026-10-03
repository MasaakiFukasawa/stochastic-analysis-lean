import Chapter3C2Composition
import Chapter3GradientCalculus
import Chapter3ItoVariationCovariance
import Chapter3OpenPathMeasurable

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 3400000
set_option backward.isDefEq.respectTransparency false

/-- Construct the semimartingale gradient and compute its covariation with
its corresponding coordinate. The Hessian correction is not assumed. -/
theorem c3_gradient_covariance
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T) {d : ℕ}
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X A M : Fin d → ClosedTime T → Ω → ℝ)
    (C J : Fin d → Fin d → ClosedTime T → Ω → ℝ)
    (hX : ∀ i, SemimartingaleDecomposition P F (X i) (A i) (M i))
    (hC : ∀ i j, LocalCovarianceWitness P F (M i) (M j) (C i j))
    (f : (Fin d → ℝ) → ℝ) (hf : ContDiff ℝ 3 f)
    (c : ℕ → ℝ) (hc : ∀ k, 0 ≤ c k) (hcm : Monotone c) (hcT : ∀ k, (c k:EReal) < T)
    (hcc : ∀ t, t < ⊤ → ∃ k, t < realTimeClamp (T := T) (c k))
    (hJc : ∀ i j ω t, t < ⊤ → ContinuousAt (fun s => J i j s ω) t)
    (hJ : ∀ i j, VariationIntegralFormula P c hc (C i j)
      (fun z => fderiv ℝ (fderiv ℝ f) (fun k => X k (realTimeClamp z.2) z.1)
        (Pi.single i 1) (Pi.single j 1)) (J i j)) :
    ∃ B L D : Fin d → ClosedTime T → Ω → ℝ,
      (∀ i, SemimartingaleDecomposition P F
        (fun t ω => fderiv ℝ f (fun k => X k t ω) (Pi.single i 1)) (B i) (L i)) ∧
      (∀ i, LocalCovarianceWitness P F (L i) (M i) (D i)) ∧
      ∀ᵐ ω ∂P, ∀ i t, t < ⊤ → D i t ω = ∑ j, J j i t ω := by
  classical
  let g := fun i x => fderiv ℝ f x (Pi.single i 1)
  have hg i : ContDiff ℝ 2 (g i) := coordinate_gradient_contDiff f hf i
  choose B L N hL hN hNI heL using fun i => c2_composition_martingale_part P hT F hF hle hnull
    X A M C hX hC (g i) (hg i) c hc hcm hcT hcc
  have hj i j : ∃ D, LocalCovarianceWitness P F (N i j) (M i) D ∧
      ∀ᵐ ω ∂P, ∀ t, t < ⊤ → D t ω = J j i t ω := by
    let H := fun z : Ω × ℝ => fderiv ℝ (g i) (fun k => X k (realTimeClamp z.2) z.1) (Pi.single j 1)
    have hHmeas ω : Measurable (fun r => H (ω,r)) := by
      change Measurable (fun r => fderiv ℝ (g i) (fun k => X k (realTimeClamp r) ω) (Pi.single j 1))
      apply open_path_real_measurable (fun t => fderiv ℝ (g i) (fun k => X k t ω) (Pi.single j 1))
      intro t ht
      exact (((hg i).continuous_fderiv (by norm_num)).clm_apply continuous_const).continuousAt.comp
        (continuousAt_pi.mpr (fun k => (hX k).continuous ω t ht))
    have hJi : VariationIntegralFormula P c hc (C j i) H (J j i) := by
      have he : H = (fun z => fderiv ℝ (fderiv ℝ f) (fun k => X k (realTimeClamp z.2) z.1)
          (Pi.single j 1) (Pi.single i 1)) := by
        funext z
        exact coordinate_gradient_fderiv f hf i _ _
      rw [he]
      exact hJ j i
    exact ito_covariance_identified_with_variation_integral P hT F (M j) (N i j) (M i) (C j i) (J j i)
      (hN i j) (hX i).martingale (hC j i) H hHmeas (hNI i j) c hc hcT hcc (hJc j i) hJi
  choose E hE heE using hj
  let D := fun i t ω => ∑ j, E i j t ω
  have hsum i : LocalMProcessWitness P F (fun t ω => ∑ j, N i j t ω) :=
    local_process_finset_sum P F hF hle Finset.univ (N i) (fun j _ => hN i j) (zero_local_process P hT F)
  have hsumC i : LocalCovarianceWitness P F (fun t ω => ∑ j, N i j t ω) (M i) (D i) := by
    have hzero : LocalCovarianceWitness P F (fun _ _ => 0) (M i) (fun _ _ => 0) := by
      refine ⟨?_,?_⟩
      · simpa only [zero_mul,sub_zero] using zero_local_process P hT F
      · simpa only [zero_mul] using (hC i i).variation.smul F 0
    exact local_covariance_finset_sum P F hF hle Finset.univ (N i) (E i) (M i) (fun j _ => hE i j) hzero
  refine ⟨B,L,D,hL,?_,?_⟩
  · intro i
    exact (hsumC i).congr_ae_processes P F hF hle (hsum i) (hX i).martingale (hL i).martingale
      (hX i).martingale ((heL i).mono (fun ω hω t ht => (hω t ht).symm)) (Filter.Eventually.of_forall (fun _ _ _ => rfl))
  · filter_upwards [ae_all_iff.mpr (fun i => ae_all_iff.mpr (heE i))] with ω hω
    intro i t ht
    exact Finset.sum_congr rfl (fun j _ => hω i j t ht)

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.c3_gradient_covariance
