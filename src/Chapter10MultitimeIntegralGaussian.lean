import Chapter10StoppedCoefficientRegularity
import Chapter10DeterministicIntegralGaussian
import Chapter5StoppedIntegralFormula
import Chapter6FiniteWeightedIto

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter6 Asakura.Chapter8
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- Joint Gaussianity at arbitrary finitely many times of actual deterministic
Itô integrals, including degenerate coefficient matrices. -/
theorem deterministic_integral_multitime_gaussian {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d p : ℕ} (B : BrownianSystem P d)
    (G : Fin p → Fin d → ℝ → ℝ) (hG : ∀ i j,Continuous (G i j))
    (N : Fin p → Fin d → HalfClosedTime → Ω → ℝ)
    (hN : ∀ i j,LocalMProcessWitness P B.F (N i j))
    (hNI : ∀ i j,ItoCovarianceFormula P B.F (B.W j) (fun z => G i j z.2) (N i j))
    (R : ℝ) (hR : 0≤R) (τ : Fin p → ℝ) (hτ : ∀ i,τ i∈Icc 0 R) :
    HasGaussianLaw (fun w i => ∑ j,N i j (realTimeClamp (τ i)) w) P := by
  classical
  let X := fun w i => ∑ j,N i j (realTimeClamp (τ i)) w
  have hm : Measurable X := Measurable.of_eval (fun i => Finset.measurable_sum _
    (fun j _ => ((hN i j).adapted P B.F _ (half_real_time_finite (τ i))).mono (B.le _) le_rfl))
  have ht : (0:EReal)<⊤ := by simp
  have hstop i : ∀ t,MeasurableSet[B.F t] {w : Ω | realTimeClamp (τ i)≤t} := by
    intro t
    by_cases h : realTimeClamp (T := (⊤:EReal)) (τ i)≤t <;> simp [h]
  let Ns := fun i j t w => N i j (min (realTimeClamp (τ i)) t) w
  have hNs i j : LocalMProcessWitness P B.F (Ns i j) :=
    (hN i j).stopped P B.F B.mono B.le (fun _ => realTimeClamp (τ i)) (hstop i)
  have hIs i j : ItoCovarianceFormula P B.F (B.W j)
      (fun z => (Ioc 0 (τ i)).indicator (G i j) z.2) (Ns i j) :=
    stopped_ito_covariance_formula P ht B.F B.mono B.le B.null _ _ _
      (B.martingale j) (hN i j) (fun _ => (hG i j).measurable) (hNI i j) (τ i) (hτ i).1
  refine ⟨hm.aemeasurable,?_⟩
  apply isGaussian_of_map_eq_gaussianReal
  intro L
  let v := fun i => L (Pi.single i 1)
  have hrepr (x : Fin p → ℝ) : L x=∑ i,v i*x i := by
    have hx : x=∑ i,x i • Pi.single i (1:ℝ) := by
      ext j
      simp [Pi.single_apply,Finset.sum_apply]
    calc
      L x = L (∑ i,x i • Pi.single i (1:ℝ)) := congrArg L hx
      _ = ∑ i,v i*x i := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i _
        simp only [map_smul,smul_eq_mul,v,mul_comm]
  let H := fun j s => ∑ i,v i*(Ioc 0 (τ i)).indicator (G i j) s
  let Y := fun j t w => ∑ i,v i*Ns i j t w
  have hY j := finite_weighted_ito P ht B.F B.mono B.le B.null (B.W j) (B.martingale j)
    (fun i z => (Ioc 0 (τ i)).indicator (G i j) z.2) (fun i => Ns i j)
    (fun i => hNs i j) (fun i => hIs i j) v
  obtain ⟨hHm,hi,hpi⟩ := stopped_coefficient_regularity G hG v τ
  have hl := integrable_deterministic_noise_law P B H hHm hi hpi Y
    (fun j => (hY j).1) (fun j => (hY j).2) R hR
  refine ⟨0,⟨∫ s in 0..R,∑ j,(H j s)^2,
    intervalIntegral.integral_nonneg_of_forall hR (fun _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))⟩,?_⟩
  rw [Measure.map_map L.continuous.measurable hm]
  have he : L ∘ X=(fun w => ∑ j,Y j (realTimeClamp R) w) := by
    funext w
    rw [Function.comp_apply,hrepr]
    dsimp only [X,Y,Ns]
    simp only [min_eq_left (real_time_clamp_mono (hτ _).2)]
    simp only [Finset.mul_sum]
    exact Finset.sum_comm
  rw [he]
  exact hl.map_eq

end Asakura.Chapter10
