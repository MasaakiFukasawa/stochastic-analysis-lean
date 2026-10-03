import Chapter5MultivariateIntegrandRegularity
import Chapter5TimeDensityInitial
import Chapter5ConstructedMultivariateIto

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false

/-- Multivariate Ito with actual constructed stochastic integrals and
ordinary time densities for all drift and covariance terms. -/
theorem multivariate_density_ito
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T) {d : ℕ}
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t ≤ m)
    (hnull : ∀ t N,MeasurableSet[m] N → P N=0 → MeasurableSet[F t] N)
    (X A M : Fin d → ClosedTime T → Ω → ℝ)
    (C : Fin d → Fin d → ClosedTime T → Ω → ℝ)
    (hX : ∀ i,SemimartingaleDecomposition P F (X i) (A i) (M i))
    (hC : ∀ i j,LocalCovarianceWitness P F (M i) (M j) (C i j))
    (f : (Fin d → ℝ) → ℝ) (hf : ContDiff ℝ 2 f)
    (c : ℕ → ℝ) (hc : ∀ n,0 ≤ c n) (hcm : Monotone c)
    (hcT : ∀ n,(c n:EReal)<T)
    (hcc : ∀ t,t<⊤ → ∃ n,t<realTimeClamp (T := T) (c n))
    (B : Fin d → Ω × ℝ → ℝ) (G : Fin d → Fin d → Ω × ℝ → ℝ)
    (hBm : ∀ i w,Measurable (fun r => B i (w,r)))
    (hBi : ∀ i n,∀ᵐ w ∂P,IntervalIntegrable (fun r => B i (w,r)) volume 0 (c n))
    (hAB : ∀ i n,∀ᵐ w ∂P,∀ r∈Icc 0 (c n),A i (realTimeClamp r) w=A i ⊥ w+∫ s in 0..r,B i (w,s))
    (hGm : ∀ i j w,Measurable (fun r => G i j (w,r)))
    (hGi : ∀ i j n,∀ᵐ w ∂P,IntervalIntegrable (fun r => G i j (w,r)) volume 0 (c n))
    (hCG : ∀ i j n,∀ᵐ w ∂P,∀ r∈Icc 0 (c n),C i j (realTimeClamp r) w=∫ s in 0..r,G i j (w,s)) :
    ∃ N : Fin d → ClosedTime T → Ω → ℝ,
      (∀ i,LocalMProcessWitness P F (N i)) ∧
      (∀ i,ItoCovarianceFormula P F (M i)
        (fun z => fderiv ℝ f (fun k => X k (realTimeClamp z.2) z.1) (Pi.single i 1)) (N i)) ∧
      ∀ r : ℝ,0 ≤ r → (r:EReal)<T →
        (fun w => f (fun i => X i (realTimeClamp r) w)) =ᵐ[P]
          fun w => f (fun i => X i ⊥ w)+(∑ i,N i (realTimeClamp r) w)+
            (∑ i,∫ s in 0..r,fderiv ℝ f (fun k => X k (realTimeClamp s) w) (Pi.single i 1)*B i (w,s))+
            (∑ i,∑ j,∫ s in 0..r,fderiv ℝ (fderiv ℝ f) (fun k => X k (realTimeClamp s) w)
              (Pi.single i 1) (Pi.single j 1)*G i j (w,s))/2 := by
  obtain ⟨Z,J,hZ,hJ,he⟩ := constructed_multivariate_ito P hT F hF hle hnull X A M C hX hC f hf c hc hcm hcT hcc
  have hex i : ∃ D N,SemimartingaleDecomposition P F (Z i) D N ∧
      VariationIntegralFormula P c hc (A i)
        (fun z => fderiv ℝ f (fun k => X k (realTimeClamp z.2) z.1) (Pi.single i 1)) D ∧
      ItoCovarianceFormula P F (M i)
        (fun z => fderiv ℝ f (fun k => X k (realTimeClamp z.2) z.1) (Pi.single i 1)) N := hZ i
  choose D N hDN hD hN using hex
  refine ⟨N,fun i => (hDN i).martingale,hN,?_⟩
  intro r hr hrT
  have hrt : realTimeClamp (T := T) r<⊤ := by
    change (realTimeClamp r:EReal)<T
    rw [real_time_clamp_eq r hr hrT.le]; exact hrT
  have hd i := multivariate_integrand_regularity P F X A M hX
    (fun x => fderiv ℝ f x (Pi.single i 1))
    ((hf.continuous_fderiv (by norm_num)).clm_apply continuous_const)
  have hdd i j := multivariate_integrand_regularity P F X A M hX
    (fun x => fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1))
    ((((hf.fderiv_right (by norm_num : (1:WithTop ℕ∞)+1≤2)).continuous_fderiv (by norm_num)).clm_apply
      continuous_const).clm_apply continuous_const)
  have heD i := time_density_variation_integral_with_initial P (A i) (D i) (A i ⊥) (B i) _ c hc hcT hcc
    (hAB i) (hBm i) (hBi i) (hd i).1 (fun n => (hd i).2.2 (c n) (hc n) (hcT n)) (hD i) r hr hrT
  have heJ i j := time_density_variation_integral P (C i j) (J i j) (G i j) _ c hc hcT hcc
    (hCG i j) (hGm i j) (hGi i j) (hdd i j).1 (fun n => (hdd i j).2.2 (c n) (hc n) (hcT n)) (hJ i j) r hr hrT
  have haD := ae_all_iff.mpr heD
  have haJ := ae_all_iff.mpr (fun i => ae_all_iff.mpr (heJ i))
  filter_upwards [he,haD,haJ] with w hw hdw hjw
  have hh := hw (realTimeClamp r) hrt
  simp_rw [(fun i => (hDN i).decomposition _ hrt w),hdw,hjw,Finset.sum_add_distrib] at hh
  linarith only [hh]

end Asakura.Chapter5
