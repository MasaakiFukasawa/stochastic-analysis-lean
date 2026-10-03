import Chapter5GeneratorPrefixCancellation
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
theorem multivariate_zero_generator_increment
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
    (hCG : ∀ i j n,∀ᵐ w ∂P,∀ r∈Icc 0 (c n),C i j (realTimeClamp r) w=∫ s in 0..r,G i j (w,s))
    (a b : ℝ) (ha0 : 0≤a) (hab : a≤b) (hbT : (b:EReal)<T)
    (hzero : ∀ w (r : ℝ),r∈Icc a b →
      (∑ i,fderiv ℝ f (fun k => X k (realTimeClamp r) w) (Pi.single i 1)*B i (w,r))+
      (∑ i,∑ j,fderiv ℝ (fderiv ℝ f) (fun k => X k (realTimeClamp r) w)
        (Pi.single i 1) (Pi.single j 1)*G i j (w,r))/2=0) :
    ∃ N : Fin d → ClosedTime T → Ω → ℝ,
      (∀ i,LocalMProcessWitness P F (N i)) ∧
      (∀ i,ItoCovarianceFormula P F (M i)
        (fun z => fderiv ℝ f (fun k => X k (realTimeClamp z.2) z.1) (Pi.single i 1)) (N i)) ∧
      (fun w => f (fun i => X i (realTimeClamp b) w)) =ᵐ[P]
        fun w => f (fun i => X i (realTimeClamp a) w)+
          ∑ i,(N i (realTimeClamp b) w-N i (realTimeClamp a) w) := by
  obtain ⟨N,hN,hNI,he⟩ := multivariate_density_ito P hT F hF hle hnull X A M C hX hC f hf
    c hc hcm hcT hcc B G hBm hBi hAB hGm hGi hCG
  refine ⟨N,hN,hNI,?_⟩
  have hb0 : 0≤b := ha0.trans hab
  have haT : (a:EReal)<T := (EReal.coe_le_coe hab).trans_lt hbT
  have hrt : realTimeClamp (T := T) b<⊤ := by
    change (realTimeClamp b:EReal)<T
    rw [real_time_clamp_eq b hb0 hbT.le]; exact hbT
  obtain ⟨j,hj⟩ := hcc _ hrt
  have hrj : b ≤ c j := by
    change (realTimeClamp b:EReal)<(realTimeClamp (c j):EReal) at hj
    rw [real_time_clamp_eq b hb0 hbT.le,real_time_clamp_eq (c j) (hc j) (hcT j).le] at hj
    exact EReal.coe_le_coe_iff.mp hj.le
  have hiB := ae_all_iff.mpr (fun i => hBi i j)
  have hiG := ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun k => hGi i k j))
  have hd i := multivariate_integrand_regularity P F X A M hX
    (fun x => fderiv ℝ f x (Pi.single i 1))
    ((hf.continuous_fderiv (by norm_num)).clm_apply continuous_const)
  have hdd i k := multivariate_integrand_regularity P F X A M hX
    (fun x => fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single k 1))
    ((((hf.fderiv_right (by norm_num : (1:WithTop ℕ∞)+1≤2)).continuous_fderiv (by norm_num)).clm_apply
      continuous_const).clm_apply continuous_const)
  filter_upwards [he b hb0 hbT,he a ha0 haT,hiB,hiG] with w hw hwa hb hg
  have hsub : uIcc (0:ℝ) b ⊆ uIcc 0 (c j) := by
    simpa only [uIcc_of_le hb0,uIcc_of_le (hc j)] using Icc_subset_Icc_right hrj
  have hs : ∀ᵐ s ∂volume.restrict (Ioc 0 b),s∈Icc 0 b :=
    (ae_restrict_mem measurableSet_Ioc).mono fun s hs => ⟨hs.1.le,hs.2⟩
  have hb' i : IntervalIntegrable
      (fun s => fderiv ℝ f (fun k => X k (realTimeClamp s) w) (Pi.single i 1)*B i (w,s)) volume 0 b := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hb0).mpr
    exact continuous_multiplier_integrable b hb0 _ hs _ _ ((hd i).2.2 b hb0 hbT w) ((hd i).1 w)
      ((hb i).mono_set hsub).1
  have hg' i k : IntervalIntegrable
      (fun s => fderiv ℝ (fderiv ℝ f) (fun k => X k (realTimeClamp s) w)
        (Pi.single i 1) (Pi.single k 1)*G i k (w,s)) volume 0 b := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hb0).mpr
    exact continuous_multiplier_integrable b hb0 _ hs _ _ ((hdd i k).2.2 b hb0 hbT w) ((hdd i k).1 w)
      ((hg i k).mono_set hsub).1
  have hz := integrated_generator_prefix_cancellation d a b ha0 hab _ _ hb' hg' (hzero w)
  simp only [Finset.sum_sub_distrib]
  linarith only [hw,hwa,hz]

end Asakura.Chapter5
