import Chapter4VectorTimeIntegrand
import Chapter5TimeDensityInitial
import Chapter4FiniteCovarianceSum

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter5
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false

/-- C1,2 Ito with all stochastic integrals constructed and the drift and
covariance terms identified as ordinary time integrals. -/
theorem c12_density_ito_constructed
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T) {d : ℕ}
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (X A M : Fin d → ClosedTime T → Ω → ℝ)
    (C : Fin d → Fin d → ClosedTime T → Ω → ℝ)
    (hX : ∀ i,SemimartingaleDecomposition P F (X i) (A i) (M i))
    (hC : ∀ i j,LocalCovarianceWitness P F (M i) (M j) (C i j))
    (f : ℝ → (Fin d → ℝ) → ℝ) (ft : ℝ × (Fin d → ℝ) → ℝ)
    (hf : ∀ a,ContDiff ℝ 2 (f a))
    (hft : ∀ a x,HasDerivAt (fun s => f s x) (ft (a,x)) a) (hftc : Continuous ft)
    (hdxc : Continuous (fun z : ℝ × (Fin d → ℝ) => fderiv ℝ (f z.1) z.2))
    (hhc : Continuous (fun z : ℝ × (Fin d → ℝ) => fderiv ℝ (fderiv ℝ (f z.1)) z.2))
    (R : ℝ) (hR : 0≤R) (hRT : (R:EReal)<T)
    (c : ℕ → ℝ) (hc : ∀ n,0≤c n) (hcm : Monotone c) (hcT : ∀ n,(c n:EReal)<T)
    (hcc : ∀ t,t<⊤ → ∃ n,t<realTimeClamp (T := T) (c n))
    (B : Fin d → Ω × ℝ → ℝ) (G : Fin d → Fin d → Ω × ℝ → ℝ)
    (hBm : ∀ i w,Measurable (fun r => B i (w,r)))
    (hBi : ∀ i n,∀ᵐ w ∂P,IntervalIntegrable (fun r => B i (w,r)) volume 0 (c n))
    (hAB : ∀ i n,∀ᵐ w ∂P,∀ r∈Icc 0 (c n),A i (realTimeClamp r) w=A i ⊥ w+∫ s in 0..r,B i (w,s))
    (hGm : ∀ i j w,Measurable (fun r => G i j (w,r)))
    (hGi : ∀ i j n,∀ᵐ w ∂P,IntervalIntegrable (fun r => G i j (w,r)) volume 0 (c n))
    (hCG : ∀ i j n,∀ᵐ w ∂P,∀ r∈Icc 0 (c n),C i j (realTimeClamp r) w=∫ s in 0..r,G i j (w,s)) :
    let K := fun t => (finitePrefixTime (T := T) R hR t).val
    ∃ N : Fin d → ClosedTime T → Ω → ℝ,
      (∀ i,LocalMProcessWitness P F (N i)) ∧
      (∀ i,ItoCovarianceFormula P F (M i)
        (fun z => fderiv ℝ (f (K (realTimeClamp z.2))) (fun k => X k (realTimeClamp z.2) z.1) (Pi.single i 1)) (N i)) ∧
      LocalMProcessWitness P F (fun t w => ∑ i,N i t w) ∧
      ∀ r∈Icc 0 R,(fun w => f r (fun i => X i (realTimeClamp r) w))=ᵐ[P]
        fun w => f 0 (fun i => X i ⊥ w)+(∑ i,N i (realTimeClamp r) w)+
          (∫ s in 0..r,ft (s,fun i => X i (realTimeClamp s) w))+
          (∑ i,∫ s in 0..r,fderiv ℝ (f s) (fun k => X k (realTimeClamp s) w) (Pi.single i 1)*B i (w,s))+
          (∑ i,∑ j,∫ s in 0..r,fderiv ℝ (fderiv ℝ (f s)) (fun k => X k (realTimeClamp s) w)
            (Pi.single i 1) (Pi.single j 1)*G i j (w,s))/2 := by
  dsimp only
  obtain ⟨Z,J,hZ,hJ,he⟩ := c12_clock_ito_constructed P hT F hF hle hnull X A M C hX hC
    f ft hf hft hftc hdxc hhc R hR hRT c hc hcm hcT hcc
  choose D N hDN hD hN using hZ
  let K := fun t => (finitePrefixTime (T := T) R hR t).val
  let H₁ := fun i (z : Ω × ℝ) => fderiv ℝ (f (K (realTimeClamp z.2)))
    (fun k => X k (realTimeClamp z.2) z.1) (Pi.single i 1)
  let H₂ := fun i j (z : Ω × ℝ) => fderiv ℝ (fderiv ℝ (f (K (realTimeClamp z.2))))
    (fun k => X k (realTimeClamp z.2) z.1) (Pi.single i 1) (Pi.single j 1)
  have h₁ i := vector_time_integrand_regularity P F X A M hX R hR
    (fun z => fderiv ℝ (f z.1) z.2 (Pi.single i 1)) (hdxc.clm_apply continuous_const)
  have h₂ i j := vector_time_integrand_regularity P F X A M hX R hR
    (fun z => fderiv ℝ (fderiv ℝ (f z.1)) z.2 (Pi.single i 1) (Pi.single j 1))
    ((hhc.clm_apply continuous_const).clm_apply continuous_const)
  refine ⟨N,fun i => (hDN i).martingale,hN,?_,?_⟩
  · exact local_martingale_finset_sum P hT F hF hle Finset.univ N (fun i _ => (hDN i).martingale)
  intro r hr
  have hrT : (r:EReal)<T := (EReal.coe_le_coe hr.2).trans_lt hRT
  have hrt : realTimeClamp (T := T) r<⊤ := by
    change (realTimeClamp r:EReal)<T
    rw [real_time_clamp_eq r hr.1 hrT.le]
    exact hrT
  have hdi i := time_density_variation_integral_with_initial P (A i) (D i) (A i ⊥) (B i) (H₁ i)
    c hc hcT hcc (hAB i) (hBm i) (hBi i) (h₁ i).1 (fun n => (h₁ i).2.2 (c n) (hc n) (hcT n)) (hD i) r hr.1 hrT
  have hji i j := time_density_variation_integral P (C i j) (J i j) (G i j) (H₂ i j)
    c hc hcT hcc (hCG i j) (hGm i j) (hGi i j) (h₂ i j).1 (fun n => (h₂ i j).2.2 (c n) (hc n) (hcT n)) (hJ i j) r hr.1 hrT
  filter_upwards [he r hr,ae_all_iff.mpr hdi,ae_all_iff.mpr (fun i => ae_all_iff.mpr (hji i))] with w hew hdw hjw
  have hd' i : D i (realTimeClamp r) w=∫ s in 0..r,
      fderiv ℝ (f s) (fun k => X k (realTimeClamp s) w) (Pi.single i 1)*B i (w,s) := by
    rw [hdw i]
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' : s∈Icc 0 R := Icc_subset_Icc_right hr.2 (by simpa only [uIcc_of_le hr.1] using hs)
    dsimp only [H₁,K]
    rw [finite_prefix_time_of_real R s hR hs' hRT.le]
  have hj' i j : J i j (realTimeClamp r) w=∫ s in 0..r,
      fderiv ℝ (fderiv ℝ (f s)) (fun k => X k (realTimeClamp s) w) (Pi.single i 1) (Pi.single j 1)*G i j (w,s) := by
    rw [hjw i j]
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' : s∈Icc 0 R := Icc_subset_Icc_right hr.2 (by simpa only [uIcc_of_le hr.1] using hs)
    dsimp only [H₂,K]
    rw [finite_prefix_time_of_real R s hR hs' hRT.le]
  have hz : (∑ i,Z i (realTimeClamp r) w)=(∑ i,D i (realTimeClamp r) w)+(∑ i,N i (realTimeClamp r) w) := by
    simp only [(hDN _).decomposition _ hrt w,Finset.sum_add_distrib]
  rw [hz] at hew
  simp only [hd',hj'] at hew
  linarith

end Asakura.Chapter4
