import Chapter4GeneratorIntegral
import Chapter4FinitePathLift

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter5
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false

/-- A C1,2 function satisfying the backward equation along a vector
semimartingale has an actual local martingale representation. -/
theorem c12_harmonic_local_representation
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
    (hCG : ∀ i j n,∀ᵐ w ∂P,∀ r∈Icc 0 (c n),C i j (realTimeClamp r) w=∫ s in 0..r,G i j (w,s))
    (hpde : ∀ᵐ w ∂P,∀ r∈Icc 0 R,
      ft (r,fun k => X k (realTimeClamp r) w)+
      (∑ i,fderiv ℝ (f r) (fun k => X k (realTimeClamp r) w) (Pi.single i 1)*B i (w,r))+
      (∑ i,∑ j,fderiv ℝ (fderiv ℝ (f r)) (fun k => X k (realTimeClamp r) w)
        (Pi.single i 1) (Pi.single j 1)*G i j (w,r))/2=0) :
    ∃ N : ClosedTime T → Ω → ℝ,LocalMProcessWitness P F N ∧
      ∀ r∈Icc 0 R,(fun w => f r (fun i => X i (realTimeClamp r) w))=ᵐ[P]
        fun w => f 0 (fun i => X i ⊥ w)+N (realTimeClamp r) w := by
  obtain ⟨N,_,_,hN,he⟩ := c12_density_ito_constructed P hT F hF hle hnull X A M C hX hC
    f ft hf hft hftc hdxc hhc R hR hRT c hc hcm hcT hcc B G hBm hBi hAB hGm hGi hCG
  refine ⟨fun t w => ∑ i,N i t w,hN,?_⟩
  intro r hr
  have hrT : (r:EReal)<T := (EReal.coe_le_coe hr.2).trans_lt hRT
  obtain ⟨n,hn⟩ := hcc _ (real_time_below r hr.1 hrT)
  have hrn : r≤c n := by
    change (realTimeClamp r:EReal)<(realTimeClamp (c n):EReal) at hn
    rw [real_time_clamp_eq r hr.1 hrT.le,real_time_clamp_eq (c n) (hc n) (hcT n).le] at hn
    exact EReal.coe_le_coe_iff.mp hn.le
  have hsub : uIcc 0 r⊆uIcc 0 (c n) := by
    rw [uIcc_of_le hr.1,uIcc_of_le (hc n)]
    exact Icc_subset_Icc_right hrn
  filter_upwards [he r hr,hpde,ae_all_iff.mpr (fun i => hBi i n),
    ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun j => hGi i j n))] with w hew hpw hbw hgw
  let V := fun s => (s,fun i => X i (realTimeClamp s) w)
  have hVc : ContinuousOn V (uIcc 0 r) := by
    rw [uIcc_of_le hr.1]
    apply continuousOn_id.prodMk
    intro s hs
    apply ContinuousAt.continuousWithinAt
    apply continuousAt_pi.mpr
    intro i
    exact ((hX i).continuous w _ (real_time_below s hs.1 ((EReal.coe_le_coe hs.2).trans_lt hrT))).comp
      real_time_clamp_continuous.continuousAt
  have hat : IntervalIntegrable (fun s => ft (V s)) volume 0 r :=
    (hftc.comp_continuousOn hVc).intervalIntegrable
  have hbt i : IntervalIntegrable (fun s =>
      fderiv ℝ (f s) (V s).2 (Pi.single i 1)*B i (w,s)) volume 0 r :=
    ((hbw i).mono_set hsub).continuousOn_mul ((hdxc.clm_apply continuous_const).comp_continuousOn hVc)
  have hgt i j : IntervalIntegrable (fun s =>
      fderiv ℝ (fderiv ℝ (f s)) (V s).2 (Pi.single i 1) (Pi.single j 1)*G i j (w,s)) volume 0 r :=
    ((hgw i j).mono_set hsub).continuousOn_mul
      (((hhc.clm_apply continuous_const).clm_apply continuous_const).comp_continuousOn hVc)
  have hz := generator_integral_zero r _ _ _ hat hbt hgt (fun s hs =>
    hpw s (Icc_subset_Icc_right hr.2 (by simpa only [uIcc_of_le hr.1] using hs)))
  dsimp only [V] at hz
  linarith

end Asakura.Chapter4
