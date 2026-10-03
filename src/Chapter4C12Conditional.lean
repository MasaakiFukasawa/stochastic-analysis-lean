import Chapter4C12Harmonic
import Chapter4VectorBoundedConditional

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter5
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false

/-- Conditional identity for bounded C1,2 solutions of the backward
equation in arbitrary dimension. All Ito integrals are constructed. -/
theorem c12_harmonic_conditional
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
        (Pi.single i 1) (Pi.single j 1)*G i j (w,r))/2=0)
    (hfc : Continuous (fun z : ℝ × (Fin d → ℝ) => f z.1 z.2))
    (K : ℝ) (hb : ∀ r∈Icc 0 R,∀ x,|f r x|≤K)
    (s : ℝ) (hs : s∈Icc 0 R) :
    P[(fun w => f R (fun i => X i (realTimeClamp R) w)) | F (realTimeClamp s)]=ᵐ[P]
      fun w => f s (fun i => X i (realTimeClamp s) w) := by
  obtain ⟨N,hN,he⟩ := c12_harmonic_local_representation P hT F hF hle hnull X A M C hX hC
    f ft hf hft hftc hdxc hhc R hR hRT c hc hcm hcT hcc B G hBm hBi hAB hGm hGi hCG hpde
  have ha t (ht : t<⊤) : Measurable[F t] (fun w i => X i t w) := by
    letI : MeasurableSpace Ω := F t
    apply Measurable.of_eval
    intro i
    have heq : X i t=fun w => A i t w+M i t w := funext ((hX i).decomposition t ht)
    change Measurable[F t] (X i t)
    rw [heq]
    exact ((hX i).variation.adapted t ht).add ((hX i).martingale.adapted P F t ht)
  exact vector_bounded_conditional_from_local_representation P hT F hF hle
    (fun t w i => X i t w) ha (fun w t ht => continuousAt_pi.mpr fun i => (hX i).continuous w t ht)
    (fun z => f z.1 z.2) hfc N hN R hR hRT K hb he s hs

end Asakura.Chapter4
