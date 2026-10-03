import Chapter4RealBorelCoefficientDomain
import Chapter4VectorSolutionPowerMoment
import Chapter4VectorRealPath
import Chapter4VectorSDEInitial
import Chapter4VectorGlobalPowerMoment
import Chapter4VectorPowerGrowth

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4.Vector
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

theorem global_sde_moment_from_manuscript_hypotheses
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T) (hTinf : T=⊤) {dim noise : ℕ}
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (W C : Fin noise → ClosedTime T → Ω → ℝ)
    (hW : ∀ j,LocalMProcessWitness P F (W j))
    (hC : ∀ j,LocalCovarianceWitness P F (W j) (W j) (C j))
    (hclock : ∀ j w (r : ℝ),0≤r → (r:EReal)<T → C j (realTimeClamp r) w=r)
    (μ : Fin dim → (Fin dim → ℝ) → ℝ) (σ : Fin dim → Fin noise → (Fin dim → ℝ) → ℝ)
    (hμ : ∀ i,Measurable (μ i)) (hσ : ∀ i j,Measurable (σ i j))
    (L : ℝ) (hL : 0≤L)
    (hgrowth : ∀ x,(∑ i,(μ i x)^2)+(∑ i,∑ j,(σ i j x)^2)≤L*(1+∑ k,(x k)^2))
    (p : ℝ) (hp : 2≤p)
    (ξ : Ω → Fin dim → ℝ) (hξm : Measurable[m] ξ) (hξi : MemLp ξ (ENNReal.ofReal p) P)
    (X : ClosedTime T → Ω → Fin dim → ℝ)
    (ha : ∀ t,t<⊤ → Measurable[F t] (X t))
    (hc : ∀ w t,t<⊤ → ContinuousAt (fun s => X s w) t)
    (N : Fin dim → Fin noise → ClosedTime T → Ω → ℝ)
    (hn : ∀ i j,LocalMProcessWitness P F (N i j))
    (hI : ∀ i j,ItoCovarianceFormula P F (W j) (fun z => σ i j (X (realTimeClamp z.2) z.1)) (N i j))
    (he : ∀ᵐ w ∂P,∀ r : ℝ,0≤r → (r:EReal)<T → ∀ i,
      X (realTimeClamp r) w i=ξ w i+(∫ s in 0..r,μ i (X (realTimeClamp s) w))+∑ j,N i j (realTimeClamp r) w)
    (R : ℝ) (hR : 0≤R) (hRT : (R:EReal)<T) :
    MemLp (realVectorPath X hc R hRT) (ENNReal.ofReal p) P := by
  classical
  have hμg i x : (μ i x)^2≤L*(1+∑ k,(x k)^2) := by
    have hh := Finset.single_le_sum (s := Finset.univ) (f := fun i => (μ i x)^2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
    have hs : 0≤∑ i,∑ j,(σ i j x)^2 := Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    linarith only [hh,hs,hgrowth x]
  have hσg i j x : (σ i j x)^2≤L*(1+∑ k,(x k)^2) := by
    have hj := Finset.single_le_sum (s := Finset.univ) (f := fun j => (σ i j x)^2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
    have hi := Finset.single_le_sum (s := Finset.univ) (f := fun i => ∑ j,(σ i j x)^2)
      (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (Finset.mem_univ i)
    have hm : 0≤∑ i,(μ i x)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    linarith only [hj,hi,hm,hgrowth x]
  exact global_sde_power_moment P hT hTinf F hF hle hnull W C hW hC hclock μ σ hμ hσ
    (L*(dim+1)) (by positivity)
    (fun i x => vector_square_growth_norm x _ L hL (hμg i x))
    (fun i j x => vector_square_growth_norm x _ L hL (hσg i j x))
    p hp ξ hξm hξi X ha hc N hn hI he R hR hRT

end Asakura.Chapter4.Vector
