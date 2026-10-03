import Chapter5BSDEEnergyConnection
import Chapter5AprioriFullEnergy

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

/-- The a priori proof assembled from actual Ito integrals and the BSDE's
drift decomposition. No energy identity, bracket bound, maximal estimate,
or mean-zero stochastic term is assumed. Here ell and mu2 stand for the
printed lambda² and mu². -/
theorem bsde_apriori_constructed
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t E, MeasurableSet[m] E → P E = 0 → MeasurableSet[F t] E)
    (W A Y V M : ClosedTime T → Ω → ℝ)
    (hW : LocalMProcessWitness P F W) (hA : LocalCovarianceWitness P F W W A)
    (hY : SemimartingaleDecomposition P F Y V M)
    (c : ℕ → ℝ) (hc : ∀ n, 0 < c n) (hcm : StrictMono c) (hcT : ∀ n, (c n:EReal) < T)
    (hct : StrictMono (fun n => realTimeClamp (T := T) (c n)))
    (hcut : ∀ n, realTimeClamp (T := T) (c n) < ⊤)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < realTimeClamp (T := T) (c n))
    (hclock : ∀ n w r, r ∈ Icc 0 (c n) → A (realTimeClamp r) w = r)
    (G B : Ω × ℝ → ℝ) (hGm : Measurable G) (hBm : Measurable B)
    (hG : ∀ n, @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) (c n) => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) (c n) => G (z.1,z.2.val)))
    (hGi : ∀ n, ∀ᵐ w ∂P, IntervalIntegrable (fun r => G (w,r)^2) volume 0 (c n))
    (hBi : ∀ n, ∀ᵐ w ∂P, IntervalIntegrable (fun r => B (w,r)) volume 0 (c n))
    (hVB : ∀ n, ∀ᵐ w ∂P, ∀ r ∈ Icc 0 (c n), V (realTimeClamp r) w = V ⊥ w + ∫ s in 0..r,B (w,s))
    (hMG : ItoCovarianceFormula P F W G M)
    (R : ℝ) (hR : 0 ≤ R) (hRT : (R:EReal) < T)
    (β C₀ ell mu2 : ℝ) (hC₀ : 0 ≤ C₀) (hell : C₀ < ell)
    (hmu2 : 0 < mu2) (hβ : C₀*(2+ell)+mu2 ≤ β)
    (hterminal : MemLp (Y (realTimeClamp R)) 2 P)
    (hGL : MemLp G 2 (P.prod (volume.restrict (Ioc 0 R))))
    (hBL : MemLp B 2 (P.prod (volume.restrict (Ioc 0 R))))
    (hYm : Measurable (fun z : Ω × ℝ => Y (realTimeClamp z.2) z.1))
    (hYL : MemLp (fun z : Ω × ℝ => Y (realTimeClamp z.2) z.1) 2 (P.prod (volume.restrict (Ioc 0 R))))
    (D : Ω × ℝ → ℝ) (hDm : Measurable D) (hDL : MemLp D 2 (P.prod (volume.restrict (Ioc 0 R))))
    (hbound : ∀ w r, r ∈ Icc 0 R → |B (w,r)| ≤ C₀*(|Y (realTimeClamp r) w|+|G (w,r)|)+|D (w,r)|) :
    let K := (∫ w,Real.exp (β*R)*(Y (realTimeClamp R) w)^2 ∂P)+
      (∫ w,(∫ r in 0..R,Real.exp (β*r)*D (w,r)^2) ∂P)/mu2
    (∀ t ∈ Icc 0 R, (∫ w,Real.exp (β*t)*(Y (realTimeClamp t) w)^2 ∂P) ≤ K) ∧
    (∫ w,(∫ r in 0..R,Real.exp (β*r)*(Y (realTimeClamp r) w)^2) ∂P) ≤ R*K ∧
    (∫ w,(∫ r in 0..R,Real.exp (β*r)*G (w,r)^2) ∂P) ≤ ell/(ell-C₀)*K := by
  have hell0 : 0 < ell := hC₀.trans_lt hell
  have hβ0 : 0 ≤ β := (by positivity : 0 ≤ C₀*(2+ell)+mu2).trans hβ
  obtain ⟨N,hN,hYt,he,hnoise⟩ := bsde_constructed_energy_and_zero_mean P hT F hF hle hnull
    W A Y V M hW hA hY c hc hcm hcT hct hcut hcc hclock G B hGm hBm hG hGi hBi hVB hMG
    R hR hRT β hβ0 hterminal hGL hBL
  apply apriori_full_energy_from_constructed_energy P R hR β C₀ ell mu2 hC₀ hell hmu2 hβ
    (fun z : Ω × ℝ => Y (realTimeClamp z.2) z.1) G D (fun z => -B z)
    hYm hGm hDm hBm.neg hYL hGL hDL hterminal
    (by intro w r hr; simpa only [abs_neg] using hbound w r hr) hYt
    (fun t w => N (realTimeClamp R) w-N (realTimeClamp t) w)
    (fun t ht => (hnoise t ht).1) (fun t ht => (hnoise t ht).2)
  intro t ht
  filter_upwards [he t ht] with w hw
  simpa only [mul_neg,intervalIntegral.integral_neg,sub_eq_add_neg] using hw

end Asakura.Chapter5
