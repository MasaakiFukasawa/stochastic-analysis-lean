import Chapter4VectorPrefixPowerEstimate
import Chapter4VectorPowerGronwall
import Chapter4VolterraPathLimit

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter5
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false

theorem vector_integral_uniform_power_bound
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t E, MeasurableSet[m] E → P E = 0 → MeasurableSet[F t] E)
    {d dim : ℕ} (W A : Fin d → ClosedTime T → Ω → ℝ) (N : Fin dim → Fin d → ClosedTime T → Ω → ℝ)
    (hW : ∀ j,LocalMProcessWitness P F (W j))
    (hA : ∀ j,LocalCovarianceWitness P F (W j) (W j) (A j))
    (hN : ∀ i j,LocalMProcessWitness P F (N i j))
    (c : ℕ → ℝ) (hc : ∀ n, 0 < c n) (hcm : StrictMono c) (hcT : ∀ n, (c n:EReal) < T)
    (hct : StrictMono (fun n => realTimeClamp (T := T) (c n)))
    (hcut : ∀ n, realTimeClamp (T := T) (c n) < ⊤)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < realTimeClamp (T := T) (c n))
    (hclock : ∀ j n w r, r ∈ Icc 0 (c n) → A j (realTimeClamp r) w = r)
    (G : Fin dim → Fin d → Ω × ℝ → ℝ)
    (hG : ∀ i j n, @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) (c n) => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) (c n) => G i j (z.1,z.2.val)))
    (hi : ∀ i j n, ∀ᵐ w ∂P, IntervalIntegrable (fun r => G i j (w,r)^2) volume 0 (c n))
    (hNI : ∀ i j,ItoCovarianceFormula P F (W j) (G i j) (N i j))
    (R : ℝ) (hR : 0≤R) (hRT : (R:EReal)<T) (p : ℝ) (hp : 2≤p)
    (Y : Ω → C(Icc (0:ℝ) R,Fin dim → ℝ)) (hYm : Measurable[m] Y) 
    (hYi : MemLp Y (ENNReal.ofReal p) P)
    (ξ : Fin dim → Ω → ℝ) (hξm : ∀ i,Measurable[m] (ξ i)) (hξi : ∀ i,MemLp (ξ i) (ENNReal.ofReal p) P)
    (U : Fin dim → Ω × ℝ → ℝ) (hUm : ∀ i,Measurable[m.prod inferInstance] (U i)) (hGm : ∀ i j,Measurable[m.prod inferInstance] (G i j))
    (K : ℝ) (hK : 0≤K)
    (hUg : ∀ i w r,r∈Icc 0 R → |U i (w,r)|^p≤K*(1+‖Y w (projIcc 0 R hR r)‖^p))
    (hGg : ∀ i j w r,r∈Icc 0 R → |G i j (w,r)|^p≤K*(1+‖Y w (projIcc 0 R hR r)‖^p))
    (hrep : ∀ᵐ w ∂P,∀ r i,Y w r i=ξ i w+(∫ s in 0..r.val,U i (w,s))+∑ j,N i j (realTimeClamp r.val) w) :
    let α := (dim:ℝ)^(p-1)*(3:ℝ)^(p-1)
    let δ := (d:ℝ)^(p-1)*d
    let rate := vectorMomentGrowthRate R p K α dim δ
    (∫ w,‖Y w‖^p ∂P)≤(α*(∑ i,∫ w,|ξ i w|^p ∂P)+rate*R)*Real.exp ((rate+1)*R) := by
  letI : MeasurableSpace Ω := m
  dsimp only
  have hp0 : 0<p := by linarith only [hp]
  let u := fun t => ∫ w,‖prefixPath hR (normEnvelope (Y w)) t‖^p ∂P
  have hu : Continuous u := prefix_power_moment_continuous P hR (fun w => normEnvelope (Y w))
    (norm_envelope_measurable Y hYm) p hp0 ((norm_envelope_memLp P Y hYm _).2 hYi)
  have hh := vector_moment_gronwall_bound R p K (∑ i,∫ w,|ξ i w|^p ∂P)
    ((dim:ℝ)^(p-1)*(3:ℝ)^(p-1)) dim ((d:ℝ)^(p-1)*d)
    (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg dim) _) (Real.rpow_nonneg (by norm_num) _))
    (Nat.cast_nonneg dim) (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _) (Nat.cast_nonneg d))
    hR hp hK (Finset.sum_nonneg (fun _ _ => integral_nonneg (fun w => Real.rpow_nonneg (abs_nonneg _) _)))
    u hu (fun t => integral_nonneg (fun w => Real.rpow_nonneg (norm_nonneg _) _))
    (fun t ht => vector_integral_prefix_power_estimate P hT F hF hle hnull W A N hW hA hN
      c hc hcm hcT hct hcut hcc hclock G hG hi hNI R hR hRT p hp Y hYm hYi ξ hξm hξi
      U hUm hGm K hK hUg hGg hrep t ht)
  simpa only [u,prefix_path_endpoint,norm_envelope_norm] using hh

end Asakura.Chapter4
