import Chapter4C12ItoConstructed
import Chapter5ClippedClockIntegral
import Chapter5ZeroIto

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter5
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false

/-- The C1,2 formula with actual time as its first coordinate and the
ordinary Lebesgue time integral, in arbitrary state dimension. -/
theorem c12_clock_ito_constructed
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
    (hcc : ∀ t,t<⊤ → ∃ n,t<realTimeClamp (T := T) (c n)) :
    let K := fun t => (finitePrefixTime (T := T) R hR t).val
    ∃ Z : Fin d → ClosedTime T → Ω → ℝ,∃ J : Fin d → Fin d → ClosedTime T → Ω → ℝ,
      (∀ i,SemimartingaleIntegralFormula P F c hc (A i) (M i)
        (fun z => fderiv ℝ (f (K (realTimeClamp z.2))) (fun k => X k (realTimeClamp z.2) z.1) (Pi.single i 1)) (Z i)) ∧
      (∀ i j,VariationIntegralFormula P c hc (C i j)
        (fun z => fderiv ℝ (fderiv ℝ (f (K (realTimeClamp z.2)))) (fun k => X k (realTimeClamp z.2) z.1)
          (Pi.single i 1) (Pi.single j 1)) (J i j)) ∧
      ∀ r∈Icc 0 R,(fun w => f r (fun i => X i (realTimeClamp r) w))=ᵐ[P]
        fun w => f 0 (fun i => X i ⊥ w)+(∫ s in 0..r,ft (s,fun i => X i (realTimeClamp s) w))+
          (∑ i,Z i (realTimeClamp r) w)+(∑ i,∑ j,J i j (realTimeClamp r) w)/2 := by
  dsimp only
  let K := fun t => (finitePrefixTime (T := T) R hR t).val
  obtain ⟨Z0,Z,J,hZ0,hZ,hJ,he⟩ := c12_time_space_ito_constructed P hT F hF hle hnull
    (fun t _ => K t) (clipped_clock_semimartingale P hT F hF R hR)
    (fun _ => finite_prefix_time_mono R hR) (fun _ t => (finitePrefixTime R hR t).property.1)
    X A M C hX hC f ft hf hft hftc hdxc hhc c hc hcm hcT hcc
  obtain ⟨D,N,hDN,hD,hN⟩ := hZ0
  have hn := integral_against_zero_martingale P hT F hF hle hnull N _ hDN.martingale hN
  refine ⟨Z,J,hZ,hJ,?_⟩
  intro r hr
  have hrT : (r:EReal)<T := (EReal.coe_le_coe hr.2).trans_lt hRT
  have hrt : realTimeClamp (T := T) r < ⊤ := by
    change (realTimeClamp r : EReal) < T
    rw [real_time_clamp_eq r hr.1 hrT.le]
    exact hrT
  have htime := clipped_clock_variation_integral P R hR hRT.le D _ c hc hcT hcc hD r hr.1 hr.2 hrT
  filter_upwards [he,hn,htime] with w hw hnw htw
  have hh := hw (realTimeClamp r) hrt
  have hk0 : K ⊥=0 := by
    change (min (0:EReal) (R:EReal)).toReal=0
    rw [min_eq_left (by exact_mod_cast hR),EReal.toReal_zero]
  have hkr : K (realTimeClamp r)=r := finite_prefix_time_of_real R r hR hr hRT.le
  have hi : (∫ s in 0..r,ft (K (realTimeClamp s),fun i => X i (realTimeClamp s) w))=
      ∫ s in 0..r,ft (s,fun i => X i (realTimeClamp s) w) := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' : s∈Icc 0 R := Icc_subset_Icc_right hr.2 (by simpa only [uIcc_of_le hr.1] using hs)
    dsimp only
    rw [show K (realTimeClamp s)=s from finite_prefix_time_of_real R s hR hs' hRT.le]
  rw [hkr,hk0,hDN.decomposition _ hrt w,hnw _ hrt,add_zero,htw,hi] at hh
  exact hh

end Asakura.Chapter4
