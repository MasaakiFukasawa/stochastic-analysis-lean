import Chapter4DiscountedMartingaleProduct
import Chapter4DiscountedDriftAlgebra
import Chapter2CommonTimeEquality

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter5
set_option maxHeartbeats 4600000
set_option backward.isDefEq.respectTransparency false

/-- A process with drift kU-g becomes a local martingale after discounting
and adding the discounted source integral. The stochastic integral is
constructed from its actual local martingale part. -/
theorem discounted_drift_local_representation
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (U N K G : ClosedTime T → Ω → ℝ) (hN : LocalMProcessWitness P F N)
    (hUc : ∀ w t,t<⊤ → ContinuousAt (fun s => U s w) t)
    (hKa : ∀ t,t<⊤ → Measurable[F t] (K t))
    (hKc : ∀ w t,t<⊤ → ContinuousAt (fun s => K s w) t)
    (hGc : ∀ w t,t<⊤ → ContinuousAt (fun s => G s w) t)
    (R : ℝ) (hR : 0≤R) (hRT : (R:EReal)<T)
    (hKpos : ∀ w r,r∈Icc 0 R → 0≤K (realTimeClamp r) w)
    (he : ∀ r∈Icc 0 R,U (realTimeClamp r)=ᵐ[P] fun w => U ⊥ w+N (realTimeClamp r) w+
      ∫ s in 0..r,K (realTimeClamp s) w*U (realTimeClamp s) w-G (realTimeClamp s) w) :
    ∃ Z : ClosedTime T → Ω → ℝ,LocalMProcessWitness P F Z ∧
      ∀ r∈Icc 0 R,
        (fun w => U (realTimeClamp r) w*discountFactor (fun s => K (realTimeClamp s) w) r+
          ∫ s in 0..r,G (realTimeClamp s) w*discountFactor (fun u => K (realTimeClamp u) w) s)=ᵐ[P]
        fun w => U ⊥ w+Z (realTimeClamp r) w := by
  let q : ℝ → ClosedTime T := fun r => min (realTimeClamp R) (realTimeClamp r)
  have hq r (hr : r∈Icc 0 R) : q r=realTimeClamp r := min_eq_right (real_time_clamp_mono hr.2)
  let u := fun w r => U (q r) w
  let k := fun w r => K (q r) w
  let g := fun w r => G (q r) w
  let n := fun w r => N (q r) w
  let b := fun w r => k w r*u w r-g w r
  have huc w : Continuous (u w) := (open_path_stopped_continuous U hUc R hR hRT w).comp real_time_clamp_continuous
  have hkc w : Continuous (k w) := (open_path_stopped_continuous K hKc R hR hRT w).comp real_time_clamp_continuous
  have hgc w : Continuous (g w) := (open_path_stopped_continuous G hGc R hR hRT w).comp real_time_clamp_continuous
  have hnc w : Continuous (n w) := (open_path_stopped_continuous N (hN.path P F) R hR hRT w).comp real_time_clamp_continuous
  have hbc w : Continuous (b w) := (hkc w).mul (huc w) |>.sub (hgc w)
  have hprim w : Continuous (fun r => ∫ s in 0..r,b w s) := by
    apply continuous_iff_continuousAt.mpr
    intro r
    exact (intervalIntegral.integral_hasDerivAt_right ((hbc w).intervalIntegrable 0 r)
      (hbc w).stronglyMeasurable.stronglyMeasurableAtFilter (hbc w).continuousAt).continuousAt
  letI : Nonempty (Icc (0:ℝ) R) := ⟨⟨0,le_rfl,hR⟩⟩
  have hec : ∀ᵐ w ∂P,∀ r : Icc (0:ℝ) R,u w r.val=U ⊥ w+n w r.val+∫ s in 0..r.val,b w s := by
    apply continuous_process_common_time_equality P
      (fun r : Icc (0:ℝ) R => fun w => u w r.val)
      (fun r : Icc (0:ℝ) R => fun w => U ⊥ w+n w r.val+∫ s in 0..r.val,b w s)
      (fun w => (huc w).comp continuous_subtype_val)
      (fun w => (continuous_const.add (hnc w) |>.add (hprim w)).comp continuous_subtype_val)
    intro r
    filter_upwards [he r.val r.property] with w hw
    dsimp only [u,n]
    rw [hq r.val r.property,hw]
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' : s∈Icc 0 R := Icc_subset_Icc_right r.property.2 (by simpa only [uIcc_of_le r.property.1] using hs)
    dsimp only [b,k,u,g]
    rw [hq s hs']
  have hde w s (hs : s∈Icc 0 R) : discountFactor (k w) s=
      discountFactor (fun a => K (realTimeClamp a) w) s := by
    dsimp only [discountFactor]
    congr 2
    apply intervalIntegral.integral_congr
    intro a ha
    dsimp only [k]
    rw [hq a (Icc_subset_Icc_right hs.2 (by simpa only [uIcc_of_le hs.1] using ha))]
  obtain ⟨Z,hZ,hp⟩ := discounted_martingale_product P hT F hF hle hnull N K hN hKa hKc R hR hRT hKpos
  refine ⟨Z,hZ,?_⟩
  intro r hr
  filter_upwards [hec,hp r hr] with w hw hpw
  have hnprod : n w r*discountFactor (k w) r=Z (realTimeClamp r) w-
      ∫ s in 0..r,n w s*discountFactor (k w) s*k w s := by
    dsimp only [n]
    rw [hq r hr,hde w r hr,hpw]
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' : s∈Icc 0 R := Icc_subset_Icc_right hr.2 (by simpa only [uIcc_of_le hr.1] using hs)
    dsimp only [k]
    rw [hq s hs',hde w s hs']
  have hh := discounted_drift_cancellation (k w) (b w) (u w) (n w) (g w)
    (hkc w) (hbc w) (hnc w) (hgc w) (U ⊥ w) (Z (realTimeClamp r) w) r hr.1
    (fun s hs => hw ⟨s,Icc_subset_Icc_right hr.2 hs⟩) (fun _ _ => rfl) hnprod
  dsimp only [u] at hh
  rw [hq r hr,hde w r hr] at hh
  convert hh using 1
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  have hs' : s∈Icc 0 R := Icc_subset_Icc_right hr.2 (by simpa only [uIcc_of_le hr.1] using hs)
  dsimp only [g]
  rw [hq s hs',hde w s hs']

end Asakura.Chapter4
