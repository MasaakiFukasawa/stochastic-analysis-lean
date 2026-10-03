import Chapter5BSDEFiniteEnergyData
import Chapter5FrozenQuotient

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false

/-- An equality of drivers in sample-time L² gives the BSDE identity
at each time, including the terminal endpoint. -/
theorem finite_bsde_equation_from_drift
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (F : ClosedTime T → MeasurableSpace Ω)
    (W : ClosedTime T → Ω → ℝ) (c : ℕ → ℝ)
    (hc : ∀ j,0≤c j) (hcT : ∀ j,(c j:EReal)<T) (hco : ∀ r,∃ j,r≤c j)
    (R : ℝ) (hR : 0≤R) (hRT : (R:EReal)<T)
    (u : BSDEFiniteEnergyData P F W c R) (ξ : Ω → ℝ)
    (hξ : u.Y (realTimeClamp R) =ᵐ[P] ξ)
    (G : Ω × ℝ → ℝ) (hGm : Measurable G)
    (hG2 : MemLp G 2 (P.prod (volume.restrict (Ioc 0 R))))
    (he : u.B =ᵐ[P.prod (volume.restrict (Ioc 0 R))] fun z => -G z) :
    ∀ t∈Icc 0 R,(u.Y (realTimeClamp t)) =ᵐ[P]
      fun w => ξ w+(∫ r in t..R,G (w,r))-(u.M (realTimeClamp R) w-u.M (realTimeClamp t) w) := by
  obtain ⟨j,hj⟩ := hco R
  have hp := time_primitive_common_congr P R u.B (fun z => -G z) he
  have hGi := (finite_time_L2_sections P R hR G hGm hG2).1
  have hfin (r : ℝ) (hr : r∈Icc 0 R) : realTimeClamp (T := T) r<⊤ := by
    change (realTimeClamp r:EReal)<T
    rw [real_time_clamp_eq r hr.1 ((EReal.coe_le_coe hr.2).trans hRT.le)]
    exact (EReal.coe_le_coe hr.2).trans_lt hRT
  intro t ht
  filter_upwards [u.drift j,hp,hξ,hGi] with w hd hpw htw hgw
  have hi : IntervalIntegrable (fun r => G (w,r)) volume 0 R :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hR).mpr (hgw.integrable (by norm_num))
  have h0t : IntervalIntegrable (fun r => G (w,r)) volume 0 t := hi.mono_set (by simpa only [uIcc_of_le ht.1,uIcc_of_le hR] using Icc_subset_Icc_right ht.2)
  have htR : IntervalIntegrable (fun r => G (w,r)) volume t R := hi.mono_set (by simpa only [uIcc_of_le ht.2,uIcc_of_le hR] using Icc_subset_Icc_left ht.1)
  have hs := intervalIntegral.integral_add_adjacent_intervals h0t htR
  have hdt := hd t ⟨ht.1,ht.2.trans hj⟩
  have hdR := hd R ⟨hR,hj⟩
  rw [hpw t ht,intervalIntegral.integral_neg] at hdt
  rw [hpw R ⟨hR,le_rfl⟩,intervalIntegral.integral_neg] at hdR
  have hyt := u.decomposition.decomposition _ (hfin t ht) w
  have hyR := u.decomposition.decomposition _ (hfin R ⟨hR,le_rfl⟩) w
  change u.Y (realTimeClamp t) w=ξ w+(∫ r in t..R,G (w,r))-(u.M (realTimeClamp R) w-u.M (realTimeClamp t) w)
  linarith only [hs,hdt,hdR,hyt,hyR,htw]

end Asakura.Chapter5
