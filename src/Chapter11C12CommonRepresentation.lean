import Chapter11ScalarC12Ito
import Chapter5BracketCommonTime

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false

/-- Put scalar Ito on one common event for every time, retaining the
 generator integral so the formula can be evaluated at an exit time. -/
theorem c12_ito_common_representation
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (R : ℝ) (hR : 0≤R) (X N : ℝ → Ω → ℝ)
    (hX : ∀ w,ContinuousOn (fun r => X r w) (Icc 0 R))
    (hN : ∀ w,ContinuousOn (fun r => N r w) (Icc 0 R))
    (g : ℝ → ℝ → ℝ) (gt : ℝ × ℝ → ℝ)
    (hgc : Continuous (fun z : ℝ × ℝ => g z.1 z.2)) (hgtc : Continuous gt)
    (hdc : Continuous (fun z : ℝ × ℝ => deriv (g z.1) z.2))
    (hddc : Continuous (fun z : ℝ × ℝ => deriv (deriv (g z.1)) z.2))
    (b q : Ω × ℝ → ℝ)
    (hbi : ∀ᵐ w ∂P,IntervalIntegrable (fun r => b (w,r)) volume 0 R)
    (hqi : ∀ᵐ w ∂P,IntervalIntegrable (fun r => q (w,r)) volume 0 R)
    (he : ∀ r∈Icc 0 R,(fun w => g r (X r w))=ᵐ[P] fun w => g 0 (X 0 w)+N r w+
      (∫ s in 0..r,gt (s,X s w))+
      (∫ s in 0..r,deriv (g s) (X s w)*b (w,s))+
      (∫ s in 0..r,deriv (deriv (g s)) (X s w)*q (w,s))/2) :
    ∀ᵐ w ∂P,∀ r∈Icc 0 R,g r (X r w)=g 0 (X 0 w)+N r w+
      ∫ s in 0..r,gt (s,X s w)+deriv (g s) (X s w)*b (w,s)+
        deriv (deriv (g s)) (X s w)*q (w,s)/2 := by
  let G := fun w s => gt (s,X s w)+deriv (g s) (X s w)*b (w,s)+
    deriv (deriv (g s)) (X s w)*q (w,s)/2
  have hp w : ContinuousOn (fun s => (s,X s w)) (uIcc 0 R) := by
    rw [uIcc_of_le hR]
    exact continuousOn_id.prodMk (hX w)
  have ht w : IntervalIntegrable (fun s => gt (s,X s w)) volume 0 R :=
    (hgtc.comp_continuousOn (hp w)).intervalIntegrable
  have hbq : ∀ᵐ w ∂P,
      IntervalIntegrable (fun s => deriv (g s) (X s w)*b (w,s)) volume 0 R ∧
      IntervalIntegrable (fun s => deriv (deriv (g s)) (X s w)*q (w,s)) volume 0 R := by
    filter_upwards [hbi,hqi] with w hb hq
    exact ⟨hb.continuousOn_mul (hdc.comp_continuousOn (hp w)),
      hq.continuousOn_mul (hddc.comp_continuousOn (hp w))⟩
  have hi : ∀ᵐ w ∂P,IntervalIntegrable (G w) volume 0 R := by
    filter_upwards [hbq] with w hw
    exact ((ht w).add hw.1).add (hw.2.div_const 2)
  have hc w : ContinuousOn (fun r => g r (X r w)-g 0 (X 0 w)-N r w) (Icc 0 R) :=
    (((hgc.comp_continuousOn (continuousOn_id.prodMk (hX w))).sub continuousOn_const).sub (hN w))
  have hh := bracket_primitive_common_time P R hR
    (fun r w => g r (X r w)-g 0 (X 0 w)-N r w) G hc hi (by
      intro r hr
      filter_upwards [he r hr,hbq] with w hew hw
      have hsub : uIcc 0 r⊆uIcc 0 R := by
        rw [uIcc_of_le hr.1,uIcc_of_le hR]
        exact Icc_subset_Icc_right hr.2
      dsimp only [G]
      rw [intervalIntegral.integral_add (((ht w).mono_set hsub).add (hw.1.mono_set hsub))
        ((hw.2.mono_set hsub).div_const 2),
        intervalIntegral.integral_add ((ht w).mono_set hsub) (hw.1.mono_set hsub),
        intervalIntegral.integral_div]
      linarith)
  filter_upwards [hh] with w hw
  intro r hr
  have h := hw r hr
  dsimp only [G] at h
  linarith

end Asakura.Chapter11
