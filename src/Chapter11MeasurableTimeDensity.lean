import Chapter5TimeDensityInitial
import Chapter2SignedRestriction

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter5
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- The time-density identity for measurable integrands on their actual
integrability domain; no continuity of trading holdings is required. -/
theorem measurable_time_density_variation_integral
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {T : EReal} [Fact (0≤T)]
    (B J : ClosedTime T → Ω → ℝ) (U : Ω → ℝ) (G H : Ω × ℝ → ℝ)
    (c : ℕ → ℝ) (hc : ∀ n,0≤c n) (hcT : ∀ n,(c n:EReal)<T)
    (hcc : ∀ t,t<⊤ → ∃ n,t<realTimeClamp (T := T) (c n))
    (d : ℝ) (hd : 0≤d) (hdT : (d:EReal)<T)
    (hB : ∀ᵐ w ∂P,∀ r∈Icc 0 d,B (realTimeClamp r) w=U w+∫ s in 0..r,G (w,s))
    (hGm : ∀ w,Measurable (fun r => G (w,r)))
    (hGi : ∀ᵐ w ∂P,IntervalIntegrable (fun r => G (w,r)) volume 0 d)
    (hHm : ∀ w,Measurable (fun r => H (w,r)))
    (hHGi : ∀ᵐ w ∂P,IntervalIntegrable (fun r => H (w,r)*G (w,r)) volume 0 d)
    (hJ : VariationIntegralFormula P c hc B H J) :
    J (realTimeClamp d)=ᵐ[P] fun w => ∫ r in 0..d,H (w,r)*G (w,r) := by
  have hdt : realTimeClamp (T := T) d<⊤ := by
    change (realTimeClamp d:EReal)<T
    rw [real_time_clamp_eq d hd hdT.le]; exact hdT
  obtain ⟨j,hj⟩ := hcc _ hdt
  have hdj : d≤c j := by
    change (realTimeClamp d:EReal)<(realTimeClamp (c j):EReal) at hj
    rw [real_time_clamp_eq d hd hdT.le,real_time_clamp_eq (c j) (hc j) (hcT j).le] at hj
    exact EReal.coe_le_coe_iff.mp hj.le
  obtain ⟨κ,_,hκ,hHi,hform⟩ := hJ j
  filter_upwards [hκ,hHi,hform,hB,hGi,hHGi] with w hκw hHiw hfw hBw hGiw hp
  have hclip r : intervalClamp 0 (c j) (hc j) (min r d)=intervalClamp 0 d hd r := by
    rcases le_total r 0 with hr|hr
    · simp [intervalClamp,projIcc_of_le_left,hr,min_le_left r d |>.trans hr]
    · rcases le_total r d with hrd|hdr
      · rw [min_eq_left hrd,intervalClamp_eq 0 (c j) (hc j) ⟨hr,hrd.trans hdj⟩,intervalClamp_eq 0 d hd ⟨hr,hrd⟩]
      · rw [min_eq_right hdr,intervalClamp_eq 0 (c j) (hc j) ⟨hd,hdj⟩]
        simp [intervalClamp,projIcc_of_right_le hd hdr]
  have hinterval s t (hst : s≤t) : Ioc s t∩Iic d=Ioc (min s d) (min t d) := by
    ext r
    simp only [mem_inter_iff,mem_Ioc,mem_Iic,lt_min_iff,le_min_iff]
    constructor
    · rintro ⟨⟨hs,ht⟩,hr⟩
      exact ⟨lt_of_le_of_lt (min_le_left s d) hs,ht,hr⟩
    · rintro ⟨hs,ht,hr⟩
      have hsd : s<d := by by_contra hh; rw [min_eq_right (le_of_not_gt hh)] at hs; linarith
      rw [min_eq_left hsd.le] at hs
      exact ⟨⟨hs,ht⟩,hr⟩
  have hi : Integrable (fun r => H (w,r)) (show SignedMeasure ℝ from (κ w).restrict (Iic d)).totalVariation := by
    rw [signed_totalVariation_restrict _ measurableSet_Iic]
    exact hHiw.restrict
  have he := cumulative_stieltjes_density_integral d hd (fun r => G (w,r)) (fun r => H (w,r))
    (hGm w) (hHm w) hGiw ((κ w).restrict (Iic d)) hi hp (by
      intro s t hst
      rw [VectorMeasure.restrict_apply _ measurableSet_Iic measurableSet_Ioc,hinterval s t hst,
        hκw _ _ (min_le_min_right d hst),hclip,hclip,
        hBw _ (intervalClamp_mem _ _ _ _),hBw _ (intervalClamp_mem _ _ _ _)]
      ring)
  have hf := hfw (realTimeClamp d)
  rw [min_eq_right (real_time_clamp_mono hdj),finite_prefix_time_of_real (c j) d (hc j) ⟨hd,hdj⟩ (hcT j).le] at hf
  change J (realTimeClamp d) w=signedIntegralRaw (κ w) ((Iic d).indicator (fun r => H (w,r))) at hf
  rw [hf,← signed_integral_restrict (κ w) measurableSet_Iic _ (hHm w) hHiw.restrict,he]

end Asakura.Chapter11
