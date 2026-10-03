import Chapter11MeasurableTimeDensity
import Chapter2SignedDensityIntegral
import Chapter4FinitePathLift

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter4
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- Constant bank holdings give the bank-price increment. -/
theorem constant_variation_integral_at {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {T : EReal} [Fact (0≤T)]
    (c : ℕ → ℝ) (hc : ∀ n,0≤c n) (hcT : ∀ n,(c n:EReal)<T)
    (hcc : ∀ t,t<⊤ → ∃ n,t<realTimeClamp (T:=T) (c n))
    (A I : ClosedTime T → Ω → ℝ) (k d : ℝ) (hd : 0≤d) (hdT : (d:EReal)<T)
    (hI : VariationIntegralFormula P c hc A (fun _ => k) I) :
    I (realTimeClamp d)=ᵐ[P] fun w => k*(A (realTimeClamp d) w-A ⊥ w) := by
  have hdt := real_time_below d hd hdT
  obtain ⟨j,hj⟩ := hcc _ hdt
  have hdj : d≤c j := by
    change (realTimeClamp d:EReal)<(realTimeClamp (c j):EReal) at hj
    rw [real_time_clamp_eq d hd hdT.le,real_time_clamp_eq (c j) (hc j) (hcT j).le] at hj
    exact EReal.coe_le_coe_iff.mp hj.le
  obtain ⟨ν,hs,hν,_,he⟩ := hI j
  have hz : realTimeClamp (T:=T) 0=⊥ := by
    apply Subtype.ext
    exact real_time_clamp_eq 0 le_rfl ((EReal.coe_le_coe hd).trans hdT.le)
  filter_upwards [hs,hν,he] with w hs hν he
  have hf := he (realTimeClamp d)
  rw [min_eq_right (real_time_clamp_mono hdj),finite_prefix_time_of_real (c j) d (hc j) ⟨hd,hdj⟩ (hcT j).le] at hf
  rw [hf]
  have hh : signedCumulative (ν w) (fun _ => k) d=signedIntegralRaw (ν w) ((Ioc 0 d).indicator (fun _ => k)) := by
    apply signed_integral_congr_of_absolute_continuity (ν w).totalVariation (ν w) (by rfl)
    filter_upwards [hs] with r hr
    simp only [Set.indicator,mem_Iic,mem_Ioc,hr.1,true_and]
  rw [hh,signed_integral_indicator_const _ _ measurableSet_Ioc,hν 0 d hd,
    intervalClamp_eq 0 (c j) (hc j) ⟨hd,hdj⟩,intervalClamp_eq 0 (c j) (hc j) ⟨le_rfl,hc j⟩,hz]

end Asakura.Chapter11
