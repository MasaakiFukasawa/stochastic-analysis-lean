import EndToEndProbabilityTests

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.EndToEnd
set_option backward.isDefEq.respectTransparency false

/-- The density argument printed in the Cramer--Wold proof: integrate
 |p_n-p| = p_n+p-2 min(p_n,p), then apply dominated convergence to the minimum. -/
theorem probability_density_L1 {E : Type*} [MeasurableSpace E]
    (μ : Measure E) (p : ℕ → E → ℝ) (q : E → ℝ)
    (hp : ∀ n,Integrable (p n) μ) (hq : Integrable q μ)
    (hp0 : ∀ n,∀ᵐ x ∂μ,0 ≤ p n x) (hq0 : ∀ᵐ x ∂μ,0 ≤ q x)
    (hpm : ∀ n,(∫ x,p n x ∂μ)=1) (hqm : (∫ x,q x ∂μ)=1)
    (hlim : ∀ᵐ x ∂μ,Tendsto (fun n => p n x) atTop (𝓝 (q x))) :
    Tendsto (fun n => ∫ x,|p n x-q x| ∂μ) atTop (𝓝 0) := by
  have hm n : AEStronglyMeasurable (fun x => min (p n x) (q x)) μ :=
    (continuous_fst.min continuous_snd).comp_aestronglyMeasurable
      ((hp n).aestronglyMeasurable.prodMk hq.aestronglyMeasurable)
  have hb n : ∀ᵐ x ∂μ,‖min (p n x) (q x)‖ ≤ q x := by
    filter_upwards [hp0 n,hq0] with x hx hqx
    simpa only [Real.norm_eq_abs,abs_of_nonneg (le_min hx hqx)] using min_le_right (p n x) (q x)
  have hi n : Integrable (fun x => min (p n x) (q x)) μ :=
    hq.mono' (hm n) (hb n)
  have ht : Tendsto (fun n => ∫ x,min (p n x) (q x) ∂μ) atTop (𝓝 (∫ x,q x ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence q hm hq hb
    filter_upwards [hlim] with x hx
    simpa only [min_self] using hx.min (tendsto_const_nhds (x:=q x))
  rw [hqm] at ht
  have he n : (∫ x,|p n x-q x| ∂μ)=2-2*(∫ x,min (p n x) (q x) ∂μ) := by
    have heq : (fun x => |p n x-q x|) =
        (fun x => p n x+q x-2*min (p n x) (q x)) := by
      funext x
      rcases le_total (p n x) (q x) with h | h
      · rw [abs_of_nonpos (sub_nonpos.mpr h),min_eq_left h]; ring
      · rw [abs_of_nonneg (sub_nonneg.mpr h),min_eq_right h]; ring
    rw [heq,integral_sub (show Integrable (fun x => p n x+q x) μ from (hp n).add hq) ((hi n).const_mul 2),
      integral_add (hp n) hq,integral_const_mul,hpm n,hqm]
    ring
  simp_rw [he]
  simpa using (tendsto_const_nhds (x:=(2:ℝ))).sub (ht.const_mul 2)

#print axioms probability_density_L1
end Asakura.EndToEnd
