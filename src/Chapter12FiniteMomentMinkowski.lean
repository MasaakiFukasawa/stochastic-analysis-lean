import Chapter12MomentToSobolevNorm

open MeasureTheory
open scoped ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

theorem finite_moment_minkowski_bound {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (p : ℕ) (hp : 0<p) [Fact (1≤(p:ℝ≥0∞))]
    (f : ι → Ω → ℝ) (hf : ∀ i,MemLp (f i) (p:ℝ≥0∞) P)
    (hn : ∀ i x,0≤f i x) (a : ι → ℝ) (ha : ∀ i,0≤a i) (c : ℝ) (hc : 0≤c)
    (hb : ∀ i,(∫ x,(f i x)^p ∂P)≤(c*a i)^p) :
    (∫ x,(∑ i,f i x)^p ∂P)≤(c*∑ i,a i)^p := by
  classical
  let v := fun i => (hf i).toLp (f i)
  have hv i : ‖v i‖^p=∫ x,(f i x)^p ∂P := by
    rw [lp_nat_norm_power p hp]
    apply integral_congr_ae
    filter_upwards [(hf i).coeFn_toLp] with x hx
    rw [hx,Real.norm_eq_abs,abs_of_nonneg (hn i x)]
  have hnorm i : ‖v i‖≤c*a i := by
    apply (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hc (ha i)) hp.ne').mp
    rw [hv]
    exact hb i
  have hsum : ‖∑ i,v i‖≤c*∑ i,a i := by
    apply (norm_sum_le _ _).trans
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => hnorm i)
  have he : (∫ x,(∑ i,f i x)^p ∂P)=‖∑ i,v i‖^p := by
    rw [lp_nat_norm_power p hp]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ v,
      ae_all_iff.mpr (fun i => (hf i).coeFn_toLp)] with x hx hi
    rw [hx]
    have hpoint : ∑ i,v i x=∑ i,f i x := Finset.sum_congr rfl (fun i _ => hi i)
    rw [hpoint,Real.norm_eq_abs,abs_of_nonneg (Finset.sum_nonneg (fun i _ => hn i x))]
  rw [he]
  exact pow_le_pow_left₀ (norm_nonneg _) hsum p

end Asakura.Chapter12
