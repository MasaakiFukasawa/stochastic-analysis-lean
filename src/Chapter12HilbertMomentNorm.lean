import Chapter12MomentToSobolevNorm

open MeasureTheory
open scoped ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

/-- Taking the moment root and using the already proved Lp triangle
inequality gives the printed sum of Sobolev norms. -/
theorem hilbert_moment_to_sobolev_norm {Ω I K : Type*} [MeasurableSpace Ω] [Fintype I] [NormedAddCommGroup K]
    {E : I → Type*} [∀ i,NormedAddCommGroup (E i)] {P : Measure Ω}
    (m : ℕ) (hm : 0<m) [Fact (1≤(m:ℝ≥0∞))]
    (z : Lp K (m:ℝ≥0∞) P) (v : ∀ i,Lp (E i) (m:ℝ≥0∞) P)
    (C : ℝ) (hC : 0≤C)
    (hb : (∫ x,‖z x‖^m ∂P)≤C^m*(∫ x,(∑ i,‖v i x‖)^m ∂P)) :
    ‖z‖≤C*∑ i,‖v i‖ := by
  classical
  let f := fun i => ((Lp.memLp (v i)).norm).toLp (fun x => ‖v i x‖)
  let F : Lp ℝ (m:ℝ≥0∞) P := ∑ i,f i
  have he : (F : Ω → ℝ)=ᵐ[P] (fun x => ∑ i,‖v i x‖) := by
    filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ f,
      ae_all_iff.mpr (fun i => ((Lp.memLp (v i)).norm).coeFn_toLp)] with x hs hi
    change (∑ i,f i) x=_
    rw [hs]
    exact Finset.sum_congr rfl (fun i _ => hi i)
  have hnorm (i : I) : ‖f i‖=‖v i‖ := by
    rw [Lp.norm_toLp,Lp.norm_def,eLpNorm_norm]
    exact (Lp.memLp (v i)).aestronglyMeasurable
  have hF : ‖F‖≤∑ i,‖v i‖ := by
    simpa only [hnorm] using (norm_sum_le Finset.univ f)
  have hi : (∫ x,(∑ i,‖v i x‖)^m ∂P)=‖F‖^m := by
    rw [lp_nat_norm_power m hm]
    apply integral_congr_ae
    filter_upwards [he] with x hx
    rw [hx,Real.norm_eq_abs,abs_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))]
  have hb' : ‖z‖^m≤(C*‖F‖)^m := by
    rw [lp_nat_norm_power m hm,mul_pow]
    simpa only [hi] using hb
  have hroot : ‖z‖≤C*‖F‖ :=
    (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _)) hm.ne').mp hb'
  exact hroot.trans (mul_le_mul_of_nonneg_left hF hC)

end Asakura.Chapter12
