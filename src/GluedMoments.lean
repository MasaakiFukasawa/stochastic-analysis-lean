import GluedGaussian

open MeasureTheory ProbabilityTheory Set
namespace Asakura
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma glued_process_mean (W : (ℕ × UnitCube 1) → Ω → ℝ)
    (hl : ∀ p, MemLp (W p) 2 P) (h0 : ∀ k ω, W (k,cubeZero) ω = 0)
    (hm : ∀ p, (∫ ω, W p ω ∂P) = 0) (t : ℝ) :
    (∫ ω, gluedProcess W t ω ∂P) = 0 := by
  obtain ⟨N,hN⟩ := exists_nat_gt t
  have he : gluedProcess W t = fun ω => ∑ k ∈ Finset.range N, W (k,unitTimeCube k t) ω := by
    funext ω
    exact gluedPath_eq_sum _ (fun k => h0 k ω) N t hN.le
  rw [he, integral_finsetSum]
  · simp [hm]
  · intro k hk
    exact (hl _).integrable (by norm_num)

lemma glued_process_covariance (W : (ℕ × UnitCube 1) → Ω → ℝ)
    (hl : ∀ p, MemLp (W p) 2 P) (h0 : ∀ k ω, W (k,cubeZero) ω = 0)
    (hc : ∀ k l s t, cov[W (k,s), W (l,t); P] =
      if k = l then min (s.val 0) (t.val 0) else 0)
    (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    cov[gluedProcess W s, gluedProcess W t; P] = min s t := by
  obtain ⟨N,hN⟩ := exists_nat_gt (max s t)
  have hsN : s ≤ N := (le_max_left _ _).trans hN.le
  have htN : t ≤ N := (le_max_right _ _).trans hN.le
  have he (u : ℝ) (hu : u ≤ N) : gluedProcess W u =
      fun ω => ∑ k ∈ Finset.range N, W (k,unitTimeCube k u) ω := by
    funext ω
    exact gluedPath_eq_sum _ (fun k => h0 k ω) N u hu
  rw [he s hsN, he t htN, covariance_fun_sum_fun_sum'
    (fun k hk => hl (k,unitTimeCube k s)) (fun k hk => hl (k,unitTimeCube k t))]
  simp_rw [hc]
  have hdiag : (∑ k ∈ Finset.range N, ∑ l ∈ Finset.range N,
      if k = l then min (unitTime k s) (unitTime l t) else 0) =
      ∑ k ∈ Finset.range N, min (unitTime k s) (unitTime k t) := by
    apply Finset.sum_congr rfl
    intro k hk
    simp [Finset.sum_ite_eq, hk]
  change (∑ k ∈ Finset.range N, ∑ l ∈ Finset.range N,
    if k = l then min (unitTime k s) (unitTime l t) else 0) = _
  rw [hdiag]
  exact unitTime_min_sum N s t ⟨hs,hsN⟩ ⟨ht,htN⟩
end Asakura
