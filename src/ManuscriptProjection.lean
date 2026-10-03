import ConvexTail
open Set Filter
open scoped Topology
namespace Asakura

/-- app1:274--309: approximate minimizers, convex-tail Cauchy selection,
completeness and closedness. No projection existence theorem is called. -/
theorem manuscript_projection_exists {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (C : Set H)
    (hne : C.Nonempty) (hc : IsClosed C) (hconv : Convex ℝ C) (u : H) :
    ∃ v ∈ C, ∀ w ∈ C, ‖u - v‖ ≤ ‖u - w‖ := by
  classical
  let a := sInf ((fun w => ‖u-w‖) '' C)
  have hne' : ((fun w => ‖u-w‖) '' C).Nonempty := hne.image _
  have hb : BddBelow ((fun w => ‖u-w‖) '' C) :=
    ⟨0, by rintro y ⟨w,hw,rfl⟩; exact norm_nonneg _⟩
  have ha0 : 0 ≤ a := le_csInf hne' (by rintro y ⟨w,hw,rfl⟩; exact norm_nonneg _)
  have hamin : ∀ w ∈ C, a ≤ ‖u-w‖ := fun w hw => csInf_le hb ⟨w,hw,rfl⟩
  have hchoose : ∀ n : ℕ, ∃ w ∈ C, ‖u-w‖ < a + 1 / ((n:ℝ)+1) := by
    intro n
    obtain ⟨y, ⟨w,hw,rfl⟩, hy⟩ := exists_lt_of_csInf_lt hne'
      (lt_add_of_pos_right a (by positivity : 0 < 1 / ((n:ℝ)+1)))
    exact ⟨w,hw,hy⟩
  choose h hC hdist using hchoose
  have hbound : ∀ n, ‖h n‖ ≤ a + 1 + ‖u‖ := by
    intro n
    have htri : ‖h n‖ ≤ ‖u-h n‖ + ‖u‖ := by
      have ht := norm_sub_le u (u-h n)
      simpa [sub_sub_cancel, add_comm] using ht
    have hfrac : 1 / ((n:ℝ)+1) ≤ 1 := by
      apply (div_le_one (by positivity)).mpr
      linarith [Nat.cast_nonneg (α := ℝ) n]
    linarith [hdist n]
  obtain ⟨g, hg, hgc⟩ := convex_tail_selection h (a+1+‖u‖) hbound
  have hgC : ∀ n, g n ∈ C := by
    intro n
    exact convexHull_min (by rintro w ⟨k,hk,rfl⟩; exact hC k) hconv (hg n)
  have hgd : ∀ n, ‖u-g n‖ ≤ a + 1 / ((n:ℝ)+1) := by
    intro n
    have hball : convexHull ℝ (h '' Set.Ici n) ⊆ Metric.closedBall u (a+1/((n:ℝ)+1)) := by
      apply convexHull_min _ (convex_closedBall u _)
      rintro w ⟨k,hk,rfl⟩
      rw [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev]
      have hfrac : 1 / ((k:ℝ)+1) ≤ 1 / ((n:ℝ)+1) :=
        one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hk 1)
      linarith [hdist k]
    have hh := hball (hg n)
    simpa [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] using hh
  obtain ⟨v,hv⟩ := cauchySeq_tendsto_of_complete hgc
  have hvC : v ∈ C := hc.mem_of_tendsto hv (Eventually.of_forall hgC)
  have hvd : ‖u-v‖ ≤ a := by
    have hnorm := ((tendsto_const_nhds (x := u)).sub hv).norm
    have hr : Tendsto (fun n : ℕ => a + 1 / ((n:ℝ)+1)) atTop (𝓝 a) := by
      simpa using (tendsto_const_nhds (x := a)).add tendsto_one_div_add_atTop_nhds_zero_nat
    exact le_of_tendsto_of_tendsto' hnorm hr hgd
  exact ⟨v,hvC,fun w hw => hvd.trans (hamin w hw)⟩

/-- app1:310--321: uniqueness via midpoint and parallelogram, already explicit. -/
theorem manuscript_projection_unique {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (C : Set H) (hc : Convex ℝ C) (u v w : H)
    (hv : v ∈ C) (hw : w ∈ C)
    (hminv : ∀ z ∈ C, ‖u-v‖ ≤ ‖u-z‖)
    (hminw : ∀ z ∈ C, ‖u-w‖ ≤ ‖u-z‖) : v = w :=
  projection_unique C hc u v w hv hw hminv hminw

/-- app1:323: move by inner(u-v,h)/norm(h)^2 and contradict minimality. -/
theorem manuscript_projection_orthogonal {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (K : Submodule ℝ H) (u v : H) (hv : v ∈ K) :
    (∀ w ∈ K, ‖u-v‖ ≤ ‖u-w‖) ↔ ∀ h ∈ K, inner ℝ (u-v) h = 0 := by
  constructor
  · intro hmin h hh
    by_contra hn
    have hh0 : h ≠ 0 := by intro hz; simp [hz] at hn
    have hnorm : 0 < ‖h‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hh0)
    let c : ℝ := inner ℝ (u-v) h / ‖h‖^2
    have hpert := hmin (v+c • h) (K.add_mem hv (K.smul_mem c hh))
    have hexp : ‖u-(v+c • h)‖^2 = ‖u-v‖^2 - 2*c*inner ℝ (u-v) h + c^2*‖h‖^2 := by
      rw [show u-(v+c • h) = (u-v)-c • h by module, norm_sub_sq_real]
      simp [inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
      ring
    have hc : c * ‖h‖^2 = inner ℝ (u-v) h := div_mul_cancel₀ _ (ne_of_gt hnorm)
    have hsq : 0 < (inner ℝ (u-v) h)^2 := sq_pos_of_ne_zero hn
    have hs := mul_nonneg (sub_nonneg.mpr hpert) (add_nonneg (norm_nonneg (u-(v+c • h))) (norm_nonneg (u-v)))
    have hnormc : c^2 * ‖h‖^2 = c * inner ℝ (u-v) h := by nlinarith [hc]
    have hprod : 0 < c * inner ℝ (u-v) h := by
      dsimp [c]
      rw [div_mul_eq_mul_div]
      exact div_pos (by nlinarith) hnorm
    nlinarith
  · intro horth w hw
    have hperp := horth (w-v) (K.sub_mem hw hv)
    have heq : u-w = (u-v)-(w-v) := by module
    have hsq := norm_sub_sq_real (u-v) (w-v)
    rw [← heq, hperp, mul_zero, sub_zero] at hsq
    nlinarith [norm_nonneg (u-v), norm_nonneg (u-w), sq_nonneg ‖w-v‖]

end Asakura
