import Appendix
open Set Filter
open scoped Topology
namespace Asakura

/-- app1:344--378: choose approaching sequences, take image limits, prove the
uniform modulus by passing to limits, and prove uniqueness on the dense set. -/
theorem manuscript_uniform_extension {S T : Type*} [MetricSpace S] [MetricSpace T]
    [CompleteSpace T] (D : Set S) (hd : Dense D) (f : D → T) (hf : UniformContinuous f) :
    ∃! g : S → T, UniformContinuous g ∧ ∀ x : D, g x = f x := by
  classical
  have hseq : ∀ x : S, ∃ s : ℕ → S, (∀ n, s n ∈ D) ∧ Tendsto s atTop (𝓝 x) :=
    fun x => mem_closure_iff_seq_limit.mp (hd x)
  choose s hsD hst using hseq
  let a : S → ℕ → D := fun x n => ⟨s x n,hsD x n⟩
  have haC : ∀ x, CauchySeq (a x) := by
    intro x
    exact Metric.cauchySeq_iff.mpr ((Metric.cauchySeq_iff (u := s x)).mp (hst x).cauchySeq)
  have hlimit : ∀ x, ∃ y, Tendsto (fun n => f (a x n)) atTop (𝓝 y) :=
    fun x => cauchySeq_tendsto_of_complete (hf.comp_cauchySeq (haC x))
  choose g hgt using hlimit
  have hgu : UniformContinuous g := by
    apply Metric.uniformContinuous_iff.mpr
    intro ε hε
    obtain ⟨δ,hδ,hmod⟩ := Metric.uniformContinuous_iff.mp hf (ε/2) (by positivity)
    refine ⟨δ,hδ,?_⟩
    intro x y hxy
    have hnear : ∀ᶠ n in atTop, dist (a x n) (a y n) < δ :=
      ((hst x).dist (hst y)).eventually (gt_mem_nhds hxy)
    have hbound : ∀ᶠ n in atTop, dist (f (a x n)) (f (a y n)) ≤ ε/2 :=
      hnear.mono (fun n hn => (hmod hn).le)
    have hle := le_of_tendsto ((hgt x).dist (hgt y)) hbound
    exact hle.trans_lt (by linarith)
  have hrestrict : ∀ x : D, g x = f x := by
    intro x
    have hat : Tendsto (a x) atTop (𝓝 x) :=
      Metric.tendsto_nhds.mpr ((Metric.tendsto_nhds (u := s (x : S)) (a := (x : S))).mp (hst x))
    exact tendsto_nhds_unique (hgt x) (hf.continuous.continuousAt.tendsto.comp hat)
  refine ⟨g, ⟨hgu,hrestrict⟩, ?_⟩
  intro g' hg'
  funext x
  have ht : Tendsto (fun n => g' (s x n)) atTop (𝓝 (g' x)) :=
    hg'.1.continuous.continuousAt.tendsto.comp (hst x)
  have heq : (fun n => g' (s x n)) = (fun n => f (a x n)) :=
    funext (fun n => hg'.2 (a x n))
  rw [heq] at ht
  exact tendsto_nhds_unique ht (hgt x)

/-- app1:381--406: rescale a nonzero vector into a small ball at zero. -/
theorem manuscript_continuous_linear_bound {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E →ₗ[ℝ] F) (hA : Continuous A) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, ‖A x‖ ≤ C * ‖x‖ := by
  obtain ⟨δ,hδ,hsmall⟩ := Metric.continuousAt_iff.mp hA.continuousAt 1 (by norm_num)
  refine ⟨2/δ, by positivity, ?_⟩
  intro x
  by_cases hx : x = 0
  · simp [hx]
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let r : ℝ := δ / (2*‖x‖)
  have hr : 0 < r := div_pos hδ (by positivity)
  have hrnorm : ‖r • x‖ = δ/2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    dsimp [r]
    field_simp
  have hs : dist (r • x) 0 < δ := by rw [dist_zero_right, hrnorm]; linarith
  have hh := hsmall hs
  simp only [map_zero, dist_zero_right, map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hr] at hh
  have hmul : r * ‖x‖ = δ/2 := by dsimp [r]; field_simp
  have hrel : (2/δ) * r = 1/‖x‖ := by dsimp [r]; field_simp
  have hbound : r * ‖A x‖ ≤ 1 := hh.le
  have hposC : 0 < 2/δ := by positivity
  have h := mul_le_mul_of_nonneg_left hbound hposC.le
  rw [← mul_assoc, hrel] at h
  have h' := mul_le_mul_of_nonneg_right h hxpos.le
  simpa [mul_comm, mul_left_comm, mul_assoc, hxpos.ne'] using h'

/-- app1:381--406: the bound gives a uniform delta, completing all three implications. -/
theorem manuscript_linear_continuity_iff {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (A : E →ₗ[ℝ] F) :
    (Continuous A ↔ ∃ C : ℝ, 0 < C ∧ ∀ x, ‖A x‖ ≤ C*‖x‖) ∧
    (UniformContinuous A ↔ Continuous A) := by
  have hb : (∃ C : ℝ, 0 < C ∧ ∀ x, ‖A x‖ ≤ C*‖x‖) → UniformContinuous A := by
    rintro ⟨C,hC,hb⟩
    apply Metric.uniformContinuous_iff.mpr
    intro ε hε
    refine ⟨ε/C,div_pos hε hC,?_⟩
    intro x y hxy
    rw [dist_eq_norm,← map_sub]
    have hdist : ‖x-y‖ < ε/C := by simpa [dist_eq_norm] using hxy
    exact (hb (x-y)).trans_lt (by nlinarith [(lt_div_iff₀ hC).mp hdist])
  exact ⟨⟨manuscript_continuous_linear_bound A,fun h => (hb h).continuous⟩,
    ⟨UniformContinuous.continuous,fun h => hb (manuscript_continuous_linear_bound A h)⟩⟩

end Asakura
