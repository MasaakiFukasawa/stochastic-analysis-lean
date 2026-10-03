import Chapter12GraphClosure
import GaussianLimit

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false

/-- For deterministic Wiener integrals it suffices to prove the normal law
on a dense class of elementary integrands. The isometry determines the
variance after taking the L2 limit. -/
theorem wiener_gaussian_law_from_dense_core {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : Measure Ω) [IsProbabilityMeasure P] (W : H →ₗᵢ[ℝ] Lp ℝ 2 P)
    (S : Set H) (hS : Dense S)
    (hcore : ∀ h ∈ S, HasLaw (W h : Ω → ℝ)
      (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P) (h : H) :
    HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P := by
  obtain ⟨a,ha,hal⟩ := mem_closure_iff_seq_limit.mp (hS h)
  have hlim : Tendsto (fun n => W (a n)) atTop (𝓝 (W h)) :=
    W.continuous.continuousAt.tendsto.comp hal
  have hg : HasGaussianLaw (W h : Ω → ℝ) P :=
    Asakura.gaussian_L2_limit (fun n => (hcore (a n) (ha n)).hasGaussianLaw) hlim
  have hm : (∫ ω, W h ω ∂P) = 0 := by
    have hc := Asakura.L2_mean_continuous.continuousAt.tendsto.comp hlim
    have he n : (∫ ω, W (a n) ω ∂P) = 0 := by
      simpa only [integral_id_gaussianReal] using (hcore (a n) (ha n)).integral_eq
    change Tendsto (fun n => ∫ ω, W (a n) ω ∂P) atTop (𝓝 (∫ ω, W h ω ∂P)) at hc
    simp only [he] at hc
    exact (tendsto_nhds_unique hc tendsto_const_nhds)
  refine ⟨(Lp.memLp (W h)).aestronglyMeasurable.aemeasurable, ?_⟩
  rw [hg.map_eq_gaussianReal,hm,Asakura.L2_variance_inner,hm,zero_pow (by norm_num : (2:ℕ) ≠ 0),
    sub_zero,W.inner_map_map,real_inner_self_eq_norm_sq]
  congr 1
  apply NNReal.eq
  change max (‖h‖^2) 0 = ‖h‖^2
  exact max_eq_left (sq_nonneg _)

end Asakura.Chapter12
