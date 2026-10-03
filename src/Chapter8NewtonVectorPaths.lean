import Chapter8NewtonSpectral

open Set Filter
open scoped Topology RealInnerProductSpace
namespace Asakura.Chapter8

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem newton_vector_energy_derivative (q v : ℝ → E) (δ b t : ℝ)
    (H : E →ₗ[ℝ] E) (hq : HasDerivAt q (v t) t)
    (hv : HasDerivAt v (-H (q t)-δ • v t) t) :
    HasDerivAt (fun s => newtonVectorEnergy δ b (q s) (v s))
      (-newtonVectorDissipation δ b H (q t) (v t)) t := by
  have hh := (((hq.norm_sq).const_mul (b+δ^2/2)).add
    ((hq.inner ℝ hv).const_mul δ)).add hv.norm_sq
  convert hh using 1
  · rfl
  · simp only [newtonVectorDissipation,inner_sub_right,inner_neg_right,inner_smul_right,
      real_inner_self_eq_norm_sq,real_inner_comm (v t) (q t)]
    ring

/-- Multidimensional path contraction. H may vary with time; no derivative of
its eigenvectors is taken. -/
theorem vector_newton_contraction [FiniteDimensional ℝ E]
    (l u δ : ℝ) (hl : 0 < l) (hlu : l ≤ u)
    (hδ : Real.sqrt u - Real.sqrt l < δ) :
    ∃ b r : ℝ, 0 < r ∧ 0 < b+δ^2/4 ∧ ∀ (q v : ℝ → E) (H : ℝ → E →ₗ[ℝ] E) (T : ℝ),
      0 ≤ T → ContinuousOn q (Icc 0 T) → ContinuousOn v (Icc 0 T) →
      (∀ t ∈ Ioo 0 T, (H t).IsSymmetric) →
      (∀ t ∈ Ioo 0 T, ∀ x, l*‖x‖^2 ≤ ⟪x,H t x⟫ ∧ ⟪x,H t x⟫ ≤ u*‖x‖^2) →
      (∀ t ∈ Ioo 0 T, HasDerivAt q (v t) t) →
      (∀ t ∈ Ioo 0 T, HasDerivAt v (-H t (q t)-δ • v t) t) →
      ∀ t ∈ Icc 0 T, newtonVectorEnergy δ b (q t) (v t) ≤
        Real.exp (-2*r*t)*newtonVectorEnergy δ b (q 0) (v 0) := by
  obtain ⟨b,r,hr,hpos,hform⟩ := newton_uniform_form_rate l u δ hl hlu hδ
  have hp := hpos 1 (-δ/2) (Or.inl one_ne_zero)
  have hpdet : 0 < b+δ^2/4 := by dsimp [newtonEnergy] at hp; nlinarith only [hp]
  refine ⟨b,r,hr,hpdet,?_⟩
  intro q v H T hT hq hv hH hbound hdq hdv
  apply dissipative_energy_bound _ r T hT
  · dsimp [newtonVectorEnergy]
    exact (((hq.norm.pow 2).const_mul _).add ((hq.inner hv).const_mul δ)).add (hv.norm.pow 2)
  · intro t ht
    refine ⟨-newtonVectorDissipation δ b (H t) (q t) (v t),
      newton_vector_energy_derivative q v δ b t (H t) (hdq t ht) (hdv t ht), ?_⟩
    have hh := newton_spectral_form_bound l u δ b r (H t) (hH t ht)
      (fun x => (hbound t ht x).1) (fun x => (hbound t ht x).2) hform (q t) (v t)
    linarith

end Asakura.Chapter8
