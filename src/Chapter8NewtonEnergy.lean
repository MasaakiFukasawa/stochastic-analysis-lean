import Chapter8NewtonForms

open Set Filter
open scoped Topology
namespace Asakura.Chapter8

/-- Differentiation of the Newton energy after common-noise cancellation. -/
theorem newton_energy_derivative (q v : ℝ → ℝ) (δ b h t : ℝ)
    (hq : HasDerivAt q (v t) t)
    (hv : HasDerivAt v (-h*q t-δ*v t) t) :
    HasDerivAt (fun s => newtonEnergy δ b (q s) (v s))
      (-newtonDissipation δ b h (q t) (v t)) t := by
  have hh := (((hq.pow 2).const_mul (b+δ^2/2)).add
    ((hq.const_mul δ).mul hv)).add (hv.pow 2)
  convert hh using 1
  · rfl
  · dsimp [newtonDissipation]; ring

/-- The integrating factor step, including the closed time interval endpoints. -/
theorem dissipative_energy_bound (E : ℝ → ℝ) (r T : ℝ) (hT : 0 ≤ T)
    (hc : ContinuousOn E (Icc 0 T))
    (hD : ∀ t ∈ Ioo 0 T, ∃ d, HasDerivAt E d t ∧ d ≤ -2*r*E t) :
    ∀ t ∈ Icc 0 T, E t ≤ Real.exp (-2*r*t)*E 0 := by
  let F := fun t => Real.exp (2*r*t)*E t
  have hFc : ContinuousOn F (Icc 0 T) :=
    ((by fun_prop : Continuous (fun t : ℝ => Real.exp (2*r*t))).continuousOn).mul hc
  have hFD (t : ℝ) (ht : t ∈ Ioo 0 T) :
      ∃ d, HasDerivAt F d t ∧ d ≤ 0 := by
    obtain ⟨d,hd,hbd⟩ := hD t ht
    refine ⟨Real.exp (2*r*t)*(2*r*E t+d), ?_, ?_⟩
    · convert ((((hasDerivAt_id t).const_mul (2*r)).exp).mul hd) using 1
      · rfl
      · simp only [id_eq]; ring
    · exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (by linarith)
  have ha : AntitoneOn F (Icc 0 T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 T) hFc
    · intro t ht
      obtain ⟨d,hd,_⟩ := hFD t (by simpa using ht)
      exact hd.differentiableAt.differentiableWithinAt
    · intro t ht
      obtain ⟨d,hd,hbd⟩ := hFD t (by simpa using ht)
      rw [hd.deriv]; exact hbd
  intro t ht
  have hh := ha (show (0:ℝ) ∈ Icc 0 T from ⟨le_rfl,hT⟩) ht ht.1
  have hb := mul_le_mul_of_nonneg_left hh (Real.exp_pos (-2*r*t)).le
  have hex : Real.exp (-2*r*t)*Real.exp (2*r*t) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1 <;> congr 1 <;> ring
  dsimp only [F] at hb
  rwa [← mul_assoc,hex,one_mul,mul_zero,Real.exp_zero,one_mul] at hb

/-- Scalar Newton path contraction, with an arbitrary time-dependent stiffness
inside the manuscript's Hessian interval. -/
theorem scalar_newton_contraction (l u δ : ℝ) (hl : 0 < l)
    (hlu : l ≤ u) (hδ : Real.sqrt u - Real.sqrt l < δ) :
    ∃ b r : ℝ, 0 < r ∧ 0 < b+δ^2/4 ∧ ∀ (q v H : ℝ → ℝ) (T : ℝ), 0 ≤ T →
      ContinuousOn q (Icc 0 T) → ContinuousOn v (Icc 0 T) →
      (∀ t ∈ Ioo 0 T, l ≤ H t ∧ H t ≤ u) →
      (∀ t ∈ Ioo 0 T, HasDerivAt q (v t) t) →
      (∀ t ∈ Ioo 0 T, HasDerivAt v (-H t*q t-δ*v t) t) →
      ∀ t ∈ Icc 0 T,
        newtonEnergy δ b (q t) (v t) ≤
          Real.exp (-2*r*t)*newtonEnergy δ b (q 0) (v 0) := by
  obtain ⟨b,r,hr,hpos,hform⟩ := newton_uniform_form_rate l u δ hl hlu hδ
  have hp := hpos 1 (-δ/2) (Or.inl one_ne_zero)
  have hpdet : 0 < b+δ^2/4 := by dsimp [newtonEnergy] at hp; nlinarith only [hp]
  refine ⟨b,r,hr,hpdet,?_⟩
  intro q v H T hT hq hv hH hdq hdv
  apply dissipative_energy_bound _ r T hT
  · dsimp [newtonEnergy]
    exact (((hq.pow 2).const_mul _).add ((hq.const_mul δ).mul hv)).add (hv.pow 2)
  · intro t ht
    refine ⟨-newtonDissipation δ b (H t) (q t) (v t),
      newton_energy_derivative q v δ b (H t) t (hdq t ht) (hdv t ht), ?_⟩
    have hh := hform (H t) (hH t ht).1 (hH t ht).2 (q t) (v t)
    linarith

end Asakura.Chapter8
