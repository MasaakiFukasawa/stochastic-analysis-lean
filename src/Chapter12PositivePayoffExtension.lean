import Chapter12LognormalPayoffMoments

open MeasureTheory Set
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

def positiveOrthant (d : ℕ) : Set (Fin d → ℝ) := {x | ∀ i,0<x i}

noncomputable def positivePayoffExtension {d : ℕ} (h : positiveOrthant d → ℝ)
    (x : Fin d → ℝ) : ℝ := by
  classical
  exact if hx : x∈positiveOrthant d then h ⟨x,hx⟩ else 0

theorem positive_payoff_extension_measurable {d : ℕ} (h : positiveOrthant d → ℝ)
    (hm : Measurable h) : Measurable (positivePayoffExtension h) := by
  classical
  have hs : MeasurableSet (positiveOrthant d) := by
    change MeasurableSet {x : Fin d → ℝ | ∀ i,0<x i}
    simpa only [Set.setOf_forall] using
      MeasurableSet.iInter (fun i : Fin d => measurableSet_lt (measurable_const (a := (0:ℝ))) (measurable_pi_apply i))
  apply measurable_of_restrict_of_restrict_compl hs
  · have he : (positiveOrthant d).domRestrict (positivePayoffExtension h)=h := by
      funext y
      exact dif_pos y.property
    rw [he]
    exact hm
  · have he : (positiveOrthant d)ᶜ.domRestrict (positivePayoffExtension h)=fun _ => (0:ℝ) := by
      funext x
      exact dif_neg x.property
    rw [he]
    exact measurable_const

theorem positive_payoff_extension_bound {d : ℕ} (h : positiveOrthant d → ℝ)
    (C : ℝ) (n : ℕ) (hb : ∀ x,|h x|≤C*(1+‖x.val‖^n)) :
    ∀ x,|positivePayoffExtension h x|≤|C| *(1+‖x‖^n) := by
  intro x
  unfold positivePayoffExtension
  split_ifs with hx
  · exact (hb ⟨x,hx⟩).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
  · simp only [abs_zero]
    positivity

theorem positive_payoff_extension_lognormal {d : ℕ} (h : positiveOrthant d → ℝ)
    (x y : Fin d → ℝ) (hx : ∀ i,0<x i) :
    positivePayoffExtension h (fun i => x i*Real.exp (y i))=
      h ⟨(fun i => x i*Real.exp (y i)),fun i => mul_pos (hx i) (Real.exp_pos _)⟩ := by
  unfold positivePayoffExtension
  exact dif_pos (fun i => mul_pos (hx i) (Real.exp_pos _))

end Asakura.Chapter12
