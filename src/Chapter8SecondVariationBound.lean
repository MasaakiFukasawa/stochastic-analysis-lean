import Chapter8VariationalStability

open MeasureTheory Set
open scoped NNReal
namespace Asakura.Chapter8
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/-- Bound an actual second variation by the Lipschitz estimate on J.
This is deterministic and independent of the sample of the forcing. -/
theorem second_variation_bound {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E]
    (D : E → E →L[ℝ] E) (C : ℝ≥0) (hD : LipschitzWith C D)
    (X : E → ℝ → E) (J : E → ℝ → E →L[ℝ] E)
    (hcX : ∀ x,Continuous (X x)) (hcJ : ∀ x,Continuous (J x))
    (T A B L : ℝ) (hT : 0 ≤ T) (hA : 0 ≤ A) (hB : 0 ≤ B) (hL : 0<L)
    (hDb : ∀ x,‖D x‖ ≤ L)
    (hJb : ∀ x s,s∈Icc 0 T → ‖J x s‖ ≤ B)
    (hLip : ∀ x y s,s∈Icc 0 T → ‖X x s-X y s‖ ≤ A*‖x-y‖)
    (hJ : ∀ x s,s∈Icc 0 T → ∀ h,J x s h=h+∫ r in 0..s,D (X x r) (J x r h))
    (x : E) (t : ℝ) (ht : t∈Icc 0 T) (K : E →L[ℝ] E →L[ℝ] E)
    (hK : HasFDerivAt (fun z => J z t) K x) :
    ‖K‖ ≤ (C:ℝ)*A*B*T*Real.exp (L*T) := by
  let c : ℝ≥0 := ⟨(C:ℝ)*A*B*T*Real.exp (L*T),by positivity⟩
  have hJL := variational_initial_stability D C hD X J hcX hcJ T A B L hT hA hB hL hDb hJb hLip hJ
  have hc : LipschitzWith c (fun z => J z t) := by
    apply LipschitzWith.of_dist_le_mul
    intro z y
    change dist (J z t) (J y t) ≤ ((C:ℝ)*A*B*T*Real.exp (L*T))*dist z y
    simpa only [dist_eq_norm] using hJL z y t ht
  exact hK.le_of_lipschitz hc

end Asakura.Chapter8
