import Chapter12VariationalInvertibility
import Chapter8VariationalConstruction
import Chapter9VariationalOperatorDerivative

open Set
open scoped NNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

/-- Constructing the variational ODE on a slightly larger interval gives
all finite-time inverses and their exponential bound, including endpoints. -/
theorem constructed_variational_inverse {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
    (A : ℝ → E →L[ℝ] E) (hcA : Continuous A) (K : ℝ≥0)
    (hb : ∀ t,‖A t‖≤(K:ℝ)) (T : ℝ) (hT : 0≤T) :
    ∃ J : ℝ → E →L[ℝ] E,Continuous J ∧
      (∀ t∈Icc (0:ℝ) T,∀ v,J t v=v+∫ s in 0..t,A s (J s v)) ∧
      ∀ t∈Icc (0:ℝ) T,∃ e : E ≃L[ℝ] E,e.toContinuousLinearMap=J t ∧
        ‖e.symm.toContinuousLinearMap‖≤Real.exp ((K:ℝ)*t) := by
  obtain ⟨J,hcJ,hJ⟩ := Asakura.Chapter8.variational_operator_exists (T+1) (by linarith) A hcA K hb
  obtain ⟨h0,hd⟩ := Asakura.Chapter9.variational_integral_operator_derivative J A hcJ hcA (T+1)
    (by linarith) hJ
  refine ⟨J,hcJ,?_,?_⟩
  · intro t ht v
    exact hJ t ⟨ht.1,by linarith [ht.2]⟩ v
  · intro t ht
    apply variational_flow_equiv_with_inverse_bound J A t K ht.1 hcJ h0
    · intro s hs
      exact hd s ⟨hs.1,by linarith [hs.2,ht.2]⟩
    · intro s _
      exact hb s

end Asakura.Chapter12
