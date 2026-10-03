import Chapter12CylinderDirectionDivergence
import Chapter12WienerIncrementFromCoordinates
import Chapter12OrthogonalCylinderTest

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

/-- The Brownian-increment test in the Clark--Ocone proof, for every F in
the closed derivative domain and every smooth cylinder depending on past
times. Orthogonality and the divergence formula are derived, not assumed. -/
theorem clark_brownian_increment_test {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (T : ℝ) (hT : 0 < T)
    (W : FiniteWienerHilbert d T →ₗᵢ[ℝ] Lp ℝ 2 P)
    (hW : ∀ h, HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (X : BrownianTimeCoordinates d T → Ω → ℝ)
    (hX : ∀ z, X z =ᵐ[P] (W (brownianTimeDirection z) : Ω → ℝ)) :
    letI := finite_horizon_L2_nontrivial T hT
    ∀ (D : Lp ℝ 2 P →ₗ.[ℝ] Lp (FiniteWienerHilbert d T) 2 P),
      (D.graph : Set (Lp ℝ 2 P × Lp (FiniteWienerHilbert d T) 2 P)) =
        closure (range (cylinderPair P W univ dense_univ (fun h _ => hW h) 2 (by simp))) →
    ∀ (G : SmoothCylinder (FiniteWienerHilbert d T)) (i : Fin (d+1))
      (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T),
      (∀ j, ∃ z : BrownianTimeCoordinates d T,
        G.direction j = brownianTimeDirection z ∧ z.2.val ≤ a) →
    ∀ F : D.domain,
      (∫ w, G.value P W w * inner ℝ (D F w)
        (WithLp.toLp 2 (Pi.single i (finiteTimeIntervalVector T a b))) ∂P) =
      ∫ w, (F : Lp ℝ 2 P) w * G.value P W w *
        (X (i,⟨b,ha.trans hab,hb⟩) w-X (i,⟨a,ha,hab.trans hb⟩) w) ∂P := by
  letI := finite_horizon_L2_nontrivial T hT
  intro D hgraph G i a b ha hab hb hG F
  let h : FiniteWienerHilbert d T := WithLp.toLp 2 (Pi.single i (finiteTimeIntervalVector T a b))
  have horth (j) : inner ℝ (G.direction j) h = 0 := by
    obtain ⟨z,hz,hza⟩ := hG j
    rw [hz]
    exact finite_brownian_past_future z i a b hza
  have hgrad (w : Ω) : inner ℝ (G.gradient P W w) h = 0 :=
    cylinder_derivative_orthogonal G.direction h horth _
  obtain ⟨hi,hdiv⟩ := cylinder_direction_divergence P W univ dense_univ (fun h _ => hW h) D hgraph G h
  have he := hdiv F
  rw [L2.inner_def,L2.inner_def] at he
  have hl : (∫ w, inner ℝ (D F w) (hi.toLp _ w) ∂P) =
      ∫ w, G.value P W w * inner ℝ (D F w) h ∂P := by
    apply integral_congr_ae
    filter_upwards [hi.coeFn_toLp] with w hw
    rw [hw,inner_smul_right]
  have hr : (∫ w, inner ℝ ((F : Lp ℝ 2 P) w)
        (G.ibpTestLp P W univ dense_univ (fun h _ => hW h) h 2 (by simp) w) ∂P) =
      ∫ w, (F : Lp ℝ 2 P) w * G.value P W w *
        (X (i,⟨b,ha.trans hab,hb⟩) w-X (i,⟨a,ha,hab.trans hb⟩) w) ∂P := by
    apply integral_congr_ae
    filter_upwards [(G.ibpTest_memLp P W univ dense_univ (fun h _ => hW h) h 2 (by simp)).coeFn_toLp,
      wiener_increment_from_coordinates P T W X hX i a b ha hab hb] with w hw hinc
    dsimp only [SmoothCylinder.ibpTestLp]
    rw [hw]
    change (G.value P W w*W h w-inner ℝ (G.gradient P W w) h)*(F : Lp ℝ 2 P) w = _
    rw [hgrad,sub_zero]
    dsimp only [h]
    rw [hinc]
    ring
  exact hl.symm.trans (he.trans hr)

end Asakura.Chapter12
