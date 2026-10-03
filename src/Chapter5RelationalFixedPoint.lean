import Chapter5BSDEProductContraction

namespace Asakura.Chapter5

/-- Build the map from existence of frozen solutions. The contraction
estimate also proves independence of the choice of each frozen solution. -/
theorem relational_fixed_point_from_squared_estimate
    {E : Type*} [MetricSpace E] [CompleteSpace E] [Nonempty E]
    (R : E → E → Prop) (hex : ∀ x,∃ y,R x y)
    (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1)
    (hcontract : ∀ x x' y y',R x y → R x' y' → dist y y'^2 ≤ q*dist x x'^2) :
    ∃! x,R x x := by
  classical
  let F := fun x => Classical.choose (hex x)
  have hF x : R x (F x) := Classical.choose_spec (hex x)
  have hsingle x y (hy : R x y) : F x = y := by
    have hh := hcontract x x (F x) y (hF x) hy
    simp only [dist_self,zero_pow (by norm_num : (2:ℕ) ≠ 0),mul_zero] at hh
    exact dist_eq_zero.mp (by nlinarith [dist_nonneg (x := F x) (y := y)])
  obtain ⟨x,hx,hu⟩ := fixed_point_from_squared_estimate F q hq hq1
    (fun x y => hcontract x y (F x) (F y) (hF x) (hF y))
  refine ⟨x,?_,?_⟩
  · simpa only [hx] using hF x
  · intro y hy
    exact hu y (hsingle y y hy)

/-- Apply the actual two-component a-priori estimates to the relation
of frozen BSDE solutions. This produces a unique nonlinear solution
without postulating a pre-existing single-valued BSDE map. -/
theorem bsde_relational_fixed_point {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] [CompleteSpace H]
    (R : WithLp 2 (H × H) → WithLp 2 (H × H) → Prop)
    (hex : ∀ x,∃ y,R x y)
    (D : WithLp 2 (H × H) → WithLp 2 (H × H) → ℝ)
    (T C β : ℝ) (hT : 0 ≤ T) (hβ : 2*(1+T)*C^2 < β)
    (hY : ∀ x x' y y',R x y → R x' y' → ‖y.fst-y'.fst‖^2 ≤ (T/β)*D x x')
    (hZ : ∀ x x' y y',R x y → R x' y' → ‖y.snd-y'.snd‖^2 ≤ (1/β)*D x x')
    (hD : ∀ x x',D x x' ≤ 2*C^2*(‖x.fst-x'.fst‖^2+‖x.snd-x'.snd‖^2)) :
    ∃! x,R x x := by
  have hb : 0 < β := lt_of_le_of_lt (by positivity) hβ
  obtain ⟨hq,hq1⟩ := contraction_ratio T C β hT hβ
  apply relational_fixed_point_from_squared_estimate R hex (2*(1+T)*C^2/β) hq hq1
  intro x x' y y' hy hy'
  simp only [dist_eq_norm,WithLp.prod_norm_sq_eq_of_L2,WithLp.sub_fst,WithLp.sub_snd]
  calc
    _ ≤ (T/β)*D x x'+(1/β)*D x x' := add_le_add (hY x x' y y' hy hy') (hZ x x' y y' hy hy')
    _ = ((1+T)/β)*D x x' := by ring
    _ ≤ ((1+T)/β)*(2*C^2*(‖x.fst-x'.fst‖^2+‖x.snd-x'.snd‖^2)) :=
      mul_le_mul_of_nonneg_left (hD x x') (by positivity)
    _ = _ := by ring

end Asakura.Chapter5
