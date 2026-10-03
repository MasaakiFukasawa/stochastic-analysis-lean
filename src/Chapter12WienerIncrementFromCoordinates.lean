import Chapter12FinitePastFuture

open MeasureTheory Set Filter
open scoped ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

theorem finite_time_interval_difference (T a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    finiteTimeIntervalVector T 0 b-finiteTimeIntervalVector T 0 a = finiteTimeIntervalVector T a b := by
  apply Lp.ext
  have h0 (s t : ℝ) : (finiteTimeIntervalVector T s t : ℝ → ℝ) =ᵐ[(volume.restrict (Ioi (0:ℝ))).restrict (Iic T)]
      (Ioc s t).indicator (fun _ => (1:ℝ)) := indicatorConstLp_coeFn
  filter_upwards [Lp.coeFn_sub (finiteTimeIntervalVector T 0 b) (finiteTimeIntervalVector T 0 a),
    h0 0 b,h0 0 a,h0 a b] with t ht h1 h2 h3
  rw [ht,Pi.sub_apply,h1,h2,h3]
  simp only [Set.indicator_apply,Set.mem_Ioc]
  split_ifs <;> norm_num at * <;> grind

/-- The interval increment identity follows solely from the coordinate
identities, so it holds for the very Wiener map defining the closed D. -/
theorem wiener_increment_from_coordinates {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {d : ℕ} (T : ℝ)
    (W : FiniteWienerHilbert d T →ₗᵢ[ℝ] Lp ℝ 2 P)
    (X : BrownianTimeCoordinates d T → Ω → ℝ)
    (hX : ∀ z, X z =ᵐ[P] (W (brownianTimeDirection z) : Ω → ℝ))
    (i : Fin (d+1)) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T) :
    (W (WithLp.toLp 2 (Pi.single i (finiteTimeIntervalVector T a b))) : Ω → ℝ) =ᵐ[P]
      fun w => X (i,⟨b,ha.trans hab,hb⟩) w-X (i,⟨a,ha,hab.trans hb⟩) w := by
  classical
  let za : BrownianTimeCoordinates d T := (i,⟨a,ha,hab.trans hb⟩)
  let zb : BrownianTimeCoordinates d T := (i,⟨b,ha.trans hab,hb⟩)
  have hd : brownianTimeDirection zb-brownianTimeDirection za =
      WithLp.toLp 2 (Pi.single i (finiteTimeIntervalVector T a b)) := by
    apply PiLp.ext
    intro j
    change ((Pi.single i (finiteTimeIntervalVector T 0 b) : Fin (d+1) → _) j)-
      ((Pi.single i (finiteTimeIntervalVector T 0 a) : Fin (d+1) → _) j) =
      ((Pi.single i (finiteTimeIntervalVector T a b) : Fin (d+1) → _) j)
    by_cases hj : j = i
    · subst j
      simpa only [Pi.single_eq_same] using finite_time_interval_difference T a b ha hab
    · simp [Pi.single_eq_of_ne hj]
  rw [← hd,W.map_sub]
  filter_upwards [Lp.coeFn_sub (W (brownianTimeDirection zb)) (W (brownianTimeDirection za)),
    hX za,hX zb] with w hw h1 h2
  rw [hw,Pi.sub_apply,← h1,← h2]

end Asakura.Chapter12
