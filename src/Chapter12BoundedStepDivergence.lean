import Chapter12ClarkBoundedPastTest
import Chapter12DivergenceDuality

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal Topology RealInnerProductSpace
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

/-- The divergence of a bounded adapted elementary integrand is its actual
weighted Brownian increment. The multiplier need not be Malliavin differentiable. -/
theorem bounded_past_step_divergence {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (T : ℝ) (hT : 0<T)
    (W : FiniteWienerHilbert d T →ₗᵢ[ℝ] Lp ℝ 2 P)
    (hW : ∀ h,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (X : BrownianTimeCoordinates d T → Ω → ℝ)
    (hXm : ∀ z,Measurable (X z)) (hXc : ∀ w,Continuous (fun z => X z w))
    (hX : ∀ z,X z=ᵐ[P] (W (brownianTimeDirection z) : Ω → ℝ)) :
    letI := finite_horizon_L2_nontrivial T hT
    ∀ (D : Lp ℝ 2 P →ₗ.[ℝ] Lp (FiniteWienerHilbert d T) 2 P),
      (D.graph : Set _)=closure (range (cylinderPair P W univ dense_univ (fun h _ => hW h) 2 (by simp))) →
    ∀ (i : Fin (d+1)) (a b : ℝ) (ha : 0≤a) (hab : a≤b) (hb : b≤T)
      (G : Ω → ℝ),MemLp G ∞ P →
      AEStronglyMeasurable[MeasurableSpace.comap
        (fun w (z : BrownianTimeCoordinates d a) => X (z.1,⟨z.2.val,z.2.property.1,z.2.property.2.trans (hab.trans hb)⟩) w)
        inferInstance] G P →
    let h : FiniteWienerHilbert d T := WithLp.toLp 2 (Pi.single i (finiteTimeIntervalVector T a b))
    let Z := fun w => G w*(X (i,⟨b,ha.trans hab,hb⟩) w-X (i,⟨a,ha,hab.trans hb⟩) w)
    ∃ (hu : MemLp (fun w => G w • h) 2 P) (hz : MemLp Z 2 P),
      IsDivergence D (hu.toLp _) (hz.toLp _) := by
  letI := finite_horizon_L2_nontrivial T hT
  intro D hg i a b ha hab hb G hG hnat
  dsimp only
  let h : FiniteWienerHilbert d T := WithLp.toLp 2 (Pi.single i (finiteTimeIntervalVector T a b))
  have hu : MemLp (fun w => G w • h) 2 P := hG.smul (memLp_const h (p := 2) (μ := P))
  have hinc := wiener_increment_from_coordinates P T W X hX i a b ha hab hb
  have hz : MemLp (fun w => G w*(X (i,⟨b,ha.trans hab,hb⟩) w-X (i,⟨a,ha,hab.trans hb⟩) w)) 2 P :=
    (hG.mul (Lp.memLp (W h))).ae_eq (hinc.mono (fun w hw => by dsimp only [h,Pi.mul_apply] at *; rw [hw]))
  refine ⟨hu,hz,?_⟩
  intro Y
  have he := clark_bounded_past_increment_test P T hT W hW X hXm hXc hX D hg Y i a b ha hab hb G hG hnat
  rw [L2.inner_def,L2.inner_def]
  calc
    _ = ∫ w,G w*inner ℝ (D Y w) h ∂P := by
      apply integral_congr_ae
      filter_upwards [hu.coeFn_toLp] with w hw
      rw [hw,real_inner_smul_right]
    _ = _ := he
    _ = ∫ w,inner ℝ ((Y : Lp ℝ 2 P) w) (hz.toLp _ w) ∂P := by
      apply integral_congr_ae
      filter_upwards [hz.coeFn_toLp] with w hw
      rw [hw]
      change (Y : Lp ℝ 2 P) w*G w*(X (i,⟨b,ha.trans hab,hb⟩) w-X (i,⟨a,ha,hab.trans hb⟩) w)=
        (G w*(X (i,⟨b,ha.trans hab,hb⟩) w-X (i,⟨a,ha,hab.trans hb⟩) w))*(Y : Lp ℝ 2 P) w
      ring

end Asakura.Chapter12
