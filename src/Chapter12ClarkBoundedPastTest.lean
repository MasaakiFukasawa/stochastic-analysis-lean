import Chapter12ClarkPastTest
import Chapter12FinitePastFuture
import Chapter12WienerIncrementFromCoordinates

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology RealInnerProductSpace
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

/-- The manuscript's increment test for bounded past-measurable random
variables, with actual interval directions and Brownian increments. -/
theorem clark_bounded_past_increment_test {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (T : ℝ) (hT : 0 < T)
    (W : FiniteWienerHilbert d T →ₗᵢ[ℝ] Lp ℝ 2 P)
    (hW : ∀ h, HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (X : BrownianTimeCoordinates d T → Ω → ℝ)
    (hXm : ∀ z, Measurable (X z)) (hXc : ∀ w, Continuous (fun z => X z w))
    (hX : ∀ z, X z =ᵐ[P] (W (brownianTimeDirection z) : Ω → ℝ)) :
    letI := finite_horizon_L2_nontrivial T hT
    ∀ (D : Lp ℝ 2 P →ₗ.[ℝ] Lp (FiniteWienerHilbert d T) 2 P),
      (D.graph : Set _) = closure (range (cylinderPair P W univ dense_univ (fun h _ => hW h) 2 (by simp))) →
    ∀ (F : D.domain) (i : Fin (d+1)) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T)
      (G : Ω → ℝ), MemLp G ∞ P →
      AEStronglyMeasurable[MeasurableSpace.comap
        (fun w (z : BrownianTimeCoordinates d a) => X (z.1,⟨z.2.val,z.2.property.1,z.2.property.2.trans (hab.trans hb)⟩) w)
        inferInstance] G P →
      (∫ w,G w*inner ℝ (D F w)
        (WithLp.toLp 2 (Pi.single i (finiteTimeIntervalVector T a b))) ∂P) =
      ∫ w,(F : Lp ℝ 2 P) w*G w*
        (X (i,⟨b,ha.trans hab,hb⟩) w-X (i,⟨a,ha,hab.trans hb⟩) w) ∂P := by
  letI := finite_horizon_L2_nontrivial T hT
  letI : Fact ((2:ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
  intro D hgraph F i a b ha hab hb G hG hgen
  let e : BrownianTimeCoordinates d a → BrownianTimeCoordinates d T :=
    fun z => (z.1,⟨z.2.val,z.2.property.1,z.2.property.2.trans (hab.trans hb)⟩)
  have hec : Continuous e := continuous_fst.prodMk (continuous_snd.subtype_val.subtype_mk _)
  letI : Nonempty (BrownianTimeCoordinates d a) := ⟨(0,⟨0,le_rfl,ha⟩)⟩
  obtain ⟨times,htimes⟩ := TopologicalSpace.exists_dense_seq (α := BrownianTimeCoordinates d a)
  let h : FiniteWienerHilbert d T := WithLp.toLp 2 (Pi.single i (finiteTimeIntervalVector T a b))
  have h4 : MemLp G 4 P := hG.mono_exponent le_top
  have hg4 : AEStronglyMeasurable[MeasurableSpace.comap
      (fun w z => X (e z) w) inferInstance] (h4.toLp G) P :=
    hgen.congr h4.coeFn_toLp.symm
  have hx := closed_derivative_past_test P W univ dense_univ (fun h _ => hW h)
    (fun z => X (e z)) (fun z => hXm (e z)) (fun w => (hXc w).comp hec)
    (fun z => brownianTimeDirection (e z)) (fun z => hX (e z)) times htimes h
    (fun z => finite_brownian_past_future (e z) i a b z.2.property.2)
    D hgraph F (h4.toLp G) hg4
  have hi := wiener_increment_from_coordinates P T W X hX i a b ha hab hb
  calc
    _ = ∫ w,h4.toLp G w*inner ℝ (D F w) h ∂P := by
      apply integral_congr_ae
      filter_upwards [h4.coeFn_toLp] with w hw
      rw [hw]
    _ = ∫ w,(F : Lp ℝ 2 P) w*h4.toLp G w*W h w ∂P := hx
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [h4.coeFn_toLp,hi] with w hw hv
      rw [hw]
      dsimp only [h]
      rw [hv]

end Asakura.Chapter12
