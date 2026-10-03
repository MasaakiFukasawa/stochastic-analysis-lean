import FullAuditL2L1Projection
import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated

open MeasureTheory Filter Set
open scoped ENNReal
namespace Asakura.FullAudit
variable {Ω : Type*} {G H m : MeasurableSpace Ω} {P : @Measure Ω m}
  [IsProbabilityMeasure P]

/-- C2 follows directly from the orthogonal remainder of the L2 projection. -/
theorem projection_C2 (hG : G ≤ m) (X Y : Lp ℝ 2 P)
    (hY : AEStronglyMeasurable[G] Y P) :
    inner ℝ (condExpL2 ℝ ℝ hG X : Lp ℝ 2 P) Y = inner ℝ X Y := by
  letI : Fact (G ≤ m) := ⟨hG⟩
  symm
  rw [← sub_eq_zero, ← inner_sub_left, condExpL2]
  simp only [← Submodule.starProjection_apply,
    mem_lpMeas_iff_aestronglyMeasurable.mpr hY,
    Submodule.starProjection_inner_eq_zero X Y]

theorem projection_C2_integral (hG : G ≤ m) (X Y : Lp ℝ 2 P)
    (hY : AEStronglyMeasurable[G] Y P) :
    (∫ ω, X ω * Y ω ∂P) =
      ∫ ω, (condExpL2 ℝ ℝ hG X : Lp ℝ 2 P) ω * Y ω ∂P := by
  have hh := (projection_C2 hG X Y hY).symm
  simpa only [L2.inner_def, RCLike.inner_apply, conj_trivial, mul_comm] using hh

/-- Testing the difference against itself proves uniqueness, without an L1 CE theorem. -/
theorem projection_unique (hG : G ≤ m) (X Z : Lp ℝ 2 P)
    (hZ : AEStronglyMeasurable[G] Z P)
    (h : ∀ Y : Lp ℝ 2 P, AEStronglyMeasurable[G] Y P →
      inner ℝ Z Y = inner ℝ X Y) :
    Z = (condExpL2 ℝ ℝ hG X : Lp ℝ 2 P) := by
  let V := (condExpL2 ℝ ℝ hG X : Lp ℝ 2 P)
  have hV : AEStronglyMeasurable[G] V P := aestronglyMeasurable_condExpL2 hG X
  have hD : AEStronglyMeasurable[G] (Z-V : Lp ℝ 2 P) P :=
    (hZ.sub hV).congr (Lp.coeFn_sub Z V).symm
  have hh := h (Z-V) hD
  have hp := projection_C2 hG X (Z-V) hD
  have hz : inner ℝ (Z-V) (Z-V) = 0 := by
    rw [inner_sub_left]
    exact sub_eq_zero.mpr (hh.trans hp.symm)
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hz)

/-- C4 is linearity of the actual orthogonal projection. -/
theorem projection_C4 (hG : G ≤ m) (X Y : Lp ℝ 2 P) :
    (condExpL2 ℝ ℝ hG (X+Y) : Lp ℝ 2 P) =
      (condExpL2 ℝ ℝ hG X : Lp ℝ 2 P)+(condExpL2 ℝ ℝ hG Y : Lp ℝ 2 P) := by
  simp

/-- C5 uses the nested test spaces and C2 twice. -/
theorem projection_C5 (hHG : H ≤ G) (hG : G ≤ m) (X : Lp ℝ 2 P) :
    (condExpL2 ℝ ℝ (hHG.trans hG) (condExpL2 ℝ ℝ hG X : Lp ℝ 2 P) : Lp ℝ 2 P) =
      (condExpL2 ℝ ℝ (hHG.trans hG) X : Lp ℝ 2 P) := by
  apply projection_unique (hHG.trans hG)
  · exact aestronglyMeasurable_condExpL2 _ _
  · intro Y hY
    rw [projection_C2 (hHG.trans hG) _ Y hY]
    exact projection_C2 hG X Y (hY.mono hHG)

/-- C1 identifies the constant projection by testing against the constant one. -/
theorem projection_C1 (X : Lp ℝ 2 P) :
    (condExpL2 ℝ ℝ (bot_le : (⊥ : MeasurableSpace Ω) ≤ m) X : Lp ℝ 2 P) =ᵐ[P]
      fun _ => ∫ ω, X ω ∂P := by
  let V := (condExpL2 ℝ ℝ (bot_le : (⊥ : MeasurableSpace Ω) ≤ m) X : Lp ℝ 2 P)
  have hV := aestronglyMeasurable_condExpL2 (𝕜 := ℝ) (bot_le : (⊥ : MeasurableSpace Ω) ≤ m) X
  obtain ⟨c,hc⟩ := eq_const_of_measurable_bot hV.stronglyMeasurable_mk.measurable
  have he : V =ᵐ[P] fun _ => c := hV.ae_eq_mk.trans (ae_of_all _ fun ω => congrFun hc ω)
  let one : Lp ℝ 2 P := (memLp_const (1 : ℝ)).toLp (fun _ => 1)
  have hone : one =ᵐ[P] fun _ => (1 : ℝ) := (memLp_const (1 : ℝ)).coeFn_toLp
  have hom : AEStronglyMeasurable[⊥] one P := aestronglyMeasurable_const.congr hone.symm
  have hh := projection_C2_integral (bot_le : (⊥ : MeasurableSpace Ω) ≤ m) X one hom
  have hleft : (∫ ω, X ω * one ω ∂P) = ∫ ω, X ω ∂P :=
    integral_congr_ae (hone.mono fun ω hω => by simp [hω])
  have hright : (∫ ω, V ω * one ω ∂P) = c := by
    calc
      _ = ∫ _ : Ω, c ∂P := integral_congr_ae (by
        filter_upwards [he,hone] with ω hv ho
        simp [hv,ho])
      _ = c := by simp
  change (∫ ω, X ω * one ω ∂P) = ∫ ω, V ω * one ω ∂P at hh
  rw [hleft,hright] at hh
  simpa only [hh] using he
/-- C3 is obtained by testing against Y times each measurable L2 test function.
All three products belong to L2 by the boundedness of Y. -/
theorem projection_C3 (hG : G ≤ m) (X : Lp ℝ 2 P) (Y : Ω → ℝ)
    (hY : AEStronglyMeasurable[G] Y P) (hYinf : MemLp Y ∞ P) :
    let hXY : MemLp (Y * (X : Ω → ℝ)) 2 P := hYinf.mul (Lp.memLp X)
    let V := (condExpL2 ℝ ℝ hG X : Lp ℝ 2 P)
    (condExpL2 ℝ ℝ hG (hXY.toLp (Y * (X : Ω → ℝ))) : Lp ℝ 2 P) =ᵐ[P] Y * (V : Ω → ℝ) := by
  dsimp only
  let V := (condExpL2 ℝ ℝ hG X : Lp ℝ 2 P)
  have hV : AEStronglyMeasurable[G] V P := aestronglyMeasurable_condExpL2 hG X
  have hXY : MemLp (Y * (X : Ω → ℝ)) 2 P := hYinf.mul (Lp.memLp X)
  have hYV : MemLp (Y * (V : Ω → ℝ)) 2 P := hYinf.mul (Lp.memLp V)
  let A := hXY.toLp (Y * (X : Ω → ℝ))
  let B := hYV.toLp (Y * (V : Ω → ℝ))
  have hA : A =ᵐ[P] Y * (X : Ω → ℝ) := hXY.coeFn_toLp
  have hB : B =ᵐ[P] Y * (V : Ω → ℝ) := hYV.coeFn_toLp
  have hBm : AEStronglyMeasurable[G] B P := (hY.mul hV).congr hB.symm
  have he : B = (condExpL2 ℝ ℝ hG A : Lp ℝ 2 P) := by
    apply projection_unique hG A B hBm
    intro Z hZ
    have hYZ : MemLp (Y * (Z : Ω → ℝ)) 2 P := hYinf.mul (Lp.memLp Z)
    let W := hYZ.toLp (Y * (Z : Ω → ℝ))
    have hW : W =ᵐ[P] Y * (Z : Ω → ℝ) := hYZ.coeFn_toLp
    have hWm : AEStronglyMeasurable[G] W P := (hY.mul hZ).congr hW.symm
    have hh := projection_C2_integral hG X W hWm
    have hl : (∫ ω, X ω * W ω ∂P) = ∫ ω, A ω * Z ω ∂P := by
      apply integral_congr_ae
      filter_upwards [hA,hW] with ω ha hw
      simp only [ha,hw,Pi.mul_apply]
      ring
    have hr : (∫ ω, V ω * W ω ∂P) = ∫ ω, B ω * Z ω ∂P := by
      apply integral_congr_ae
      filter_upwards [hB,hW] with ω hb hw
      simp only [hb,hw,Pi.mul_apply]
      ring
    change (∫ ω, X ω * W ω ∂P) = ∫ ω, V ω * W ω ∂P at hh
    rw [hl,hr] at hh
    simpa only [L2.inner_def,RCLike.inner_apply,conj_trivial,mul_comm] using hh.symm
  exact (EventuallyEq.of_eq (congrArg (fun z : Lp ℝ 2 P => (z : Ω → ℝ)) he.symm)).trans hB

end Asakura.FullAudit
