import Chapter8SDELinearCoordinates
import Chapter8PhaseCoordinates

open MeasureTheory Set
open scoped BigOperators
namespace Asakura.Chapter8
open Asakura.Chapter4 Asakura.Chapter3Complete Asakura.FullAudit
open Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- The phase-space SDE yields the two integral equations used in the
Newton energy proof, in arbitrary continuous linear spatial coordinates. -/
theorem newton_sde_coordinates {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P n)
    (e : (Fin d → ℝ) ≃L[ℝ] E) (g : E → E) (hg : Continuous g)
    (δ : ℝ) (σ : Fin d → Fin n → ℝ) (x : Fin (d+d) → ℝ)
    (X : HalfClosedTime → Ω → Fin (d+d) → ℝ)
    (hX : VectorSDESolution P B.F B.W
      (Fin.addCases (fun i z => velocityProjection d z i)
        (fun i z => e.symm (-g (e (positionProjection d z))-δ • e (velocityProjection d z)) i))
      (Fin.addCases (fun _ _ _ => 0) (fun i j _ => σ i j)) (fun _ => x) X) :
    let Y := fun t w => (e (positionProjection d (X (realTimeClamp t) w)),
      e (velocityProjection d (X (realTimeClamp t) w)))
    (∀ w,Continuous (fun t => Y t w)) ∧
    ∀ᵐ w ∂P,Y 0 w=(e (positionProjection d x),e (velocityProjection d x)) ∧
      (∀ t≥0,(Y t w).1=e (positionProjection d x)+∫ s in 0..t,(Y s w).2) ∧
      (∀ t≥0,(Y t w).2=e (velocityProjection d x)+
        (∫ s in 0..t,-g (Y s w).1-δ • (Y s w).2)+
        ∑ j,B.W j (realTimeClamp t) w • e (fun i => σ i j)) := by
  let b : (Fin (d+d) → ℝ) → (Fin (d+d) → ℝ) := fun z => Fin.addCases (fun i => velocityProjection d z i)
    (fun i => e.symm (-g (e (positionProjection d z))-δ • e (velocityProjection d z)) i)
  let S : Fin (d+d) → Fin n → ℝ := Fin.addCases (fun _ _ => 0) σ
  let Q := e.toContinuousLinearMap.comp (positionProjection d)
  let V := e.toContinuousLinearMap.comp (velocityProjection d)
  have hb : Continuous b := by
    apply continuous_pi
    intro i
    refine Fin.addCases ?_ ?_ i <;> intro j
    · simp only [b,Fin.addCases_left]
      change Continuous (fun z => velocityProjection d z j)
      exact (continuous_apply j).comp (velocityProjection d).continuous
    · simp only [b,Fin.addCases_right]
      change Continuous (fun z => e.symm (-g (e (positionProjection d z))-δ • e (velocityProjection d z)) j)
      fun_prop
  have hq z : Q (b z)=V z := by
    apply congrArg e
    ext i
    change b z (Fin.castAdd d i)=velocityProjection d z i
    exact Fin.addCases_left i
  have hv z : V (b z)= -g (Q z)-δ • V z := by
    have hh : velocityProjection d (b z)=e.symm (-g (Q z)-δ • V z) := by
      ext i
      change b z (Fin.natAdd d i)=e.symm (-g (Q z)-δ • V z) i
      simpa only [b,Fin.addCases_right,Q,V,ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe]
    change e (velocityProjection d (b z))=_
    rw [hh,e.apply_symm_apply]
  have hSq j : Q (fun i => S i j)=0 := by
    have hh : positionProjection d (fun i => S i j)=0 := by
      ext i
      change S (Fin.castAdd d i) j=0
      simp only [S,Fin.addCases_left]
    change e (positionProjection d (fun i => S i j))=0
    rw [hh,map_zero]
  have hSv j : V (fun i => S i j)=e (fun i => σ i j) := by
    apply congrArg e
    ext i
    change S (Fin.natAdd d i) j=σ i j
    simp only [S,Fin.addCases_right]
  have hX' : VectorSDESolution P B.F B.W (fun i y => b y i) (fun i j _ => S i j) (fun _ => x) X := by
    convert hX using 1 <;> funext i <;> refine Fin.addCases ?_ ?_ i <;> intro j <;>
      simp only [b,S,Fin.addCases_left,Fin.addCases_right]
  have hc w : Continuous (fun t => X (realTimeClamp t) w) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (hX.path w _ (half_real_time_finite t)).comp real_time_clamp_continuous.continuousAt
  dsimp only
  refine ⟨fun w => (Q.continuous.comp (hc w)).prodMk (V.continuous.comp (hc w)),?_⟩
  have hzero : realTimeClamp (T := ⊤) 0=⊥ := by
    apply Subtype.ext
    rw [real_time_clamp_eq 0 le_rfl (by simp)]
    rfl
  filter_upwards [sde_linear_coordinate_equation P B b hb S x X hX' Q,
    sde_linear_coordinate_equation P B b hb S x X hX' V,
    hX.initial_value P (EReal.coe_lt_top 0) B.F B.W _ _ (fun _ => x) X] with w hwq hwv hw0
  refine ⟨by rw [hzero,hw0],?_,?_⟩
  · intro t ht
    simpa only [hq,hSq,smul_zero,Finset.sum_const_zero,add_zero,Q,V,ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe] using hwq t ht
  · intro t ht
    simpa only [hv,hSv,Q,V,ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe] using hwv t ht

end Asakura.Chapter8
