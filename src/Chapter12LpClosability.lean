import Chapter12LpDualSeparation
import Chapter12GraphClosure

open MeasureTheory Set Filter ENNReal
open scoped Topology
namespace Asakura.Chapter12
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

/-- The manuscript's closability proof in the actual Lp spaces. Its inputs
are the Gaussian integration-by-parts identity and a dense cylinder class;
separation of derivative limits is proved, not assumed. -/
theorem malliavin_Lp_closable {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [SecondCountableTopology H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] [HolderConjugate p q]
    (D : Lp ℝ p P →ₗ.[ℝ] Lp H p P)
    (S : Set (Lp ℝ q P)) (hS : Dense S)
    (B : S → H → Lp ℝ q P)
    (hIBP : ∀ (v : S) (h : H) (f : D.domain),
      ∫ w, (inner ℝ h (D f w))*v.val w ∂P = ∫ w, (f.val w)*(B v h w) ∂P) :
    D.IsClosable := by
  let pairing := (ContinuousLinearMap.mul ℝ ℝ).lpPairing P p q
  let left : S × H → Lp H p P →L[ℝ] ℝ := fun i =>
    (pairing.flip i.1.val).comp ((innerSL ℝ i.2).compLpL p P)
  let right : S × H → Lp ℝ p P →L[ℝ] ℝ := fun i => pairing.flip (B i.1 i.2)
  have hleft (i : S × H) (u : Lp H p P) :
      left i u = ∫ w, (inner ℝ i.2 (u w))*i.1.val w ∂P := by
    change pairing ((innerSL ℝ i.2).compLp u) i.1.val = _
    rw [ContinuousLinearMap.lpPairing_eq_integral]
    apply integral_congr_ae
    filter_upwards [(innerSL ℝ i.2).coeFn_compLp u] with w hw
    rw [hw]; rfl
  have hright (i : S × H) (u : Lp ℝ p P) :
      right i u = ∫ w, u w*(B i.1 i.2 w) ∂P := by
    exact ContinuousLinearMap.lpPairing_eq_integral _ _ _
  apply closable_of_duality D left right
  · intro i f
    rw [hleft,hright]
    exact hIBP i.1 i.2 f
  · intro u hu
    apply hilbert_Lp_separated_by_dense_tests P p q S hS u
    intro h v hv
    simpa only [hleft] using hu (⟨v,hv⟩,h)

end Asakura.Chapter12
