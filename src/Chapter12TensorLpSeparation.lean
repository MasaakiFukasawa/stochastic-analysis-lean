import Chapter12HilbertTensorSeparable
import Chapter12LpDualSeparation

open MeasureTheory Set TopologicalSpace
open scoped ENNReal Topology TensorProduct
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

theorem tensor_Lp_separated_by_pure_tests {Ω E H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [SeparableSpace E]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [SeparableSpace H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (p q : ℝ≥0∞) [Fact (1≤p)] [Fact (1≤q)] [ENNReal.HolderConjugate p q]
    (S : Set (Lp ℝ q P)) (hS : Dense S)
    (U : Lp (CompletedHilbertTensor H E) p P)
    (hu : ∀ h e,∀ v∈S,∫ w,inner ℝ (hilbertPureTensor h e) (U w)*v w ∂P=0) : U=0 := by
  have hae (h : H) (e : E) : (fun w => inner ℝ (hilbertPureTensor h e) (U w)) =ᵐ[P] 0 := by
    let L := innerSL ℝ (hilbertPureTensor h e)
    have hz : L.compLp U=0 := scalar_Lp_separated_by_dense_tests P p q S hS (L.compLp U) (by
      intro v hv
      have he := L.coeFn_compLp U
      calc
        _=(∫ w,inner ℝ (hilbertPureTensor h e) (U w)*v w ∂P) := by
          apply integral_congr_ae
          filter_upwards [he] with w hw
          rw [hw]
          rfl
        _=0 := hu h e v hv)
    have he0 : (L.compLp U : Ω → ℝ) =ᵐ[P] 0 := by
      rw [hz]
      exact Lp.coeFn_zero ℝ p P
    filter_upwards [he0,L.coeFn_compLp U] with w hw he
    exact he.symm.trans hw
  apply Lp.ext
  have hc : ∀ n m : ℕ,(fun w => inner ℝ (hilbertPureTensor (denseSeq H n) (denseSeq E m)) (U w)) =ᵐ[P] 0 :=
    fun n m => hae _ _
  filter_upwards [ae_all_iff.mpr (fun n => ae_all_iff.mpr (hc n)),Lp.coeFn_zero (CompletedHilbertTensor H E) p P] with w hw hz
  rw [hz]
  apply hilbert_pure_separate
  have hd := (denseRange_denseSeq H).prodMap (denseRange_denseSeq E)
  have hj : Continuous (fun x : H × E => inner ℝ (hilbertPureTensor x.1 x.2) (U w)) :=
    ((UniformSpace.Completion.continuous_coe (H ⊗[ℝ] E)).comp TensorProduct.continuous_tmul).inner continuous_const
  have hall : ∀ x : H × E,inner ℝ (hilbertPureTensor x.1 x.2) (U w)=0 :=
    isClosed_property hd (isClosed_eq hj continuous_const) (fun x => hw x.1 x.2)
  intro h e
  exact hall (h,e)

end Asakura.Chapter12
