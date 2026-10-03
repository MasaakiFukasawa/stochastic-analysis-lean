import Chapter12LpBochnerPointwise
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Topology.DenseEmbedding

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

/-- Pointwise identification for Hilbert-valued Lp integrals. Scalar
identifications on a countable dense set of directions give one common
exceptional null set. -/
theorem Hilbert_Lp_bochner_integral_pointwise
    {α Ω H : Type*} [MeasurableSpace α] [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (μ : Measure α) [SigmaFinite μ] (P : Measure Ω) [IsProbabilityMeasure P]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 2 ≤ p)
    (S : α × Ω → H) (hSm : Measurable S) (hL : ∀ x, MemLp (fun w => S (x,w)) p P)
    (hi : Integrable (fun x => (hL x).toLp _) μ)
    (hSi : ∀ w, Integrable (fun x => S (x,w)) μ) :
    ((∫ x,(hL x).toLp _ ∂μ : Lp H p P) : Ω → H) =ᵐ[P] (fun w => ∫ x,S (x,w) ∂μ) := by
  obtain ⟨v,hv⟩ := TopologicalSpace.exists_dense_seq (α := H)
  have he (n : ℕ) : ∀ᵐ w ∂P,
      ⟪v n,(∫ x,(hL x).toLp _ ∂μ : Lp H p P) w⟫ = ⟪v n,∫ x,S (x,w) ∂μ⟫ := by
    let L : H →L[ℝ] ℝ := innerSL ℝ (v n)
    let J := L.compLpL p P
    have hLj (x) : MemLp (fun w => L (S (x,w))) p P := L.comp_memLp' (hL x)
    have hJe (x) : J ((hL x).toLp _) = (hLj x).toLp _ := by
      apply Lp.ext
      filter_upwards [L.coeFn_compLp ((hL x).toLp _),(hL x).coeFn_toLp,(hLj x).coeFn_toLp] with w h1 h2 h3
      change L.compLp ((hL x).toLp _) w = _
      rw [h1,h2,h3]
    have hJi : Integrable (fun x => (hLj x).toLp _) μ := by
      simpa only [hJe] using J.integrable_comp hi
    have hJint : J (∫ x,(hL x).toLp _ ∂μ) = ∫ x,(hLj x).toLp _ ∂μ := by
      rw [←J.integral_comp_comm hi]
      simp only [hJe]
    have hraw := Lp_bochner_integral_pointwise μ P p hp (fun z => L (S z))
      (L.continuous.measurable.comp hSm) hLj hJi
    have hcoe := L.coeFn_compLp (∫ x,(hL x).toLp _ ∂μ)
    change (J (∫ x,(hL x).toLp _ ∂μ) : Ω → ℝ) =ᵐ[P] _ at hcoe
    rw [hJint] at hcoe
    filter_upwards [hcoe,hraw] with w h1 h2
    change L ((∫ x,(hL x).toLp _ ∂μ : Lp H p P) w) = L (∫ x,S (x,w) ∂μ)
    rw [←h1,h2]
    exact L.integral_comp_comm (hSi w)
  have hall : ∀ᵐ w ∂P, ∀ n, ⟪v n,(∫ x,(hL x).toLp _ ∂μ : Lp H p P) w⟫ =
      ⟪v n,∫ x,S (x,w) ∂μ⟫ := ae_all_iff.mpr he
  filter_upwards [hall] with w hw
  apply ext_inner_left ℝ
  have heq : (fun h : H => ⟪h,(∫ x,(hL x).toLp _ ∂μ : Lp H p P) w⟫) =
      (fun h : H => ⟪h,∫ x,S (x,w) ∂μ⟫) :=
    hv.equalizer (by fun_prop) (by fun_prop) (funext hw)
  exact congrFun heq

end Asakura.Chapter12
