import Chapter12AllSobolevReciprocal
import Chapter12MalliavinCovarianceAllSobolev
import Chapter12AllVectorSobolevFiniteSum
import Chapter12CovarianceInverseDirections

open MeasureTheory ProbabilityTheory Set ENNReal
namespace Asakura.Chapter12
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

theorem malliavin_inverse_covariance_sobolev {Ω I:Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]
    (H:RealHilbertSpaceData) [Nontrivial H] (P:Measure Ω) [IsProbabilityMeasure P]
    (W:H →ₗᵢ[ℝ] Lp ℝ 2 P) (S:Set H) (hS:Dense S)
    (hcore:∀u∈S,HasLaw (W u:Ω → ℝ) (gaussianReal 0 ⟨‖u‖^2,sq_nonneg _⟩) P)
    (hdense:∀(q:ℝ≥0∞) [Fact (1≤q)] (hq:q≠⊤),
      DenseRange (fun c:SmoothCylinder H => c.valueLp P W S hS hcore q hq))
    (D:Lp ℝ 2 P →ₗ.[ℝ] Lp H 2 P) (hD:D.IsClosed)
    (hg:(D.graph:Set _)=closure (range (cylinderPair P W S hS hcore 2 (by simp))))
    (F:I → Lp ℝ 2 P) (U:I → Lp H 2 P)
    (hF:∀i,HasAllSobolevJets H P W S hS hcore (F i)) (hDU:∀i,(F i,U i)∈D.graph)
    (hpos:∀ᵐw∂P,0<(derivativeGram (fun i => U i w)).det)
    (hi:∀(p:ℝ≥0∞) [Fact (1≤p)] (hp:p≠⊤),
      MemLp (fun w => ((derivativeGram (fun i => U i w)).det)⁻¹) p P) :
    (∀i j,HasAllSobolevJets H P W S hS hcore (fun w => (derivativeGram (fun i => U i w))⁻¹ i j)) ∧
    (∀i,HasAllVectorSobolevJets H P W S hS hcore
      (fun w => ∑j,(derivativeGram (fun l => U l w))⁻¹ i j • U j w)) ∧
    ∀i j,∀ᵐw∂P,inner ℝ (U j w) (∑l,(derivativeGram (fun a => U a w))⁻¹ i l • U l w)=
      if i=j then 1 else 0 := by
  obtain ⟨hU,hΓ,hd,ha⟩ := malliavin_covariance_all_sobolev H P W S hS hcore hdense D hg F U hF hDU
  have hinv := all_sobolev_reciprocal H P W S hS hcore hdense D hD hg _ hd hpos hi
  have hentries i j:HasAllSobolevJets H P W S hS hcore
      (fun w => (derivativeGram (fun l => U l w))⁻¹ i j) := by
    have hh := all_sobolev_product H P W S hS hcore hdense _ _ hinv (ha i j)
    simp only [Matrix.inv_def,Ring.inverse_eq_inv,Matrix.smul_apply,smul_eq_mul]
    exact hh
  refine ⟨hentries,?_,?_⟩
  · intro i
    apply all_vector_sobolev_finset_sum H P W S hS hcore Finset.univ
    intro j hj
    exact all_sobolev_scalar_vector_product H P W S hS hcore hdense _ _ (hentries i j) (hU j)
  · intro i j
    filter_upwards [hpos] with w hw
    exact inverse_covariance_direction (fun l => U l w) hw.ne' i j
end Asakura.Chapter12
#print axioms Asakura.Chapter12.malliavin_inverse_covariance_sobolev
