import Chapter12SobolevSequenceClosure
import Chapter12SobolevSequenceDerivative
import Chapter12SobolevSequenceComposition
import Chapter12SobolevSequenceProduct
import Chapter12ReciprocalRegularizerLimits
import Chapter12ReciprocalRegularizerDerivativeBound
import Chapter12ClosedC1ChainRawOutput
import Chapter12AllSobolevGradient
import Chapter12AllSobolevScalarVectorProduct
import Chapter12AllSobolevProduct

open MeasureTheory ProbabilityTheory Set ENNReal Filter
open scoped Topology ContDiff
namespace Asakura.Chapter12
set_option maxHeartbeats 4200000
set_option backward.isDefEq.respectTransparency false

theorem all_sobolev_reciprocal_square {Ω:Type*} [MeasurableSpace Ω]
    (H:RealHilbertSpaceData) [Nontrivial H] (P:Measure Ω) [IsProbabilityMeasure P]
    (W:H →ₗᵢ[ℝ] Lp ℝ 2 P) (S:Set H) (hS:Dense S)
    (hcore:∀u∈S,HasLaw (W u:Ω → ℝ) (gaussianReal 0 ⟨‖u‖^2,sq_nonneg _⟩) P)
    (hdense:∀(q:ℝ≥0∞) [Fact (1≤q)] (hq:q≠⊤),
      DenseRange (fun c:SmoothCylinder H => c.valueLp P W S hS hcore q hq))
    (D:Lp ℝ 2 P →ₗ.[ℝ] Lp H 2 P) (hD:D.IsClosed)
    (hg:(D.graph:Set _)=closure (range (cylinderPair P W S hS hcore 2 (by simp))))
    (F:Lp ℝ 2 P) (U:Lp H 2 P) (hFU:(F,U)∈D.graph)
    (hF:HasAllSobolevJets H P W S hS hcore F) (hpos:∀ᵐw∂P,0<F w)
    (hi:∀(p:ℝ≥0∞) [Fact (1≤p)] (hp:p≠⊤),MemLp (fun w => (F w)⁻¹^2) p P) :
    HasAllSobolevJets H P W S hS hcore (fun w => (F w)⁻¹^2) := by
  let ε := fun n:ℕ => (1:ℝ)/(n+1)
  have hε n:0<ε n := by dsimp [ε];positivity
  let A := fun n w => reciprocalSquareRegularizer (ε n) (F w)
  have hA n:HasAllSobolevJets H P W S hS hcore (A n) :=
    all_sobolev_smooth_composition H P W S hS hcore hdense _
      (reciprocal_square_regularizer_smooth (ε n) (hε n))
      (reciprocal_square_regularizer_growth (ε n) (hε n)) F hF
  have hU := all_sobolev_gradient H P W S hS hcore D hg F U hF hFU
  let V := fun w => (-2*F w) • U w
  have hV:HasAllVectorSobolevJets H P W S hS hcore V :=
    all_sobolev_scalar_vector_product H P W S hS hcore hdense _ _
      (all_sobolev_smul H P W S hS hcore F hF (-2)) hU
  let Z := fun n w => (A n w)^2 • V w
  have hZ n:HasAllVectorSobolevJets H P W S hS hcore (Z n) :=
    all_sobolev_scalar_vector_product H P W S hS hcore hdense _ _
      (all_sobolev_square H P W S hS hcore hdense _ (hA n)) hV
  have hAm n:MemLp (A n) 2 P := all_sobolev_memLp H P W S hS hcore _ (hA n) 2 (by simp)
  have hZm n:MemLp (Z n) 2 P := all_vector_sobolev_memLp H P W S hS hcore _ (hZ n) 2 (by simp)
  have hAZ n:((hAm n).toLp _,(hZm n).toLp _)∈D.graph := by
    apply closed_C1_chain_raw_output P W S hS hcore 2 (by simp) D hD hg F U hFU
      (reciprocalSquareRegularizer (ε n))
      (fun x => ((-2*x)*reciprocalSquareRegularizer (ε n) x)*reciprocalSquareRegularizer (ε n) x)
      (reciprocal_square_regularizer_hasDerivAt (ε n) (hε n))
      (((continuous_const.mul continuous_id).mul
        (reciprocal_square_regularizer_smooth (ε n) (hε n)).continuous).mul
        (reciprocal_square_regularizer_smooth (ε n) (hε n)).continuous)
      (2*(1+(ε n)⁻¹)*(ε n)⁻¹) (by positivity)
      (reciprocal_square_regularizer_derivative_bound (ε n) (hε n))
    · exact (hAm n).coeFn_toLp
    · filter_upwards [(hZm n).coeFn_toLp] with w hw
      rw [hw]
      dsimp [Z,V,A]
      rw [smul_smul]
      congr 1
      ring
  have ht (p:ℝ≥0∞) [Fact (1≤p)] (hp:p≠⊤) (v:ℕ → Lp ℝ p P)
      (hv:∀m,(v m:Ω → ℝ)=ᵐ[P] A m) :
      Tendsto v atTop (𝓝 ((hi p hp).toLp _)) := by
    obtain ⟨hm,ht⟩ := reciprocal_square_regularizer_Lp_limit P p hp F (Lp.aestronglyMeasurable F) hpos (hi p hp)
    have he:∀m,v m=(hm m).toLp _ := fun m => Lp.ext ((hv m).trans (hm m).coeFn_toLp.symm)
    rw [show v=(fun m => (hm m).toLp _) from funext he]
    exact ht
  have hzero (p:ℝ≥0∞) [Fact (1≤p)] (hp:p≠⊤) (v:ℕ → Lp ℝ p P)
      (hv:∀m,(v m:Ω → ℝ)=ᵐ[P] A m) : CauchySeq v := (ht p hp v hv).cauchySeq
  have hc:∀k,ScalarEvenJetCauchy H P W S hS hcore A k := by
    intro k
    induction k with
    | zero => exact scalar_even_jet_cauchy_zero H P W S hS hcore A hzero
    | succ k ih =>
      have hB := iterated_polynomial_growth_mul (fun x:ℝ => x) (fun x:ℝ => x) contDiff_id contDiff_id
        (linear_map_all_derivatives_growth (ContinuousLinearMap.id ℝ ℝ))
        (linear_map_all_derivatives_growth (ContinuousLinearMap.id ℝ ℝ))
      have hsq:ScalarEvenJetCauchy H P W S hS hcore (fun n w => (A n w)^2) k := by
        simpa only [Function.comp_def,pow_two] using scalar_even_jet_cauchy_composition
          H P W S hS hcore hdense (fun x:ℝ => x*x) (contDiff_id.mul contDiff_id) hB A hA k ih
      have hz := scalar_vector_even_jet_cauchy_product H P W S hS hcore hdense
        (fun n w => (A n w)^2) (fun _ => V)
        (fun n => all_sobolev_square H P W S hS hcore hdense _ (hA n)) (fun _ => hV)
        k hsq (vector_even_jet_cauchy_const H P W S hS hcore hdense V k)
      exact scalar_even_jet_cauchy_of_derivative H P W S hS hcore D hg A Z hAm hZm hAZ hzero k hz
  exact all_sobolev_sequence_closed H P W S hS hcore A _ hA hc hi ht
end Asakura.Chapter12
#print axioms Asakura.Chapter12.all_sobolev_reciprocal_square
