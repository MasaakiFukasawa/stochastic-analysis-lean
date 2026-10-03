import Chapter12QuotientDivergence
import Chapter12AsianWeights
import Chapter12FiniteGreekExponents

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000

/-- The printed Asian vega weight is a divergence, not just a rational
identity. Sobolev membership of J0,I1 and the two pairings are supplied by
the time-integral constructions; inverse moments control the quotient. -/
theorem asian_vega_divergence {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial H] [CompleteSpace H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h ∈ S, HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (D : Lp ℝ 2 P →ₗ.[ℝ] Lp H 2 P)
    (D4 : Lp ℝ 4 P →ₗ.[ℝ] Lp H 4 P) (D8 : Lp ℝ 8 P →ₗ.[ℝ] Lp H 8 P)
    (hD4 : D4.IsClosed) (hD8 : D8.IsClosed)
    (hg : (D.graph : Set _) = closure (range (cylinderPair P W S hS hcore 2 (by simp))))
    (hg4 : (D4.graph : Set _) = closure (range (cylinderPair P W S hS hcore 4 (by simp))))
    (hg8 : (D8.graph : Set _) = closure (range (cylinderPair P W S hS hcore 8 (by simp))))
    (J0 J1 I1 I2 : Ω → ℝ) (U V : Ω → H)
    (hJ0 : MemLp J0 8 P) (hI1 : MemLp I1 8 P) (hU : MemLp U 8 P) (hV : MemLp V 8 P)
    (h0 : (hJ0.toLp _,hU.toLp _) ∈ D8.graph) (h1 : (hI1.toLp _,hV.toLp _) ∈ D8.graph)
    (hpos : ∀ᵐ w ∂P, 0 < I1 w) (hinv : MemLp (fun w => (I1 w)⁻¹) 32 P)
    (hV16 : MemLp V 16 P) (σ : ℝ) (hσ : σ ≠ 0) (h : H)
    (hpair0 : ∀ᵐ w ∂P, inner ℝ (U w) h = σ*J1 w+I1 w)
    (hpair1 : ∀ᵐ w ∂P, inner ℝ (V w) h = σ*I2 w) :
    ∃ hv : MemLp (fun w => (J0 w/(σ*I1 w)) • h) 2 P,
    ∃ hz : MemLp (fun w => J0 w*W h w/(σ*I1 w)-J1 w/I1 w-1/σ+J0 w*I2 w/(I1 w)^2) 2 P,
      IsDivergence D (hv.toLp _) (hz.toLp _) := by
  have hdi := reciprocal_derivative_memLp P 8 16 32 I1 V hinv hV16
  obtain ⟨hv,hz,hd⟩ := quotient_direction_divergence P W S hS hcore 4 8 (by simp) (by simp)
    (by norm_num) D D4 D8 hD4 hD8 hg hg4 hg8 J0 I1 U V hJ0 hI1 hU hV h0 h1 hpos
    (hinv.mono_exponent (by norm_num)) hdi (1/σ) h
  have he : (fun w => ((1/σ)*J0 w/I1 w) • h) =ᵐ[P]
      (fun w => (J0 w/(σ*I1 w)) • h) := by
    filter_upwards [hpos] with w hw
    congr 1
    field_simp
  have hze : (fun w => ((1/σ)*J0 w/I1 w)*W h w-
      (1/σ)*(inner ℝ (U w) h/I1 w-J0 w*inner ℝ (V w) h/(I1 w)^2)) =ᵐ[P]
      (fun w => J0 w*W h w/(σ*I1 w)-J1 w/I1 w-1/σ+J0 w*I2 w/(I1 w)^2) := by
    filter_upwards [hpos,hpair0,hpair1] with w hw h0 h1
    rw [h0,h1]
    have he : (1/σ)*J0 w/I1 w = J0 w/(σ*I1 w) := by field_simp
    rw [he]
    exact asian_vega_weight σ (I1 w) (I2 w) (J0 w) (J1 w) (W h w) hσ hw.ne'
  have hv' := hv.ae_eq he
  have hz' := hz.ae_eq hze
  refine ⟨hv',hz',?_⟩
  have hve : hv.toLp _ = hv'.toLp _ := Lp.ext (hv.coeFn_toLp.trans (he.trans hv'.coeFn_toLp.symm))
  have hzz : hz.toLp _ = hz'.toLp _ := Lp.ext (hz.coeFn_toLp.trans (hze.trans hz'.coeFn_toLp.symm))
  rwa [←hve,←hzz]

end Asakura.Chapter12
