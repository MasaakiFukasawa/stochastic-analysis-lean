import Chapter12AsianDeltaDivergence
import Chapter12CallGreekTransfer
import Chapter12LowerExponentRaw

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000

theorem asian_delta_call_transfer {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial H] [CompleteSpace H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h ∈ S, HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (D : Lp ℝ 2 P →ₗ.[ℝ] Lp H 2 P) (hD : D.IsClosed)
    (D4 : Lp ℝ 4 P →ₗ.[ℝ] Lp H 4 P) (D8 : Lp ℝ 8 P →ₗ.[ℝ] Lp H 8 P)
    (hD4 : D4.IsClosed) (hD8 : D8.IsClosed)
    (hg : (D.graph : Set _) = closure (range (cylinderPair P W S hS hcore 2 (by simp))))
    (hg4 : (D4.graph : Set _) = closure (range (cylinderPair P W S hS hcore 4 (by simp))))
    (hg8 : (D8.graph : Set _) = closure (range (cylinderPair P W S hS hcore 8 (by simp))))
    (I0 I1 I2 : Ω → ℝ) (U V : Ω → H)
    (hI0 : MemLp I0 8 P) (hI1 : MemLp I1 8 P) (hU : MemLp U 8 P) (hV : MemLp V 8 P)
    (h0 : (hI0.toLp _,hU.toLp _) ∈ D8.graph) (h1 : (hI1.toLp _,hV.toLp _) ∈ D8.graph)
    (hpos : ∀ᵐ w ∂P, 0 < I1 w) (hinv : MemLp (fun w => (I1 w)⁻¹) 32 P)
    (hV16 : MemLp V 16 P) (x σ : ℝ) (hx : x ≠ 0) (hσ : σ ≠ 0) (h : H)
    (hpair0 : ∀ᵐ w ∂P, inner ℝ (U w) h = σ*I1 w)
    (hpair1 : ∀ᵐ w ∂P, inner ℝ (V w) h = σ*I2 w)
    (T K : ℝ) (hno : P {w | I0 w/T = K} = 0) :
    (∫ w,(if K < I0 w/T then (1:ℝ) else 0)*(I0 w/(x*T)) ∂P) =
    ∫ w,max (I0 w/T-K) 0*((1/x)*(I0 w*W h w/(σ*I1 w)-1+I0 w*I2 w/(I1 w)^2)) ∂P := by
  obtain ⟨hv,hz,hd⟩ := asian_delta_divergence P W S hS hcore D D4 D8 hD4 hD8 hg hg4 hg8
    I0 I1 I2 U V hI0 hI1 hU hV h0 h1 hpos hinv hV16 x σ hx hσ h hpair0 hpair1
  have hlo := lower_exponent_graph_raw P W S hS hcore 2 8 (by norm_num) (by simp) (by simp)
    D D8 hg hg8 I0 U hI0 hU h0
  obtain ⟨hA,hDA,hAG⟩ := scale_derivative_graph_raw P 2 D I0 U
    (hI0.mono_exponent (by norm_num)) (hU.mono_exponent (by norm_num)) hlo (1/T)
  have he (w : Ω) : (1/T)*I0 w = I0 w/T := by ring
  have hno' : P {w | (1/T)*I0 w = K} = 0 := by simpa only [he] using hno
  have hdir : ∀ᵐ w ∂P, inner ℝ ((1/T) • U w) ((I0 w/(x*σ*I1 w)) • h) = I0 w/(x*T) := by
    filter_upwards [hpair0,hpos] with w hw hp
    rw [real_inner_smul_left,inner_smul_right,hw]
    have hh := asian_delta_direction x σ T (I0 w) (I1 w) hσ hp.ne'
    convert hh using 1 <;> ring
  have hh := call_greek_transfer P W S hS hcore D hD hg _ (fun w => I0 w/(x*T)) _ _ _
    hA hDA hAG hv hz hd hdir K hno'
  simpa only [he] using hh

end Asakura.Chapter12
