import Chapter12AsianVegaTransfer
import Chapter12AsianVegaMoments
import Chapter12AsianMomentGradientMoments
import Chapter12AsianCompactIntegrals

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000

/-- The vega transfer formula for the actual time moments of the stock.
No Sobolev membership or derivative formula for those moments is assumed. -/
private instance vegaTimeFact16 : Fact (1 ≤ (16:ℝ≥0∞)) := ⟨by norm_num⟩

theorem asian_vega_time_integrals {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h ∈ S, HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (D : Lp ℝ 2 P →ₗ.[ℝ] Lp H 2 P) (hD : D.IsClosed)
    (D4 : Lp ℝ 4 P →ₗ.[ℝ] Lp H 4 P) (D8 : Lp ℝ 8 P →ₗ.[ℝ] Lp H 8 P)
    (D16 : Lp ℝ 16 P →ₗ.[ℝ] Lp H 16 P)
    (hD4 : D4.IsClosed) (hD8 : D8.IsClosed) (hD16 : D16.IsClosed)
    (hg : (D.graph : Set _) = closure (range (cylinderPair P W S hS hcore 2 (by simp))))
    (hg4 : (D4.graph : Set _) = closure (range (cylinderPair P W S hS hcore 4 (by simp))))
    (hg8 : (D8.graph : Set _) = closure (range (cylinderPair P W S hS hcore 8 (by simp))))
    (hg16 : (D16.graph : Set _) = closure (range (cylinderPair P W S hS hcore 16 (by simp))))
    (T : ℝ) (hT : 0 < T) (X : Ω → C(Icc (0:ℝ) T,ℝ)) (hXm : Measurable X)
    (h : Icc (0:ℝ) T → H) (hh : Continuous h) (hb : ∀ t, ‖h t‖ ≤ Real.sqrt T)
    (hXW : ∀ t, (fun w => X w t) =ᵐ[P] (W (h t) : Ω → ℝ))
    (hTdir : H) (hpair : ∀ t, inner ℝ (h t) hTdir = t.val)
    (x σ r K : ℝ) (hx : 0 < x) (hσ : 0 < σ)
    (G : Ω → ℝ) (hG : MemLp G 16 P)
    (hSb : ∀ t, ∀ᵐ w ∂P, ‖stockPathValue x σ r T (X w) t‖ ≤ ‖G w‖)
    (GV : Ω → ℝ) (hGV : MemLp GV 8 P)
    (hVb : ∀ t, ∀ᵐ w ∂P, ‖stockPathValue x σ r T (X w) t*(X w t-σ*t.val)‖ ≤ ‖GV w‖)
    (hinv : MemLp (fun w => (asianFirstTimeMoment x σ r T hT.le (X w))⁻¹) 32 P)
    (hno : P {w | asianPathAverage x r T hT.le σ (X w) = K} = 0) :
    let I := fun j w => asianMoment T hT.le x σ r j (X w)
    let J := fun j w => asianVegaMoment T hT.le x σ r j (X w)
    (∫ w,(if K < I 0 w/T then (1:ℝ) else 0)*(J 0 w/T) ∂P) =
    ∫ w,max (I 0 w/T-K) 0*(J 0 w*W hTdir w/(σ*I 1 w)-J 1 w/I 1 w-1/σ+J 0 w*I 2 w/(I 1 w)^2) ∂P := by
  letI : Fact (1 ≤ (16:ℝ≥0∞)) := ⟨by norm_num⟩
  let I := fun j w => asianMoment T hT.le x σ r j (X w)
  let U := fun j w => asianMomentGradient T hT.le x σ r j h (X w)
  have hi (j) := asian_moment_closed_graph P W S hS hcore 8 (by simp) (by norm_num) D8 hD8 hg8
    T hT.le X hXm h hh hb hXW x σ r j G (hG.mono_exponent (by norm_num)) hSb
  obtain ⟨hI0,hU0,h0⟩ := hi 0
  obtain ⟨hI1,hU1,h1⟩ := hi 1
  have hU16 := asian_moment_gradient_memLp P 16 (by simp) (by norm_num) T hT.le X hXm h hh
    x σ r 1 G hG hSb
  have hIe (w : Ω) : I 1 w = asianFirstTimeMoment x σ r T hT.le (X w) := by
    unfold I asianMoment
    rw [compact_asian_moment]
    unfold asianFirstTimeMoment
    simp only [pow_one,mul_assoc]
  have hpos : ∀ᵐ w ∂P, 0 < I 1 w := ae_of_all P fun w => by
    rw [hIe]
    exact asian_first_time_moment_pos x σ r T hx hT (X w)
  have hinv' : MemLp (fun w => (I 1 w)⁻¹) 32 P := by simpa only [hIe] using hinv
  have havg (w : Ω) : I 0 w/T = asianPathAverage x r T hT.le σ (X w) := by
    simpa only [I,asianMoment,pow_zero,one_mul] using compact_asian_average T hT (X w) x σ r
  have hn : P {w | I 0 w/T = K} = 0 := by simpa only [havg] using hno
  have hp (j) : ∀ᵐ w ∂P, inner ℝ (U j w) hTdir = σ*I (j+1) w :=
    ae_of_all P fun w => asian_moment_pairing T hT.le x σ r j h hh hTdir hpair (X w)
  let J := fun j w => asianVegaMoment T hT.le x σ r j (X w)
  let VJ := fun w => asianVegaGradient T hT.le x σ r h (X w)
  have hj := asian_vega_integral_graph P W S hS hcore 8 16 (by simp) (by simp) (by norm_num)
    D8 D16 hD8 hD16 hg8 hg16 T (compactTimeMeasure T hT.le) X hXm h hh hXW x σ r G GV
    (hG.mono_exponent (by norm_num)) hGV hSb hVb
  obtain ⟨hJ,hDJ,hJG⟩ : ∃ hJ : MemLp (J 0) 8 P, ∃ hDJ : MemLp VJ 8 P,
      (hJ.toLp _,hDJ.toLp _) ∈ D8.graph := by
    simpa only [J,VJ,asianVegaMoment,asianVegaGradient,pow_zero,one_mul] using hj
  have hpJ : ∀ᵐ w ∂P, inner ℝ (VJ w) hTdir = σ*J 1 w+I 1 w :=
    ae_of_all P fun w => asian_vega_moment_pairing T hT.le x σ r h hh hTdir hpair (X w)
  exact asian_vega_call_transfer P W S hS hcore D hD D4 D8 hD4 hD8 hg hg4 hg8
    (J 0) (J 1) (I 1) (I 2) VJ (U 1) hJ hI1 hDJ hU1 hJG h1 hpos hinv' hU16
    σ hσ.ne' hTdir hpJ (hp 1) (I 0) (U 0) hI0 hU0 h0 (hp 0) T K hn

end Asakura.Chapter12
