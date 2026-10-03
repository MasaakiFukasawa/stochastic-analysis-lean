import Chapter12AsianMomentGraphs
import Chapter12AsianCompactIntegrals
import Chapter12CallGraphRaw
import Chapter12RawGraphTransfer

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

theorem asian_call_payoff_graph {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [Nontrivial H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h ∈ S, HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (D : Lp ℝ 2 P →ₗ.[ℝ] Lp H 2 P) (hD : D.IsClosed)
    (hg : (D.graph : Set _) = closure (range (cylinderPair P W S hS hcore 2 (by simp))))
    (T : ℝ) (hT : 0<T) (X : Ω → C(Icc (0:ℝ) T,ℝ)) (hXm : Measurable X)
    (h : Icc (0:ℝ) T → H) (hh : Continuous h) (hb : ∀ t,‖h t‖≤Real.sqrt T)
    (hXW : ∀ t,(fun w => X w t) =ᵐ[P] (W (h t) : Ω → ℝ))
    (x σ r K : ℝ) (G : Ω → ℝ) (hG : MemLp G 2 P)
    (hSb : ∀ t,∀ᵐ w ∂P,‖stockPathValue x σ r T (X w) t‖≤‖G w‖)
    (hno : P {w | asianPathAverage x r T hT.le σ (X w)=K}=0) :
    ∃ hF : MemLp (fun w => Real.exp (-r*T)*max (asianPathAverage x r T hT.le σ (X w)-K) 0) 2 P,
    ∃ hDF : MemLp (fun w =>
      (Real.exp (-r*T)/T*(if K<asianPathAverage x r T hT.le σ (X w) then (1:ℝ) else 0)) •
        asianMomentGradient T hT.le x σ r 0 h (X w)) 2 P,
      (hF.toLp _,hDF.toLp _) ∈ D.graph := by
  let I := fun w => asianMoment T hT.le x σ r 0 (X w)
  let U := fun w => asianMomentGradient T hT.le x σ r 0 h (X w)
  let A := fun w => asianPathAverage x r T hT.le σ (X w)
  obtain ⟨hi,hui,hig⟩ := asian_moment_closed_graph P W S hS hcore 2 (by simp) le_rfl D hD hg
    T hT.le X hXm h hh hb hXW x σ r 0 G hG hSb
  obtain ⟨ha,hua,hag⟩ := scale_derivative_graph_raw P 2 D I U hi hui hig (1/T)
  have hav : (fun w => (1/T)*I w) =ᵐ[P] A := ae_of_all P fun w => by
    have he := compact_asian_average T hT (X w) x σ r
    simpa [I,A,asianMoment,div_eq_mul_inv,mul_comm] using he
  obtain ⟨hA,hUA,hAg⟩ := derivative_graph_raw_ae_transfer P 2 D _ A _ _ ha hua hag hav
    (Filter.EventuallyEq.rfl : (fun w => (1/T) • U w) =ᵐ[P] (fun w => (1/T) • U w))
  obtain ⟨hcall,hdcall,hcg⟩ := closed_call_graph_raw P W S hS hcore D hD hg A
    (fun w => (1/T) • U w) hA hUA hAg K hno
  obtain ⟨hpay,hdpay,hpg⟩ := scale_derivative_graph_raw P 2 D _ _ hcall hdcall hcg (Real.exp (-r*T))
  apply derivative_graph_raw_ae_transfer P 2 D _ _ _ _ hpay hdpay hpg Filter.EventuallyEq.rfl
  apply ae_of_all
  intro w
  simp only [smul_smul]
  congr 1
  dsimp only [A]
  ring

end Asakura.Chapter12
