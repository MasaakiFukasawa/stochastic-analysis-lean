import Chapter12AsianVegaTimeIntegrals
import Chapter12AsianVegaEnvelopeTrim
import Chapter12AsianAtomlessTrim
import Chapter12AsianExchangeTrim
import Chapter12StockEnvelopeTrim
import Chapter12ProbabilityTrim

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

/-- Asian call vega on terminal information. The moments, atomlessness,
parameter exchange, Sobolev time-integrals and divergence weight are all
connected to the actual Brownian stock path. The derivative operators
are precisely the closures of the common Wiener cylinder graphs. -/
private instance vegaBrownianFact16 : Fact (1 ≤ (16:ℝ≥0∞)) := ⟨by norm_num⟩

theorem asian_call_vega_brownian {Ω H : Type*} [m : MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hc : ∀ w, Continuous (fun t => B t w)) (T : ℝ≥0) (hT : 0 < T)
    (mT : MeasurableSpace Ω) (hle : mT ≤ m)
    (X : Ω → C(Icc (0:ℝ) T,ℝ)) (hXm : Measurable[mT] X)
    (he : ∀ w (s : Icc (0:ℝ) T), X w s = B ⟨s.val,s.property.1⟩ w)
    (x σ r K : ℝ) (hx : 0 < x) (hσ : 0 < σ) :
    letI := probability_trim P mT hle
    letI : MeasurableSpace Ω := mT
    ∀ (W : H →ₗᵢ[ℝ] Lp ℝ 2 (P.trim hle)) (S : Set H) (hS : Dense S)
    (hcore : ∀ h ∈ S, HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) (P.trim hle))
    (D : Lp ℝ 2 (P.trim hle) →ₗ.[ℝ] Lp H 2 (P.trim hle)) (hD : D.IsClosed)
    (D4 : Lp ℝ 4 (P.trim hle) →ₗ.[ℝ] Lp H 4 (P.trim hle))
    (D8 : Lp ℝ 8 (P.trim hle) →ₗ.[ℝ] Lp H 8 (P.trim hle))
    (D16 : Lp ℝ 16 (P.trim hle) →ₗ.[ℝ] Lp H 16 (P.trim hle))
    (hD4 : D4.IsClosed) (hD8 : D8.IsClosed) (hD16 : D16.IsClosed),
    (D.graph : Set _) = closure (range (cylinderPair (P.trim hle) W S hS hcore 2 (by simp))) →
    (D4.graph : Set _) = closure (range (cylinderPair (P.trim hle) W S hS hcore 4 (by simp))) →
    (D8.graph : Set _) = closure (range (cylinderPair (P.trim hle) W S hS hcore 8 (by simp))) →
    (D16.graph : Set _) = closure (range (cylinderPair (P.trim hle) W S hS hcore 16 (by simp))) →
    ∀ (h : Icc (0:ℝ) T → H), Continuous h → (∀ t, ‖h t‖ ≤ Real.sqrt T) →
    (∀ t, (fun w => X w t) =ᵐ[P.trim hle] (W (h t) : Ω → ℝ)) →
    (∀ t, inner ℝ (h t) (h ⟨T,T.property,le_rfl⟩) = t.val) →
    let I := fun j w => asianMoment T T.property x σ r j (X w)
    let J := fun j w => asianVegaMoment T T.property x σ r j (X w)
    HasDerivAt (fun a => ∫ w,max (asianPathAverage x r T T.property a (X w)-K) 0 ∂P.trim hle)
      (∫ w,max (I 0 w/T-K) 0*(J 0 w*B T w/(σ*I 1 w)-J 1 w/I 1 w-1/σ+J 0 w*I 2 w/(I 1 w)^2) ∂P.trim hle) σ := by
  letI : MeasurableSpace Ω := m
  obtain ⟨G,hG,hGb,_⟩ := stock_path_envelope_on_trim P mT hle B hB hm hc T X hXm he x σ r 16 (by simp)
  obtain ⟨GV,hGV,hGVb⟩ := asian_vega_envelope_on_trim P B hB hm hc T mT hle X hXm he x σ r 8 (by simp)
  have hinv := asian_inverse_moments_on_trim P B hB hm hc T hT mT hle X hXm he x σ r hx 32 (by simp)
  have hno := asian_average_no_atom_on_trim P B hB hm hc T hT mT hle X hXm he x σ r K hx hσ
  have hd := asian_vega_exchange_on_trim P B hB hm hc T hT mT hle X hXm he x r σ K hx hσ
  letI := probability_trim P mT hle
  letI : MeasurableSpace Ω := mT
  intro W S hS hcore D hD D4 D8 D16 hD4 hD8 hD16 hg hg4 hg8 hg16 h hh hb hXW hpair
  let I := fun j w => asianMoment T T.property x σ r j (X w)
  let J := fun j w => asianVegaMoment T T.property x σ r j (X w)
  have ht : (0:ℝ) < T := hT
  have hh' := asian_vega_time_integrals (P.trim hle) W S hS hcore D hD D4 D8 D16 hD4 hD8 hD16 hg hg4 hg8 hg16
    T ht X hXm h hh hb hXW (h ⟨T,T.property,le_rfl⟩) hpair x σ r K hx hσ G hG
    (fun t => ae_of_all (P.trim hle) (hGb t)) GV hGV (fun t => ae_of_all (P.trim hle) (hGVb t)) hinv hno
  have havg (w : Ω) : I 0 w/T = asianPathAverage x r T T.property σ (X w) := by
    simpa only [I,asianMoment,pow_zero,one_mul] using compact_asian_average T ht (X w) x σ r
  have hvg (w : Ω) : J 0 w/T = asianPathVega x r T T.property σ (X w) := by
    have he' := compact_asian_vega_moment T T.property (X w) x σ r 0
    simp only [pow_zero,one_mul] at he'
    unfold J asianVegaMoment asianPathVega
    simp only [pow_zero,one_mul,he']
  have hleft : (∫ w,(if K < I 0 w/T then (1:ℝ) else 0)*(J 0 w/T) ∂P.trim hle) =
      ∫ w,(if K < asianPathAverage x r T T.property σ (X w) then 1 else 0)*
      asianPathVega x r T T.property σ (X w) ∂P.trim hle := by
    apply integral_congr_ae
    apply ae_of_all
    intro w
    dsimp only
    rw [havg,hvg]
  have hright : (∫ w,max (I 0 w/T-K) 0*(J 0 w*W (h ⟨T,T.property,le_rfl⟩) w/(σ*I 1 w)-
      J 1 w/I 1 w-1/σ+J 0 w*I 2 w/(I 1 w)^2) ∂P.trim hle) =
      ∫ w,max (I 0 w/T-K) 0*(J 0 w*B T w/(σ*I 1 w)-J 1 w/I 1 w-1/σ+J 0 w*I 2 w/(I 1 w)^2) ∂P.trim hle := by
    apply integral_congr_ae
    filter_upwards [hXW ⟨T,T.property,le_rfl⟩] with w hw
    have hw' : W (h ⟨T,T.property,le_rfl⟩) w = B T w := hw.symm.trans (he w ⟨T,T.property,le_rfl⟩)
    rw [hw']
  exact hd.congr_deriv (hleft.symm.trans (hh'.trans hright))

end Asakura.Chapter12
