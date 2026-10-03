import Chapter12AsianDeltaTimeIntegrals
import Chapter12AsianAtomlessTrim
import Chapter12AsianExchangeTrim
import Chapter12StockEnvelopeTrim
import Chapter12ProbabilityTrim

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

/-- Asian call delta on terminal information. The moments, atomlessness,
parameter exchange, Sobolev time-integrals and divergence weight are all
connected to the actual Brownian stock path. The derivative operators
are precisely the closures of the common Wiener cylinder graphs. -/
theorem asian_call_delta_brownian {Ω H : Type*} [m : MeasurableSpace Ω]
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
    (hD4 : D4.IsClosed) (hD8 : D8.IsClosed),
    (D.graph : Set _) = closure (range (cylinderPair (P.trim hle) W S hS hcore 2 (by simp))) →
    (D4.graph : Set _) = closure (range (cylinderPair (P.trim hle) W S hS hcore 4 (by simp))) →
    (D8.graph : Set _) = closure (range (cylinderPair (P.trim hle) W S hS hcore 8 (by simp))) →
    ∀ (h : Icc (0:ℝ) T → H), Continuous h → (∀ t, ‖h t‖ ≤ Real.sqrt T) →
    (∀ t, (fun w => X w t) =ᵐ[P.trim hle] (W (h t) : Ω → ℝ)) →
    (∀ t, inner ℝ (h t) (h ⟨T,T.property,le_rfl⟩) = t.val) →
    let I := fun j w => asianMoment T T.property x σ r j (X w)
    HasDerivAt (fun a => ∫ w,max (asianPathAverage a r T T.property σ (X w)-K) 0 ∂P.trim hle)
      (∫ w,max (I 0 w/T-K) 0*((1/x)*(I 0 w*B T w/(σ*I 1 w)-1+I 0 w*I 2 w/(I 1 w)^2)) ∂P.trim hle) x := by
  letI : MeasurableSpace Ω := m
  obtain ⟨G,hG,hGb,_⟩ := stock_path_envelope_on_trim P mT hle B hB hm hc T X hXm he x σ r 16 (by simp)
  have hinv := asian_inverse_moments_on_trim P B hB hm hc T hT mT hle X hXm he x σ r hx 32 (by simp)
  have hno := asian_average_no_atom_on_trim P B hB hm hc T hT mT hle X hXm he x σ r K hx hσ
  have hd := asian_delta_exchange_on_trim P B hB hm hc T hT mT hle X hXm he x r σ K hx hσ
  letI := probability_trim P mT hle
  letI : MeasurableSpace Ω := mT
  intro W S hS hcore D hD D4 D8 hD4 hD8 hg hg4 hg8 h hh hb hXW hpair
  let I := fun j w => asianMoment T T.property x σ r j (X w)
  have ht : (0:ℝ) < T := hT
  have hh' := asian_delta_time_integrals (P.trim hle) W S hS hcore D hD D4 D8 hD4 hD8 hg hg4 hg8
    T ht X hXm h hh hb hXW (h ⟨T,T.property,le_rfl⟩) hpair x σ r K hx hσ G hG
    (fun t => ae_of_all (P.trim hle) (hGb t)) hinv hno
  have havg (w : Ω) : I 0 w/T = asianPathAverage x r T T.property σ (X w) := by
    simpa only [I,asianMoment,pow_zero,one_mul] using compact_asian_average T ht (X w) x σ r
  have hleft : (∫ w,(if K < I 0 w/T then (1:ℝ) else 0)*(I 0 w/(x*T)) ∂P.trim hle) =
      ∫ w,(if K < asianPathAverage x r T T.property σ (X w) then 1 else 0)*
      (asianPathAverage x r T T.property σ (X w)/x) ∂P.trim hle := by
    apply integral_congr_ae
    apply ae_of_all
    intro w
    dsimp only
    rw [show I 0 w/(x*T) = (I 0 w/T)/x by ring,havg]
  have hright : (∫ w,max (I 0 w/T-K) 0*((1/x)*(I 0 w*W (h ⟨T,T.property,le_rfl⟩) w/(σ*I 1 w)-1+
      I 0 w*I 2 w/(I 1 w)^2)) ∂P.trim hle) =
      ∫ w,max (I 0 w/T-K) 0*((1/x)*(I 0 w*B T w/(σ*I 1 w)-1+I 0 w*I 2 w/(I 1 w)^2)) ∂P.trim hle := by
    apply integral_congr_ae
    filter_upwards [hXW ⟨T,T.property,le_rfl⟩] with w hw
    have hw' : W (h ⟨T,T.property,le_rfl⟩) w = B T w := hw.symm.trans (he w ⟨T,T.property,le_rfl⟩)
    rw [hw']
  exact hd.congr_deriv (hleft.symm.trans (hh'.trans hright))

end Asakura.Chapter12
