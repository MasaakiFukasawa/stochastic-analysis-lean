import Chapter12AsianDeltaBrownian
import Chapter12AsianVegaBrownian
import Chapter12GreekSobolevOperators

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

theorem asian_call_delta_from_wiener_data {Ω H : Type*} [m : MeasurableSpace Ω]
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
    (hcore : ∀ h ∈ S, HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) (P.trim hle)),
    ∀ (h : Icc (0:ℝ) T → H), Continuous h → (∀ t, ‖h t‖ ≤ Real.sqrt T) →
    (∀ t, (fun w => X w t) =ᵐ[P.trim hle] (W (h t) : Ω → ℝ)) →
    (∀ t, inner ℝ (h t) (h ⟨T,T.property,le_rfl⟩) = t.val) →
    (∀ q : ℝ≥0∞, ∀ f : Lp ℝ q (P.trim hle),
      AEStronglyMeasurable[MeasurableSpace.comap (fun w t => X w t) inferInstance] f (P.trim hle)) →
    let I := fun j w => asianMoment T T.property x σ r j (X w)
    HasDerivAt (fun a => Real.exp (-r*T) * ∫ w,max (asianPathAverage a r T T.property σ (X w)-K) 0 ∂P.trim hle)
      (Real.exp (-r*T) * ∫ w,max (I 0 w/T-K) 0*((1/x)*(I 0 w*B T w/(σ*I 1 w)-1+I 0 w*I 2 w/(I 1 w)^2)) ∂P.trim hle) x := by
  letI : MeasurableSpace Ω := m
  have hmain := asian_call_delta_brownian (H := H) P B hB hm hc T hT mT hle X hXm he x σ r K hx hσ
  letI := probability_trim P mT hle
  letI : MeasurableSpace Ω := mT
  intro W S hS hcore h hh hb hXW hpair hgen
  letI : Nonempty (Icc (0:ℝ) T) := ⟨⟨0,le_rfl,T.property⟩⟩
  obtain ⟨times,htimes⟩ := TopologicalSpace.exists_dense_seq (α := Icc (0:ℝ) T)
  have hXm' (t : Icc (0:ℝ) T) : Measurable (fun w => X w t) :=
    (continuous_eval_const t).measurable.comp hXm
  obtain ⟨D2,D4,D8,D16,hd2,hd4,hd8,hd16,hg2,hg4,hg8,hg16⟩ :=
    greek_sobolev_operators (P.trim hle) W S hS hcore (fun t w => X w t) hXm'
      (fun w => (X w).continuous) h hXW times htimes hgen
  have hd := hmain W S hS hcore D2 hd2 D4 D8 hd4 hd8 hg2 hg4 hg8 h hh hb hXW hpair
  exact hd.const_mul (Real.exp (-r*T))

theorem asian_call_vega_from_wiener_data {Ω H : Type*} [m : MeasurableSpace Ω]
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
    (hcore : ∀ h ∈ S, HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) (P.trim hle)),
    ∀ (h : Icc (0:ℝ) T → H), Continuous h → (∀ t, ‖h t‖ ≤ Real.sqrt T) →
    (∀ t, (fun w => X w t) =ᵐ[P.trim hle] (W (h t) : Ω → ℝ)) →
    (∀ t, inner ℝ (h t) (h ⟨T,T.property,le_rfl⟩) = t.val) →
    (∀ q : ℝ≥0∞, ∀ f : Lp ℝ q (P.trim hle),
      AEStronglyMeasurable[MeasurableSpace.comap (fun w t => X w t) inferInstance] f (P.trim hle)) →
    let I := fun j w => asianMoment T T.property x σ r j (X w)
    let J := fun j w => asianVegaMoment T T.property x σ r j (X w)
    HasDerivAt (fun a => Real.exp (-r*T) * ∫ w,max (asianPathAverage x r T T.property a (X w)-K) 0 ∂P.trim hle)
      (Real.exp (-r*T) * ∫ w,max (I 0 w/T-K) 0*(J 0 w*B T w/(σ*I 1 w)-J 1 w/I 1 w-1/σ+J 0 w*I 2 w/(I 1 w)^2) ∂P.trim hle) σ := by
  letI : MeasurableSpace Ω := m
  have hmain := asian_call_vega_brownian (H := H) P B hB hm hc T hT mT hle X hXm he x σ r K hx hσ
  letI := probability_trim P mT hle
  letI : MeasurableSpace Ω := mT
  intro W S hS hcore h hh hb hXW hpair hgen
  letI : Nonempty (Icc (0:ℝ) T) := ⟨⟨0,le_rfl,T.property⟩⟩
  obtain ⟨times,htimes⟩ := TopologicalSpace.exists_dense_seq (α := Icc (0:ℝ) T)
  have hXm' (t : Icc (0:ℝ) T) : Measurable (fun w => X w t) :=
    (continuous_eval_const t).measurable.comp hXm
  obtain ⟨D2,D4,D8,D16,hd2,hd4,hd8,hd16,hg2,hg4,hg8,hg16⟩ :=
    greek_sobolev_operators (P.trim hle) W S hS hcore (fun t w => X w t) hXm'
      (fun w => (X w).continuous) h hXW times htimes hgen
  have hd := hmain W S hS hcore D2 hd2 D4 D8 D16 hd4 hd8 hd16 hg2 hg4 hg8 hg16 h hh hb hXW hpair
  exact hd.const_mul (Real.exp (-r*T))

end Asakura.Chapter12
