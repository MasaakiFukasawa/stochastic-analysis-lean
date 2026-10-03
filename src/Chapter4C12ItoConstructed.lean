import Chapter4C12Ito
import Chapter3ContinuousIntegralConstruction

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 3800000
set_option backward.isDefEq.respectTransparency false

/-- Construct every integral in the C1,2 time-space formula from the
semimartingales and the continuous derivatives. -/
theorem c12_time_space_ito_constructed
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T) {d : ℕ}
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (U : ClosedTime T → Ω → ℝ)
    (hU : SemimartingaleDecomposition P F U U (fun _ _ => 0))
    (hUmn : ∀ w,Monotone (fun t => U t w)) (hUn : ∀ w t,0≤U t w)
    (X A M : Fin d → ClosedTime T → Ω → ℝ)
    (C : Fin d → Fin d → ClosedTime T → Ω → ℝ)
    (hX : ∀ i,SemimartingaleDecomposition P F (X i) (A i) (M i))
    (hC : ∀ i j,LocalCovarianceWitness P F (M i) (M j) (C i j))
    (f : ℝ → (Fin d → ℝ) → ℝ) (ft : ℝ × (Fin d → ℝ) → ℝ)
    (hf : ∀ a,ContDiff ℝ 2 (f a))
    (hft : ∀ a x,HasDerivAt (fun s => f s x) (ft (a,x)) a) (hftc : Continuous ft)
    (hdxc : Continuous (fun z : ℝ × (Fin d → ℝ) => fderiv ℝ (f z.1) z.2))
    (hhc : Continuous (fun z : ℝ × (Fin d → ℝ) => fderiv ℝ (fderiv ℝ (f z.1)) z.2))
    (c : ℕ → ℝ) (hc : ∀ n,0≤c n) (hcm : Monotone c) (hcT : ∀ n,(c n:EReal)<T)
    (hcc : ∀ t,t<⊤ → ∃ n,t<realTimeClamp (T := T) (c n)) :
    ∃ Z0,∃ Z : Fin d → ClosedTime T → Ω → ℝ,∃ J : Fin d → Fin d → ClosedTime T → Ω → ℝ,
      SemimartingaleIntegralFormula P F c hc U (fun _ _ => 0)
        (fun z => ft (U (realTimeClamp z.2) z.1,fun i => X i (realTimeClamp z.2) z.1)) Z0 ∧
      (∀ i,SemimartingaleIntegralFormula P F c hc (A i) (M i)
        (fun z => fderiv ℝ (f (U (realTimeClamp z.2) z.1)) (fun k => X k (realTimeClamp z.2) z.1) (Pi.single i 1)) (Z i)) ∧
      (∀ i j,VariationIntegralFormula P c hc (C i j)
        (fun z => fderiv ℝ (fderiv ℝ (f (U (realTimeClamp z.2) z.1))) (fun k => X k (realTimeClamp z.2) z.1)
          (Pi.single i 1) (Pi.single j 1)) (J i j)) ∧
      ∀ᵐ w ∂P,∀ t,t<⊤ → f (U t w) (fun i => X i t w)=f (U ⊥ w) (fun i => X i ⊥ w)+
        Z0 t w+(∑ i,Z i t w)+(∑ i,∑ j,J i j t w)/2 := by
  classical
  let W := fun t w i => X i t w
  have hXm i t (ht : t < ⊤) : Measurable[F t] (X i t) := by
    have he := funext ((hX i).decomposition t ht)
    rw [he]
    exact ((hX i).variation.adapted t ht).add ((hX i).martingale.adapted P F t ht)
  have hWm t (ht : t < ⊤) : Measurable[F t] (W t) := by
    letI : MeasurableSpace Ω := F t
    exact Measurable.of_eval fun i => hXm i t ht
  have hWc w t (ht : t < ⊤) : ContinuousAt (fun s => W s w) t :=
    continuousAt_pi.mpr fun i => (hX i).continuous w t ht
  let D0 := fun t w => ft (U t w,W t w)
  let D := fun i t w => fderiv ℝ (f (U t w)) (W t w) (Pi.single i 1)
  let E := fun i j t w => fderiv ℝ (fderiv ℝ (f (U t w))) (W t w) (Pi.single i 1) (Pi.single j 1)
  have hVWm t (ht : t<⊤) : Measurable[F t] (fun w => (U t w,W t w)) :=
    (hU.variation.adapted t ht).prodMk (hWm t ht)
  have hVWc w t (ht : t<⊤) := (hU.continuous w t ht).prodMk (hWc w t ht)
  have hDm i t (ht : t<⊤) : Measurable[F t] (D i t) :=
    (hdxc.clm_apply continuous_const).measurable.comp (hVWm t ht)
  have hDc i w t (ht : t<⊤) : ContinuousAt (fun s => D i s w) t :=
    (hdxc.clm_apply continuous_const).continuousAt.comp (hVWc w t ht)
  have hEm i j t (ht : t<⊤) : Measurable[F t] (E i j t) :=
    ((hhc.clm_apply continuous_const).clm_apply continuous_const).measurable.comp (hVWm t ht)
  have hEc i j w t (ht : t<⊤) : ContinuousAt (fun s => E i j s w) t :=
    ((hhc.clm_apply continuous_const).clm_apply continuous_const).continuousAt.comp (hVWc w t ht)
  have hD0m t (ht : t<⊤) : Measurable[F t] (D0 t) := hftc.measurable.comp (hVWm t ht)
  have hD0c w t (ht : t<⊤) : ContinuousAt (fun s => D0 s w) t := hftc.continuousAt.comp (hVWc w t ht)
  have hz i : ∃ Z, SemimartingaleIntegralFormula P F c hc (A i) (M i)
      (fun z => D i (realTimeClamp z.2) z.1) Z := by
    obtain ⟨I,N,hIN,hI,hN⟩ := continuous_semimartingale_integral_exists
      P hT F hF hle hnull (X i) (A i) (M i) (D i) (hX i) (hDm i) (hDc i) c hc hcm hcT hcc
    exact ⟨fun t w => I t w+N t w,I,N,hIN,hI,hN⟩
  have hj i j : ∃ J, VariationIntegralFormula P c hc (C i j)
      (fun z => E i j (realTimeClamp z.2) z.1) J := by
    have hCv := covariance_adapted_variation P F hF hle (hX i).martingale (hX j).martingale (hC i j)
    have hCc w t (ht : t < ⊤) : ContinuousAt (fun s => C i j s w) t := by
      have hh := (((hX i).martingale.path P F w t ht).mul
        ((hX j).martingale.path P F w t ht)).sub ((hC i j).defect.path P F w t ht)
      convert hh using 1
      funext s
      simp only [Pi.sub_apply,Pi.mul_apply,sub_sub_cancel]
    obtain ⟨J,_,_,hJ⟩ := continuous_adapted_variation_exists P F hF hnull c hc hcm hcT hcc
      (C i j) hCv hCc (fun z => E i j (realTimeClamp z.2) z.1)
      (open_process_real_regularity F (E i j) (hEm i j) (hEc i j)).1
      (open_process_real_regularity F (E i j) (hEm i j) (hEc i j)).2
    exact ⟨J,hJ⟩
  choose Z hZ using hz
  choose J hJ using hj
  obtain ⟨I0,N0,hIN0,hI0,hN0⟩ := continuous_semimartingale_integral_exists P hT F hF hle hnull
    U U (fun _ _ => 0) D0 hU hD0m hD0c c hc hcm hcT hcc
  let Z0 := fun t w => I0 t w+N0 t w
  have hZ0 : SemimartingaleIntegralFormula P F c hc U (fun _ _ => 0)
      (fun z => D0 (realTimeClamp z.2) z.1) Z0 := ⟨I0,N0,hIN0,hI0,hN0⟩
  exact ⟨Z0,Z,J,hZ0,hZ,hJ,c12_time_space_ito_formula P hT F hF hle hnull U Z0 hU hUmn hUn
    X A M Z C J hX hC f ft hf hft hftc hdxc hhc c hc hcT hcc hZ0 hZ hJ⟩

end Asakura.Chapter4
