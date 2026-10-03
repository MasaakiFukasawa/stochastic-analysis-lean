import Chapter6ExponentialLocal

open MeasureTheory Set Filter
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter6
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- The actual exponential Ito formula, with both variation integrals and
the martingale integral constructed. This is used for exponential wealth
and, after a linear change of its logarithm, for the power value function. -/
theorem exponential_semimartingale_constructed {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t N,MeasurableSet[m] N → P N=0 → MeasurableSet[F t] N)
    (X A N C : ClosedTime T → Ω → ℝ) (hX : SemimartingaleDecomposition P F X A N)
    (hC : LocalCovarianceWitness P F N N C)
    (c : ℕ → ℝ) (hc : ∀ n,0<c n) (hcm : Monotone c) (hcT : ∀ n,(c n:EReal)<T)
    (hcc : ∀ t,t<⊤ → ∃ n,t<realTimeClamp (T:=T) (c n)) :
    ∃ I J L : ClosedTime T → Ω → ℝ,
      AdaptedLocalVariationWitness F I ∧ AdaptedLocalVariationWitness F J ∧
      LocalMProcessWitness P F L ∧
      VariationIntegralFormula P c (fun n => (hc n).le) A
        (fun z => Real.exp (X (realTimeClamp z.2) z.1)) I ∧
      VariationIntegralFormula P c (fun n => (hc n).le) C
        (fun z => Real.exp (X (realTimeClamp z.2) z.1)) J ∧
      ItoCovarianceFormula P F N (fun z => Real.exp (X (realTimeClamp z.2) z.1)) L ∧
      ∀ᵐ w ∂P,∀ t,t<⊤ → Real.exp (X t w)=Real.exp (X ⊥ w)+I t w+L t w+J t w/2 := by
  have hXa t (ht : t<⊤) : Measurable[F t] (X t) := by
    have he : X t=fun w => A t w+N t w := funext (hX.decomposition t ht)
    rw [he]
    exact (hX.variation.adapted t ht).add (hX.martingale.adapted P F t ht)
  have hr := open_process_real_regularity F (fun t w => Real.exp (X t w))
    (fun t ht => (hXa t ht).exp) (fun w t ht => Real.continuous_exp.continuousAt.comp (hX.continuous w t ht))
  obtain ⟨I,hIv,hIc,hI⟩ := continuous_adapted_variation_exists P F hF hnull c (fun n => (hc n).le)
    hcm hcT hcc A hX.variation (hX.variation_continuous P F) (fun z => Real.exp (X (realTimeClamp z.2) z.1)) hr.1 hr.2
  have hCv := covariance_adapted_variation P F hF hle hX.martingale hX.martingale hC
  have hCc w t (ht : t<⊤) : ContinuousAt (fun s => C s w) t := by
    have hh := ((hX.martingale.path P F w t ht).mul (hX.martingale.path P F w t ht)).sub (hC.defect.path P F w t ht)
    convert hh using 1
    funext s
    dsimp only [Pi.sub_apply,Pi.mul_apply]
    ring
  obtain ⟨J,hJv,hJc,hJ⟩ := continuous_adapted_variation_exists P F hF hnull c (fun n => (hc n).le)
    hcm hcT hcc C hCv hCc (fun z => Real.exp (X (realTimeClamp z.2) z.1)) hr.1 hr.2
  obtain ⟨L,hL,hLI⟩ := continuous_adapted_ito_exists P hT F hF hle hnull N hX.martingale (fun z => Real.exp (X (realTimeClamp z.2) z.1)) hr.1 hr.2
  have hIL : SemimartingaleDecomposition P F (fun t w => I t w+L t w) I L :=
    ⟨hIv,hL,fun w t ht => (hIc w t ht).add (hL.path P F w t ht),fun _ _ _ => rfl⟩
  have hh := scalar_ito_formula P hT F hF hle hnull X A N C (fun t w => I t w+L t w) J hX hC
    Real.exp Real.contDiff_exp c (fun n => (hc n).le) hcT hcc
    (by simpa only [Real.deriv_exp] using (show SemimartingaleIntegralFormula P F c (fun n => (hc n).le) A N
      (fun z => Real.exp (X (realTimeClamp z.2) z.1)) (fun t w => I t w+L t w) from ⟨I,L,hIL,hI,hLI⟩))
    (by simpa only [iteratedDeriv_eq_iterate,Real.iter_deriv_exp] using hJ)
  refine ⟨I,J,L,hIv,hJv,hL,hI,hJ,hLI,?_⟩
  filter_upwards [hh] with w hw
  intro t ht
  have ht' := hw t ht
  linarith

end Asakura.Chapter11
