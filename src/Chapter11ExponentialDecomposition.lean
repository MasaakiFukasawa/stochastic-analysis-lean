import Chapter11ExponentialRegular
import Chapter2StochasticFubiniPrinted

open MeasureTheory Set Filter
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter6
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false

/-- The exponential has an actual semimartingale decomposition, with its
 stochastic integral identified and both finite-variation integrals exposed. -/
theorem exponential_decomposition_constructed
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (X A N C : ClosedTime T → Ω → ℝ) (hX : SemimartingaleDecomposition P F X A N)
    (hC : LocalCovarianceWitness P F N N C)
    (c : ℕ → ℝ) (hc : ∀ n,0<c n) (hcm : Monotone c) (hcT : ∀ n,(c n:EReal)<T)
    (hcc : ∀ t,t<⊤ → ∃ n,t<realTimeClamp (T:=T) (c n)) :
    ∃ B M I J : ClosedTime T → Ω → ℝ,
      SemimartingaleDecomposition P F (fun t w => Real.exp (X t w)) B M ∧
      ItoCovarianceFormula P F N (fun z => Real.exp (X (realTimeClamp z.2) z.1)) M ∧
      VariationIntegralFormula P c (fun n => (hc n).le) A
        (fun z => Real.exp (X (realTimeClamp z.2) z.1)) I ∧
      VariationIntegralFormula P c (fun n => (hc n).le) C
        (fun z => Real.exp (X (realTimeClamp z.2) z.1)) J ∧
      (∀ t w,B t w=Real.exp (X ⊥ w)+I t w+J t w/2) := by
  obtain ⟨I,J,L,hIv,hJv,hL,hI,hJ,hLI,hIc,hJc,he⟩ :=
    exponential_semimartingale_regular_constructed P hT F hF hle hnull X A N C hX hC c hc hcm hcT hcc
  have hXa t (ht : t<⊤) : Measurable[F t] (X t) := by
    have hh : X t=fun w => A t w+N t w := funext (hX.decomposition t ht)
    rw [hh]
    exact (hX.variation.adapted t ht).add (hX.martingale.adapted P F t ht)
  have hEa t ht := (hXa t ht).exp
  have hEc w t ht : ContinuousAt (fun s => Real.exp (X s w)) t :=
    Real.continuous_exp.continuousAt.comp (hX.continuous w t ht)
  have hconst := continuous_increasing_adapted_variation hT F hF (fun _ w => Real.exp (X ⊥ w))
    (fun _ _ => (hEa ⊥ hT).mono (hF bot_le) le_rfl) (fun _ => monotoneOn_const)
    (fun _ _ _ => continuousAt_const)
  let B := fun t w => Real.exp (X ⊥ w)+I t w+J t w/2
  have hB : AdaptedLocalVariationWitness F B := by
    convert (hconst.add hIv hF).add (hJv.smul (1/2)) hF using 1
    funext t w
    dsimp only [B]
    ring
  have hBc w t ht : ContinuousAt (fun s => B s w) t :=
    (continuousAt_const.add (hIc w t ht)).add ((hJc w t ht).div_const 2)
  have hdec : ∀ᵐ w ∂P,∀ t,t<⊤ → Real.exp (X t w)=B t w+L t w := by
    filter_upwards [he] with w hw
    intro t ht
    dsimp only [B]
    linarith [hw t ht]
  obtain ⟨hs,hm⟩ := semimartingale_of_ae_decomposition P F hF
    (fun t w => Real.exp (X t w)) B L hEa hEc hB hBc hL hdec
  refine ⟨B,_,I,J,hs,?_,hI,hJ,fun _ _ => rfl⟩
  exact hLI.congr_integral P F hF hle N L _ _ hL hs.martingale hm

end Asakura.Chapter11
