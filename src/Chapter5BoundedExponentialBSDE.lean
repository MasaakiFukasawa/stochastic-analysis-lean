import Chapter5NaturalTerminalRepresentation
import Chapter5ExponentialMartingaleBounds
import Chapter5LogarithmicBSDE
import Chapter5ClockSemimartingale

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 5500000
set_option backward.isDefEq.respectTransparency false

/-- The bounded exponential terminal payoff is actually represented,
its positive conditional process is constructed, and logarithmic Ito
calculus produces the quadratic BSDE used in the Burgers example. -/
theorem bounded_exponential_bsde_constructed
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t N,MeasurableSet[m] N → P N=0 → MeasurableSet[F t] N)
    (W A : ClosedTime T → Ω → ℝ)
    (hW : LocalMProcessWitness P F W)
    (hA : LocalCovarianceWitness P F W W A)
    (hclock : ∀ w (r : ℝ),0≤r → (r:EReal)<T → A (realTimeClamp r) w=r)
    (c : ℕ → ℝ) (hc : ∀ j,0<c j) (hcm : StrictMono c) (hcT : ∀ j,(c j:EReal)<T)
    (hct : StrictMono (fun j => realTimeClamp (T := T) (c j)))
    (hcut : ∀ j,realTimeClamp (T := T) (c j)<⊤)
    (hcc : ∀ t,t<⊤ → ∃ j,t<realTimeClamp (T := T) (c j))
    (hco : ∀ r,∃ j,r≤c j)
    (R : ℝ) (hR : 0≤R) (hRT : (R:EReal)<T)
    (hFnat : F (realTimeClamp R)=Asakura.nullAugmentation (m := m) P (pastSigma W (realTimeClamp R)))
    (V : Ω → ℝ) (hV : Measurable[F (realTimeClamp R)] V)
    (f : ℝ → ℝ) (hfm : Measurable f) (B a : ℝ) (ha : a≠0) (hf : ∀ x,|f x|≤B) :
    ∃ X : ClosedTime T → Ω → ℝ,∃ Z : Ω × ℝ → ℝ,∃ N : ClosedTime T → Ω → ℝ,
      LocalMProcessWitness P F N ∧ ItoCovarianceFormula P F W Z N ∧
      (∀ t,X t =ᵐ[P] P[(fun w => Real.exp (a*f (V w)))|F t]) ∧
      (∀ᵐ w ∂P,∀ t,Real.exp (-|a| * B)≤X t w) ∧
      (∀ t∈Icc 0 R,(fun w => f (V w)) =ᵐ[P]
        fun w => Real.log (X (realTimeClamp t) w)/a-(∫ r in t..R,a/2*(Z (w,r))^2)+
          (N (realTimeClamp R) w-N (realTimeClamp t) w)) := by
  let U := fun w => Real.exp (a*f (V w))
  have hUm : Measurable[F (realTimeClamp R)] U := (measurable_const.mul (hfm.comp hV)).exp
  have hU : MemLp U 2 P := MemLp.of_bound ((hUm.mono (hle _) le_rfl).aestronglyMeasurable)
    (Real.exp (|a| * B)) (ae_of_all _ fun w => by
      simpa only [U,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using (exponential_payoff_bounds f B a hf (V w)).2)
  obtain ⟨G,M,hM,hMI,hGm,hG2,hGp,hrep⟩ := natural_terminal_brownian_representation P hT F hF hle hnull
    W A hW hA hclock c hc hcm hcT hct hcut hcc hco R hR hRT hFnat U hU hUm
  let k := ∫ w,U w ∂P
  let X := fun t w => k+M t w
  obtain ⟨hXm,hXrc,hXa,hXCE⟩ := conditional_process_from_represented_terminal P F hle U hU M hM k hrep
  have hXc w : Continuous (fun t => X t w) := continuous_const.add (hM.path w)
  have hconst : AdaptedVariationWitness F (fun _ (_ : Ω) => k) := by
    refine ⟨(fun _ _ => k),(fun _ _ => 0),?_,?_,?_,?_⟩
    · exact fun _ => ⟨measurable_const,measurable_const⟩
    · exact fun _ => ⟨monotone_const,monotone_const⟩
    · exact fun _ _ => ⟨continuousWithinAt_const,continuousWithinAt_const⟩
    · exact fun _ _ => (sub_zero _).symm
  have hMl := continuous_m2_is_local P F hF hle (fun j => realTimeClamp (T := T) (c j)) hct.monotone hcut hcc M hM
  have hX : SemimartingaleDecomposition P F X (fun _ _ => k) M :=
    ⟨global_variation_localized hT F hF _ hconst,hMl,(fun w _ _ => (hXc w).continuousAt),fun _ _ _ => rfl⟩
  obtain ⟨hb,hbounds⟩ := exponential_conditional_common_bounds P F hle V (hV.mono (hle _) le_rfl)
    f hfm B a hf X hXc hXCE
  have hpos : ∀ᵐ w ∂P,∀ r∈Icc 0 R,Real.exp (-|a| * B)≤X (realTimeClamp r) w :=
    hbounds.mono (fun w hw r _ => (hw _).1)
  have hGi : ∀ j,∀ᵐ w ∂P,IntervalIntegrable (fun r => G (w,r)^2) volume 0 (c j) := by
    intro j
    have hg := hG2.mono_measure (Measure.prod_mono (le_refl P)
      (Measure.restrict_mono (show Ioc (0:ℝ) (c j) ⊆ Ioi 0 from fun _ hr => hr.1) (le_refl volume)))
    filter_upwards [(memLp_two_iff_integrable_sq hg.aestronglyMeasurable).mp hg |>.prod_right_ae] with w hw
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (hc j).le).mpr hw
  obtain ⟨N,hN,hNI,hZ,he⟩ := logarithmic_brownian_bsde P hT F hF hle hnull W A X M (fun _ => k) hX hW hA
    G (fun w => hGm.comp measurable_prodMk_left) R hR hRT a (Real.exp (-|a| * B)) ha hb hpos
    c hc hcm hcT hct hcut hcc hGi (fun j w r hr => hclock w r hr.1 ((EReal.coe_le_coe hr.2).trans_lt (hcT j))) hGp hMI
  have hXT : X (realTimeClamp R) =ᵐ[P] U := by
    have hh := hXCE (realTimeClamp R)
    rw [condExp_of_stronglyMeasurable (hle _) hUm.stronglyMeasurable (hU.integrable (by norm_num))] at hh
    exact hh
  refine ⟨X,_,N,hN,hNI,hXCE,hbounds.mono (fun w hw t => (hw t).1),?_⟩
  intro t ht
  filter_upwards [he t ht,hXT] with w hw htw
  rw [htw] at hw
  simpa only [U,Real.log_exp,mul_div_cancel_left₀ _ ha] using hw

end Asakura.Chapter5
