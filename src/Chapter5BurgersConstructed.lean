import Chapter5BoundedExponentialBSDE
import Chapter5ConditionalHeat

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 6500000
set_option backward.isDefEq.respectTransparency false

/-- The quadratic BSDE and its heat-kernel expression belong to the
same constructed process, using Brownian independent Gaussian increments. -/
theorem burgers_log_bsde_heat_representation
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
    (hind : ∀ t∈Icc 0 R,Indep (F (realTimeClamp t))
      (MeasurableSpace.comap (fun w => W (realTimeClamp R) w-W (realTimeClamp t) w) inferInstance) P)
    (hlaw : ∀ t∈Icc 0 R,P.map (fun w => W (realTimeClamp R) w-W (realTimeClamp t) w)=
      gaussianReal 0 (R-t).toNNReal)
    (f : ℝ → ℝ) (hf : Continuous f) (B a : ℝ) (ha : a≠0) (hb : ∀ x,|f x|≤B) :
    ∃ X : ClosedTime T → Ω → ℝ,∃ Z : Ω × ℝ → ℝ,∃ N : ClosedTime T → Ω → ℝ,
      LocalMProcessWitness P F N ∧ ItoCovarianceFormula P F W Z N ∧
      (∀ t∈Icc 0 R,(fun w => Real.log (X (realTimeClamp t) w)/a) =ᵐ[P]
        fun w => logHeat a (fun x => Real.exp (a*f x)) (W (realTimeClamp t) w) (R-t)) ∧
      (∀ t∈Icc 0 R,(fun w => f (W (realTimeClamp R) w)) =ᵐ[P]
        fun w => logHeat a (fun x => Real.exp (a*f x)) (W (realTimeClamp t) w) (R-t)-
          (∫ r in t..R,a/2*(Z (w,r))^2)+(N (realTimeClamp R) w-N (realTimeClamp t) w)) := by
  have hWm (r : ℝ) : Measurable[F (realTimeClamp r)] (W (realTimeClamp r)) := by
    obtain ⟨j,hj⟩ := hco r
    exact hW.adapted P F _ ((real_time_clamp_mono hj).trans_lt (hcut j))
  obtain ⟨X,Z,N,hN,hNI,hCE,hpos,hEq⟩ := bounded_exponential_bsde_constructed
    P hT F hF hle hnull W A hW hA hclock c hc hcm hcT hct hcut hcc hco R hR hRT hFnat
    (W (realTimeClamp R)) (hWm R) f hf.measurable B a ha hb
  have hheat (t : ℝ) (ht : t∈Icc 0 R) :
      (fun w => Real.log (X (realTimeClamp t) w)/a) =ᵐ[P]
        fun w => logHeat a (fun x => Real.exp (a*f x)) (W (realTimeClamp t) w) (R-t) := by
    have hh := conditional_log_heat (F (realTimeClamp t)) P (hle _)
      (W (realTimeClamp t)) (fun w => W (realTimeClamp R) w-W (realTimeClamp t) w)
      (hWm t) (((hWm R).mono (hle _) le_rfl).sub ((hWm t).mono (hle _) le_rfl))
      (hind t ht) (R-t) (sub_nonneg.mpr ht.2) (hlaw t ht) f hf a (Real.exp (|a| * B))
      (fun x => by simpa only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using (exponential_payoff_bounds f B a hb x).2)
    have he : (fun w => W (realTimeClamp t) w+(W (realTimeClamp R) w-W (realTimeClamp t) w)) = W (realTimeClamp R) := by funext w; ring
    simp only [← Function.comp_def,he] at hh
    filter_upwards [hCE (realTimeClamp t),hh] with w hw hw'
    rw [hw]
    exact hw'
  refine ⟨X,Z,N,hN,hNI,hheat,?_⟩
  intro t ht
  filter_upwards [hEq t ht,hheat t ht] with w hw hh
  rwa [hh] at hw

end Asakura.Chapter5
