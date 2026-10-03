import Chapter6ItoChangeEndpoint
import Chapter6LikelihoodDriftGram
import Chapter6BoundedVectorConstruction

open MeasureTheory Set Filter Finset Matrix
open scoped Topology BigOperators NNReal ENNReal
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false

theorem likelihood_error_written {Ω : Type*} {m : MeasurableSpace Ω}
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {d n : ℕ}
    (B : BrownianSystem P d) (BQ : BrownianSystem Q d) (hF : BQ.F=B.F)
    (density : Ω → ℝ≥0) (hd : Measurable density)
    (hQ : Q=P.withDensity (fun w => (density w:ℝ≥0∞))) (hd2 : MemLp (fun w => (density w:ℝ)) 2 P)
    (H N : Fin n → Fin d → HalfClosedTime → Ω → ℝ)
    (hHa : ∀ k j t,Measurable[B.F t] (H k j t)) (hHc : ∀ k j w,Continuous (fun t => H k j t w))
    (hN : ∀ k j,LocalMProcessWitness P B.F (N k j))
    (hNI : ∀ k j,ItoCovarianceFormula P B.F (B.W j) (fun z => H k j (realTimeClamp z.2) z.1) (N k j))
    (K : ℝ) (hK : 0≤K) (hHb : ∀ k j t w,|H k j t w|≤K)
    (R : ℝ) (hR : 0<R) (θ : Fin n → ℝ)
    (hW : ∀ j r,r∈Icc 0 R → B.W j (realTimeClamp r)=ᵐ[Q]
      fun w => BQ.W j (realTimeClamp r) w+∫ s in 0..r,∑ k,θ k*H k j (realTimeClamp s) w) :
    ∃ M : Fin n → Fin d → HalfClosedTime → Ω → ℝ,
      (∀ k j,LocalMProcessWitness Q BQ.F (M k j)) ∧
      (∀ k j,ItoCovarianceFormula Q BQ.F (BQ.W j) (fun z => H k j (realTimeClamp z.2) z.1) (M k j)) ∧
      (let score := fun w k => ∑ j,N k j (realTimeClamp R) w
       let info : Ω → Matrix (Fin n) (Fin n) ℝ := fun w k l => ∫ r in 0..R,∑ j,H k j (realTimeClamp r) w*H l j (realTimeClamp r) w
       let noise := fun w k => ∑ j,M k j (realTimeClamp R) w
       ∀ᵐ w ∂Q,score w=info w *ᵥ θ+noise w ∧
         ((info w).PosDef → (info w)⁻¹ *ᵥ score w-θ=(info w)⁻¹ *ᵥ noise w)) := by
  let G := fun k j (z : Ω × ℝ) => H k j (realTimeClamp z.2) z.1
  have hGr k j w : Continuous (fun r => G k j (w,r)) := (hHc k j w).comp real_time_clamp_continuous
  have hGm k j : Measurable (G k j) := by
    have hm r : Measurable (H k j (realTimeClamp r)) := (hHa k j _).mono (B.le _) le_rfl
    simpa only [G,Function.comp_def,Function.uncurry_def,Prod.swap] using (measurable_uncurry_of_continuous_of_measurable (hGr k j) hm).comp measurable_swap
  have hHQ k j t : Measurable[BQ.F t] (H k j t) := by rw [hF]; exact hHa k j t
  have hGp k j r (hr : 0<r) := continuous_adapted_real_progressive BQ.F BQ.mono (G k j) r hr.le
    (fun s _ => hHQ k j _) (fun w => (hGr k j w).continuousOn)
  have hex k := bounded_vector_integrals_constructed Q BQ (G k) (hGm k) (hGp k) K hK (fun j z => hHb k j _ _)
  choose M hM hMI using hex
  let β := fun j (z : Ω × ℝ) => ∑ k,θ k*G k j z
  let L := ∑ k,|θ k| * K
  have hL : 0≤L := sum_nonneg (fun _ _ => mul_nonneg (abs_nonneg _) hK)
  have hβm j : Measurable (β j) := Finset.measurable_sum _ (fun k _ => (hGm k j).const_mul _)
  have hβb j z : |β j z|≤L := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply sum_le_sum
    intro k _
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hHb k j _ _) (abs_nonneg _)
  have he k j := ito_change_endpoint P Q B BQ hF j density hd hQ hd2 (H k j) (N k j) (M k j)
    (hHa k j) (hHc k j) (hN k j) (hM k j) (hNI k j) (hMI k j) K L hK hL (hHb k j) (β j) (hβm j) (hβb j) R hR (hW j)
  refine ⟨M,hM,hMI,?_⟩
  filter_upwards [ae_all_iff.2 (fun k => ae_all_iff.2 (he k))] with w hw
  let I : Matrix (Fin n) (Fin n) ℝ := fun k l => ∫ r in 0..R,∑ j,H k j (realTimeClamp r) w*H l j (realTimeClamp r) w
  let a : Fin n → ℝ := fun k => ∑ j,N k j (realTimeClamp R) w
  let z : Fin n → ℝ := fun k => ∑ j,M k j (realTimeClamp R) w
  have ha : a=I *ᵥ θ+z := by
    funext k
    have hh : a k=(∑ j,M k j (realTimeClamp R) w)+(∑ j,∫ r in 0..R,H k j (realTimeClamp r) w*(∑ l,θ l*H l j (realTimeClamp r) w)) := by
      dsimp only [a]
      simp_rw [hw]
      rw [sum_add_distrib]
    have hi := likelihood_score_drift_gram (fun k j r => H k j (realTimeClamp r) w) R hR.le
      (fun k j => (hGr k j w).continuousOn) θ k
    rw [hi] at hh
    exact hh.trans (add_comm _ _)
  refine ⟨ha,?_⟩
  intro hI
  change I⁻¹ *ᵥ a-θ=I⁻¹ *ᵥ z
  rw [ha]
  exact likelihood_estimator_error I hI θ z

end Asakura.Chapter6
