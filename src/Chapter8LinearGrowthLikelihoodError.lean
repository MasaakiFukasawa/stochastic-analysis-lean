import Chapter8LinearGrowthLikelihoodBrownian
import Chapter8DominatedLikelihoodError
import Chapter8ObservedPathEnvelope
import Chapter6BrownianPathEnvelope

open MeasureTheory Set Filter Finset Matrix
open scoped Topology BigOperators NNReal ENNReal
namespace Asakura.Chapter8
open Asakura.Chapter6 Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5
set_option maxHeartbeats 3800000
set_option backward.isDefEq.respectTransparency false

/-- Construct the true-parameter probability measure and its Brownian
noise, then derive the estimation error using the actual Ito integrals. -/
theorem linear_growth_likelihood_error_constructed {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P d)
    (H N : Fin n → Fin d → HalfClosedTime → Ω → ℝ)
    (hHa : ∀ k j t,Measurable[B.F t] (H k j t)) (hHc : ∀ k j w,Continuous (fun t => H k j t w))
    (hN : ∀ k j,LocalMProcessWitness P B.F (N k j))
    (hNI : ∀ k j,ItoCovarianceFormula P B.F (B.W j) (fun z => H k j (realTimeClamp z.2) z.1) (N k j))
    (K : ℝ) (hK : 0≤K) (R : ℝ) (hR : 0<R)
    (hHb : ∀ k w r,r∈Icc 0 R → ‖WithLp.toLp 2 (fun j => H k j (realTimeClamp r) w)‖≤
      K*(1+‖WithLp.toLp 2 (fun j => B.W j (realTimeClamp r) w)‖))
    (θ : Fin n → ℝ) :
    let score := fun w k => ∑ j,N k j (realTimeClamp R) w
    let info : Ω → Matrix (Fin n) (Fin n) ℝ := fun w k l => ∫ r in 0..R,∑ j,H k j (realTimeClamp r) w*H l j (realTimeClamp r) w
    ∃ (Q : Measure Ω) (hQp : IsProbabilityMeasure Q),
      Q=P.withDensity (fun w => ENNReal.ofReal (Real.exp (quadraticLogLikelihood (info w) (score w) θ))) ∧
      ∃ (BQ : BrownianSystem Q d) (M : Fin n → Fin d → HalfClosedTime → Ω → ℝ),
        BQ.F=B.F ∧ (∀ k j,LocalMProcessWitness Q BQ.F (M k j)) ∧
        (∀ k j,ItoCovarianceFormula Q BQ.F (BQ.W j) (fun z => H k j (realTimeClamp z.2) z.1) (M k j)) ∧
        (∀ᵐ w ∂Q,score w=info w *ᵥ θ+(fun k => ∑ j,M k j (realTimeClamp R) w) ∧
          ((info w).PosDef → (info w)⁻¹ *ᵥ score w-θ=(info w)⁻¹ *ᵥ (fun k => ∑ j,M k j (realTimeClamp R) w))) := by
  let D := fun w => ENNReal.ofReal (Real.exp (quadraticLogLikelihood
    (fun k l => ∫ r in 0..R,∑ j,H k j (realTimeClamp r) w*H l j (realTimeClamp r) w)
    (fun k => ∑ j,N k j (realTimeClamp R) w) θ))
  let Q := P.withDensity D
  obtain ⟨hQp,BQ,hF,hW⟩ := linear_growth_likelihood_brownian P B H N
    (fun k j t => hHa k j _) (fun k j w => (hHc k j w).comp real_time_clamp_continuous)
    hN hNI K hK R hR.le hHb θ
  letI : IsProbabilityMeasure Q := hQp
  let G := fun j (z : Ω × ℝ) => ∑ k,θ k*H k j (realTimeClamp z.2) z.1
  let C := ∑ k,|θ k| *K
  have hC : 0≤C := Finset.sum_nonneg (fun k _ => mul_nonneg (abs_nonneg _) hK)
  have hGc j w : Continuous (fun r => G j (w,r)) := continuous_finsetSum _
    (fun k _ => ((hHc k j w).comp real_time_clamp_continuous).const_mul _)
  have hGb w r (hr : r∈Icc 0 R) : ‖WithLp.toLp 2 (fun j => G j (w,r))‖≤
      C*(1+‖WithLp.toLp 2 (fun j => B.W j (realTimeClamp r) w)‖) := by
    have he : WithLp.toLp 2 (fun j => G j (w,r))=
        ∑ k,θ k • WithLp.toLp 2 (fun j => H k j (realTimeClamp r) w) := by
      ext j
      simp only [G,WithLp.ofLp_sum,Finset.sum_apply,PiLp.smul_apply,smul_eq_mul]
    rw [he]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ k,(|θ k| *K)*(1+‖WithLp.toLp 2 (fun j => B.W j (realTimeClamp r) w)‖) := by
        apply Finset.sum_le_sum
        intro k _
        rw [norm_smul,Real.norm_eq_abs,mul_assoc]
        exact mul_le_mul_of_nonneg_left (hHb k w r hr) (abs_nonneg _)
      _ = _ := by rw [Finset.sum_mul]
  have hrep j r (hr : r∈Icc 0 R) : BQ.W j (realTimeClamp r)=ᵐ[Q]
      fun w => B.W j (realTimeClamp r) w-∫ s in 0..r,G j (w,s) := by
    simpa only [min_eq_right hr.2] using hW j r hr.1
  have hX := changed_brownian_path_moment P Q B BQ G hGc R C hR.le hC hGb hrep
  obtain ⟨KQ,hKQ,hKQp,hHQb⟩ := observed_path_coefficient_envelope P Q B R hR.le hX H K hK hHb
  obtain ⟨E,hE,hEp,hEb⟩ := brownian_path_L2_envelope P B R hR.le
  let KP := fun w => K*(1+E w)
  have hKP : MemLp KP 2 P := ((memLp_const (1:ℝ) : MemLp (fun _ : Ω => (1:ℝ)) 2 P).add hE).const_mul K
  have hKPp w : 0≤KP w := mul_nonneg hK (by linarith [hEp w])
  have hHP k j w r (hr : r∈Icc 0 R) : |H k j (realTimeClamp r) w|≤KP w :=
    (PiLp.norm_apply_le (WithLp.toLp 2 (fun j => H k j (realTimeClamp r) w)) j).trans
      ((hHb k w r hr).trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl (hEb w r hr)) hK))
  have hW' j r (hr : r∈Icc 0 R) : B.W j (realTimeClamp r)=ᵐ[Q]
      fun w => BQ.W j (realTimeClamp r) w+∫ s in 0..r,∑ k,θ k*H k j (realTimeClamp s) w := by
    filter_upwards [hrep j r hr] with w hw
    dsimp only [G] at hw
    linarith
  obtain ⟨M,hM,hMI,he⟩ := dominated_likelihood_error_written P Q B BQ hF
    (withDensity_absolutelyContinuous P D) H N hHa hHc hN hNI R hR KP KQ hKP hKQ hKPp hKQp hHP hHQb θ hW'
  exact ⟨Q,hQp,rfl,BQ,M,hF,hM,hMI,he⟩
end Asakura.Chapter8
