import Chapter4VectorSolutionPowerMoment
import Chapter4VectorBorelCoefficientDomain
import Chapter4VectorPowerGrowth
import Chapter4VectorSDEInitial

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4.Vector
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- Borel coefficients satisfying the manuscript's growth condition give
finite p-moments of every actual finite-horizon solution. -/
theorem sde_power_moment_from_borel_growth
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T) {dim noise : ℕ}
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (W C : Fin noise → ClosedTime T → Ω → ℝ)
    (hW : ∀ j,LocalMProcessWitness P F (W j))
    (hC : ∀ j,LocalCovarianceWitness P F (W j) (W j) (C j))
    (hclock : ∀ j w (r : ℝ),0≤r → (r:EReal)<T → C j (realTimeClamp r) w=r)
    (R : ℝ) (hR : 0≤R) (hRT : (R:EReal)<T)
    (μ : Fin dim → (Fin dim → ℝ) → ℝ) (σ : Fin dim → Fin noise → (Fin dim → ℝ) → ℝ)
    (hμ : ∀ i,Measurable (μ i)) (hσ : ∀ i j,Measurable (σ i j))
    (L : ℝ) (hL : 0≤L)
    (hμg : ∀ i x,(μ i x)^2≤L*(1+∑ k,(x k)^2))
    (hσg : ∀ i j x,(σ i j x)^2≤L*(1+∑ k,(x k)^2))
    (p : ℝ) (hp : 2≤p)
    (ξ : Ω → Fin dim → ℝ)
    (hξm : Measurable[m] ξ) (hξi : MemLp ξ (ENNReal.ofReal p) P)
    (Y : Ω → C(Icc (0:ℝ) R,Fin dim → ℝ)) (hm : Measurable[m] Y)
    (ha : ∀ r,Measurable[F (realTimeClamp r.val)] (fun w => Y w r))
    (N : Fin dim → Fin noise → ClosedTime T → Ω → ℝ)
    (hn : ∀ i j,LocalMProcessWitness P F (N i j))
    (hI : ∀ i j,ItoCovarianceFormula P F (W j)
      (fun z => σ i j (Y z.1 (finitePrefixTime (T := T) R hR (realTimeClamp z.2)))) (N i j))
    (he : ∀ᵐ w ∂P,∀ r i,Y w r i=ξ w i+(∫ s in 0..r.val,μ i (Y w (projIcc 0 R hR s)))+∑ j,N i j (realTimeClamp r.val) w) :
    MemLp Y (ENNReal.ofReal p) P := by
  letI : MeasurableSpace Ω := m
  have hinit := finite_sde_initial_value P F R hR hRT Y ξ
    (fun i z => μ i (Y z.1 (projIcc 0 R hR z.2))) N hn he
  have hp0 : 0≤p := by linarith only [hp]
  let L' := L*(dim+1)
  have hL' : 0≤L' := by dsimp [L']; positivity
  have sqgrow (b : (Fin dim → ℝ) → ℝ) (hb : ∀ x,(b x)^2≤L*(1+∑ k,(x k)^2)) (x : Fin dim → ℝ) :
      (b x)^2≤L'*(1+‖x‖^2) := by
    have hs : (∑ k,(x k)^2)≤(dim:ℝ)*‖x‖^2 := by
      calc
        _ ≤ ∑ _k : Fin dim,‖x‖^2 := Finset.sum_le_sum (fun k _ => by
          have hh := pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm x k) 2
          simpa only [Real.norm_eq_abs,sq_abs] using hh)
        _ = _ := by simp
    have hh := mul_le_mul_of_nonneg_left hs hL
    dsimp only [L']
    nlinarith only [hb x,hh,mul_nonneg hL (sq_nonneg ‖x‖),mul_nonneg hL (Nat.cast_nonneg (α := ℝ) dim)]
  let G := fun i j (z : Ω × ℝ) => σ i j (Y z.1 (finitePrefixTime (T := T) R hR (realTimeClamp z.2)))
  let U := fun i (z : Ω × ℝ) => μ i (Y z.1 (projIcc 0 R hR z.2))
  have hdom i j := finite_borel_coefficient_domain F hF R hR hRT Y hm ha (σ i j) (hσ i j) L' hL' (sqgrow _ (hσg i j))
  obtain ⟨c,hc,hcm,hcT,hct,hcut,hcc⟩ := positive_real_time_exhaustion hT
  have hξm' i : Measurable[m] (fun w => ξ w i) := (measurable_pi_apply i).comp hξm
  have hξi' i : MemLp (fun w => ξ w i) (ENNReal.ofReal p) P := by
    apply hξi.of_le_mul (c := 1) (hξm' i).aestronglyMeasurable
    exact .of_forall (fun w => by simpa only [one_mul] using norm_le_pi_norm (ξ w) i)
  let K := (L'^(p/2)*(2:ℝ)^(p/2))
  have hK : 0≤K := by dsimp [K]; positivity
  apply vector_solution_power_moment P hT F hF hle hnull W C N hW hC hn
    c hc hcm hcT hct hcut hcc
    (fun j n w r hr => hclock j w r hr.1 ((EReal.coe_le_coe hr.2).trans_lt (hcT n)))
    G (fun i j n => (hdom i j).2.1 (c n) (hc n).le)
    (fun i j n => .of_forall ((hdom i j).2.2 (c n) (hc n).le)) hI
    R hR hRT p hp Y hm ha ((memLp_congr_ae hinit).2 hξi) (fun i w => ξ w i) hξm' hξi'
    U (fun i => (hμ i).comp (clamped_path_evaluation_measurable R hR Y hm))
    (fun i j => (hdom i j).1) K hK _ _ he
  · intro i w r hr
    exact vector_square_growth_power_bound _ _ L p hL hp0 (hμg i _)
  · intro i j w r hr
    dsimp only [G]
    rw [finite_path_lift_real R hR hRT.le Y w r hr]
    exact vector_square_growth_power_bound _ _ L p hL hp0 (hσg i j _)

end Asakura.Chapter4.Vector
