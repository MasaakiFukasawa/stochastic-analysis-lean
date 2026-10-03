import Chapter6ContinuousVectorConstruction
import Chapter6StoppedGrowthClock
import Chapter6LocalizedDensityData
import Chapter6StoppedGrowthEnergyMoment
import Chapter6EntropyDensityLimit

open MeasureTheory Set Filter Finset
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter7
set_option maxHeartbeats 5500000
set_option backward.isDefEq.respectTransparency false

/-- Linear growth gives a true density by the manuscript's exit-time,
changed-measure moment, entropy and uniform-integrability argument. -/
theorem linear_growth_exponential_mean_one {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (H : Fin d → Ω × ℝ → ℝ) (hHm : ∀ j,Measurable (H j))
    (hHp : ∀ j b,0<b → @Measurable _ _
      (progressiveSpace (fun t : Icc (0:ℝ) b => B.F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) b => H j (z.1,z.2.val)))
    (hHc : ∀ j w,Continuous (fun r => H j (w,r)))
    (R : ℝ) (hR : 0≤R) (K : ℝ) (hK : 0≤K)
    (hHb : ∀ w r,r∈Icc 0 R → ‖WithLp.toLp 2 (fun j => H j (w,r))‖≤K*(1+‖WithLp.toLp 2 (fun j => B.W j (realTimeClamp r) w)‖)) :
    ∃ (N : Fin d → HalfClosedTime → Ω → ℝ) (C : HalfClosedTime → Ω → ℝ),
      (∀ j,LocalMProcessWitness P B.F (N j)) ∧
      (∀ j,ItoCovarianceFormula P B.F (B.W j) (H j) (N j)) ∧
      LocalCovarianceWitness P B.F (fun t w => ∑ j,N j t w) (fun t w => ∑ j,N j t w) C ∧
      (∀ r : ℝ,0≤r → C (realTimeClamp r)=ᵐ[P] fun w => ∫ s in 0..r,∑ j,(H j (w,s))^2) ∧
      let D := fun w => Real.exp ((∑ j,N j (realTimeClamp R) w)-C (realTimeClamp R) w/2)
      Integrable D P ∧ (∫ w,D w ∂P)=1 := by
  obtain ⟨N,hN,hNI⟩ := continuous_vector_integrals_constructed P B H hHm hHp hHc
  obtain ⟨hZ,C,L,hC,hL,hCe,hLe⟩ := continuous_vector_integral_covariances P B H hHm hHc N hN hNI
  let Z := fun t w => ∑ j,N j t w
  have hEC : ∀ᵐ w ∂P,∀ r∈Icc 0 R,C (realTimeClamp r) w=∫ s in 0..r,∑ j,(H j (w,s))^2 :=
    covariance_density_common_time P B.F Z Z C hZ hZ hC (fun z => ∑ j,(H j z)^2)
      (fun b hb => ae_of_all _ fun w => (continuous_finsetSum _ (fun j _ => (hHc j w).pow 2)).continuousOn.intervalIntegrable_of_Icc hb)
      hCe R hR
  have hEL j : ∀ᵐ w ∂P,∀ r∈Icc 0 R,L j (realTimeClamp r) w=∫ s in 0..r,H j (w,s) :=
    covariance_density_common_time P B.F Z (B.W j) (L j) hZ (B.martingale j) (hL j) (H j)
      (fun b hb => ae_of_all _ fun w => (hHc j w).continuousOn.intervalIntegrable_of_Icc hb) (hLe j) R hR
  obtain ⟨τ,hτ,hτR,hτlim,hτb⟩ := brownian_norm_level_stops P B R hR
  have hCb n : ∀ᵐ w ∂P,|C (τ n w) w|≤K^2*(1+((n:ℝ)+1))^2*R :=
    linear_growth_stopped_clock_bound P B.W H hHc C R hR hEC K ((n:ℝ)+1) hK (by positivity)
      hHb (τ n) (hτR n) (hτb.mono (fun w hw => hw n))
  let Dn := fun n w => Real.exp (Z (τ n w) w-C (τ n w) w/2)
  have hd n := localized_density_data P B Z C hZ hC L hL H R hR hEL (τ n) (hτ n) (hτR n)
    (K^2*(1+((n:ℝ)+1))^2*R) (hCb n)
  choose hDm hDi hDmean Q hQp hQD hAE hEi hEe BQ hBQ hrep using hd
  have hWc w : ContinuousOn (fun r => (fun j => B.W j (realTimeClamp r) w)) (Icc 0 R) := by
    have hh := (continuous_pi (fun j => (open_path_stopped_continuous (B.W j) ((B.martingale j).path P B.F) R hR (EReal.coe_lt_top _) w).comp real_time_clamp_continuous)).continuousOn (s := Icc 0 R)
    apply hh.congr
    intro r hr
    funext j
    simp only [Function.comp_def,min_eq_right (real_time_clamp_mono hr.2)]
  let A := (d:ℝ)*K*R
  let e := Real.exp (((d:ℝ)*K+1)*R)
  let Bound := R*K^2*(2*(1+A*e)^2+8*e^2*(d:ℝ)^2*R)
  have hbound n : (∫ w,Dn n w*Real.log (Dn n w) ∂P)≤Bound/2 := by
    letI := hQp n
    let u := fun w => (finitePrefixTime R hR (τ n w)).val
    have hum w : u w∈Icc 0 R := (finitePrefixTime R hR (τ n w)).property
    have heu w : realTimeClamp (u w)=τ n w := by
      dsimp [u]
      rw [finite_prefix_time_clamp R hR (le_top : (R:EReal)≤⊤),min_eq_right (hτR n w)]
    have hCm := (hC.stopped_regular P B.F B.mono B.le hZ hZ (τ n) (hτ n)
      (fun w => (hτR n w).trans_lt (changed_time_finite R hR))).1 ⊤
    simp only [min_top_right] at hCm
    have hCeq : ∀ᵐ w ∂Q n,C (τ n w) w=∫ s in 0..u w,∑ j,(H j (w,s))^2 := by
      apply (hAE n _).mp
      filter_upwards [hEC] with w hw
      rw [←heu w]
      exact hw (u w) (hum w)
    have hb := stopped_growth_energy_moment (Q n) (BQ n) B.W H R hR K hK hWc hHc hHb u hum (hrep n)
      (fun w => C (τ n w) w) (hCm.mono (B.le _) le_rfl).aestronglyMeasurable hCeq
    rw [hEe n]
    exact div_le_div_of_nonneg_right hb.2 (by norm_num)
  let D := fun w => Real.exp (Z (realTimeClamp R) w-C (realTimeClamp R) w/2)
  have hlim : ∀ᵐ w ∂P,Tendsto (fun n => Dn n w) atTop (𝓝 (D w)) := by
    apply ae_of_all
    intro w
    apply tendsto_const_nhds.congr'
    filter_upwards [hτlim w] with n hn
    simp only [Dn,D,hn]
  have hfinal := entropy_localized_density_limit P Dn hDm hDi (fun n => ae_of_all _ fun w => (Real.exp_pos _).le)
    hEi (Bound/2) hbound hDmean D hlim
  exact ⟨N,C,hN,hNI,hC,hCe,hfinal⟩

end Asakura.Chapter6
