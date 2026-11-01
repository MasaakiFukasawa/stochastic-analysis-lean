import Chapter6ContinuousVectorConstruction
import Chapter6StoppedGrowthClock
import RevisionLocalizedDensity
import RevisionBrownianStops
import RevisionSurvivalDensity
import Chapter6StoppedGrowthEnergyMoment


open MeasureTheory Set Filter Finset
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter7
set_option maxHeartbeats 5500000
set_option backward.isDefEq.respectTransparency false

/-- Linear growth gives a true density by the manuscript's exit-time,
changed-measure maximal moment and survival-event argument. No entropy or uniform integrability. -/
theorem linear_growth_exponential_mean_one_exit {Ω : Type*} {m : MeasurableSpace Ω}
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
  have hBc j : ∀ w,Continuous (fun t => B.W j (min (realTimeClamp R) t) w) :=
    open_path_stopped_continuous (B.W j) ((B.martingale j).path P B.F) R hR (EReal.coe_lt_top _)
  let V := fun j w => finiteRealPath (B.W j) R (hBc j) w
  let S := fun w => ∑ j, ‖V j w‖
  have hSm : Measurable S := Finset.measurable_sum _ (fun j _ =>
    (finite_real_path_measurable B.F B.le (B.W j) R (EReal.coe_lt_top _) (hBc j)
      ((B.martingale j).adapted P B.F)).norm)
  have hS0 w : 0≤S w := sum_nonneg (fun _ _ => norm_nonneg _)
  have hSW w t : ‖WithLp.toLp 2 (fun j => B.W j (min (realTimeClamp R) t) w)‖≤S w := by
    apply (euclidean_norm_le_abs_sum _).trans
    apply sum_le_sum
    intro j _
    have he := (V j w).norm_coe_le_norm (finitePrefixTime R hR t)
    change |B.W j (realTimeClamp (finitePrefixTime R hR t).val) w|≤_ at he
    rw [finite_prefix_time_clamp R hR (le_top : (R:EReal)≤⊤)] at he
    exact he
  obtain ⟨τ,hτ,hτR,hτlim,hτb,hgood⟩ := brownian_norm_level_stops_survival P B R hR S hSW
  have hCb n : ∀ᵐ w ∂P,|C (τ n w) w|≤K^2*(1+((n:ℝ)+1))^2*R :=
    linear_growth_stopped_clock_bound P B.W H hHc C R hR hEC K ((n:ℝ)+1) hK (by positivity)
      hHb (τ n) (hτR n) (hτb.mono (fun w hw => hw n))
  let Dn := fun n w => Real.exp (Z (τ n w) w-C (τ n w) w/2)
  have hd n := localized_density_data_survival P B Z C hZ hC L hL H R hR hEL (τ n) (hτ n) (hτR n)
    (K^2*(1+((n:ℝ)+1))^2*R) (hCb n)
  choose hDm hDi hDmean Q hQp hQD hAE BQ hBQ hrep using hd
  have hWc w : ContinuousOn (fun r => (fun j => B.W j (realTimeClamp r) w)) (Icc 0 R) := by
    have hh := (continuous_pi (fun j => (open_path_stopped_continuous (B.W j) ((B.martingale j).path P B.F) R hR (EReal.coe_lt_top _) w).comp real_time_clamp_continuous)).continuousOn (s := Icc 0 R)
    apply hh.congr
    intro r hr
    funext j
    simp only [Function.comp_def,min_eq_right (real_time_clamp_mono hr.2)]
  let A := (d:ℝ)*K*R
  let e := Real.exp (((d:ℝ)*K+1)*R)
  let Bound := (d:ℝ)^2*e^2*(2*A^2+8*(d:ℝ)^2*R)
  have hbound n : Integrable (fun w => S w^2) (Q n) ∧
      (∫ w,S w^2 ∂Q n)≤Bound := by
    letI := hQp n
    let u := fun w => (finitePrefixTime R hR (τ n w)).val
    have hum w : u w∈Icc 0 R := (finitePrefixTime R hR (τ n w)).property
    obtain ⟨G,hGi,hG0,hG2,hGb⟩ := brownian_path_L2_envelope_bound (Q n) (BQ n) R hR
    let M := fun w => (d:ℝ)^2*e^2*(2*A^2+2*G w^2)
    have hMi : Integrable M (Q n) :=
      ((integrable_const (2*A^2)).add (hGi.integrable_sq.const_mul 2)).const_mul _
    have hb : ∀ᵐ w ∂Q n,S w^2≤M w := by
      filter_upwards [hrep n] with w hw
      have hp := stopped_vector_growth_path_bound
        (fun r j => B.W j (realTimeClamp r) w)
        (fun r j => (BQ n).W j (realTimeClamp r) w) (fun r j => H j (w,r))
        R (u w) K (G w) hR (hum w) hK (hG0 w) (hWc w)
        (continuous_pi (fun j => hHc j w)).continuousOn (hHb w) (hGb w)
        (fun r hr j => by linarith [hw j r hr])
      have hVp j : ‖V j w‖≤(A+G w)*e := by
        have hGw := hG0 w
        apply (ContinuousMap.norm_le _ (by dsimp [A,e]; positivity)).2
        intro r
        have hh := (PiLp.norm_apply_le (WithLp.toLp 2 (fun j => B.W j (realTimeClamp r.val) w)) j).trans (hp r.val r.property)
        simpa only [V,finiteRealPath,ContinuousMap.coe_mk,Real.norm_eq_abs,A,e] using hh
      have hSp : S w≤(d:ℝ)*(A+G w)*e := by
        have hh := sum_le_sum (fun j (_ : j∈Finset.univ) => hVp j)
        simpa only [S,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,mul_assoc] using hh
      have hsq := pow_le_pow_left₀ (hS0 w) hSp 2
      have htwo : (A+G w)^2≤2*A^2+2*G w^2 := by nlinarith [sq_nonneg (A-G w)]
      have hh := mul_le_mul_of_nonneg_left htwo (show 0≤(d:ℝ)^2*e^2 by positivity)
      dsimp [M]
      nlinarith [hsq]
    have hSi : Integrable (fun w => S w^2) (Q n) :=
      hMi.mono' (hSm.pow_const 2).aestronglyMeasurable
        (hb.mono (fun w hw => by simpa only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (S w))] using hw))
    refine ⟨hSi,?_⟩
    calc
      _ ≤ ∫ w,M w ∂Q n := integral_mono_ae hSi hMi hb
      _ = (d:ℝ)^2*e^2*(2*A^2+2*(∫ w,G w^2 ∂Q n)) := by
        rw [integral_const_mul,integral_add (integrable_const _) (hGi.integrable_sq.const_mul _),
          integral_const,integral_const_mul]
        simp
      _ ≤ Bound := by
        dsimp [Bound]
        exact mul_le_mul_of_nonneg_left (by linarith [hG2]) (by positivity)
  let D := fun w => Real.exp (Z (realTimeClamp R) w-C (realTimeClamp R) w/2)
  have hDmZ : Measurable D := by
    have hmz := (hZ.adapted P B.F _ (changed_time_finite R hR)).mono (B.le _) le_rfl
    have hmc := (hC.adapted P B.F hZ hZ _ (changed_time_finite R hR)).mono (B.le _) le_rfl
    exact (hmz.sub (hmc.div_const 2)).exp
  have heq (n : ℕ) w (hw : S w<(n:ℝ)+1) : D w=Dn n w := by
    dsimp [D,Dn]
    rw [hgood n w hw]
  have htail : Tendsto (fun n : ℕ => ∫ w in {w | (n:ℝ)+1≤S w},Dn n w ∂P) atTop (𝓝 0) := by
    have hbad (n : ℕ) : (∫ w in {w | (n:ℝ)+1≤S w},Dn n w ∂P)≤Bound/((n:ℝ)+1)^2 := by
      letI := hQp n
      let E := {w | (n:ℝ)+1≤S w}
      have hEm : MeasurableSet E := measurableSet_le measurable_const hSm
      have hmass : (Q n).real E=∫ w in E,Dn n w ∂P := by
        rw [Measure.real,hQD n,withDensity_apply _ hEm]
        rw [←ofReal_integral_eq_lintegral_ofReal (hDi n).restrict (.of_forall (fun _ => (Real.exp_pos _).le))]
        exact ENNReal.toReal_ofReal (integral_nonneg (fun _ => (Real.exp_pos _).le))
      have hh := mul_meas_ge_le_integral_of_nonneg (.of_forall (fun w => sq_nonneg (S w))) (hbound n).1 (((n:ℝ)+1)^2)
      have he : {w | ((n:ℝ)+1)^2≤S w^2}=E := by
        ext w
        exact sq_le_sq₀ (by positivity) (hS0 w)
      rw [he,hmass] at hh
      exact (le_div_iff₀ (by positivity)).mpr (by nlinarith [(hbound n).2])
    have hN : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    have hden : Tendsto (fun n : ℕ => ((n:ℝ)+1)^2) atTop atTop :=
      tendsto_atTop_mono (fun n => by nlinarith [Nat.cast_nonneg (α:=ℝ) n]) hN
    exact squeeze_zero (fun n => integral_nonneg (fun _ => (Real.exp_pos _).le)) hbad
      (tendsto_const_nhds.div_atTop hden)
  have hfinal := Asakura.Revision20261101.mean_one_of_survival P Dn D S hDi
    (fun _ _ => (Real.exp_pos _).le) hDmean hDmZ (fun _ => (Real.exp_pos _).le) hSm heq htail
  exact ⟨N,C,hN,hNI,hC,hCe,hfinal⟩

end Asakura.Chapter6
