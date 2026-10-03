import Chapter5ZeroIto
import Chapter5ClippedClockIntegral

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false

/-- Time-space Ito, with the clock, its zero stochastic integral, and the
vanishing mixed covariances all constructed from the previous chapters. -/
theorem time_space_ito_constructed
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X A M C : ClosedTime T → Ω → ℝ)
    (hX : SemimartingaleDecomposition P F X A M)
    (hC : LocalCovarianceWitness P F M M C)
    (R : ℝ) (hR : 0 ≤ R) (hRT : (R:EReal) < T)
    (f : (Fin 2 → ℝ) → ℝ) (hf : ContDiff ℝ 2 f)
    (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (hcm : Monotone c)
    (hcT : ∀ n, (c n:EReal) < T)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < realTimeClamp (T := T) (c n)) :
    let K := fun t => (finitePrefixTime (T := T) R hR t).val
    let V := fun t w => ![K t,X t w]
    ∃ I J : ClosedTime T → Ω → ℝ,
      SemimartingaleIntegralFormula P F c hc A M
        (fun z => fderiv ℝ f (V (realTimeClamp z.2) z.1) (Pi.single 1 1)) I ∧
      VariationIntegralFormula P c hc C
        (fun z => fderiv ℝ (fderiv ℝ f) (V (realTimeClamp z.2) z.1)
          (Pi.single 1 1) (Pi.single 1 1)) J ∧
      ∀ d : ℝ, 0 ≤ d → d ≤ R →
        (fun w => f ![d,X (realTimeClamp d) w]) =ᵐ[P]
          fun w => f ![0,X ⊥ w] +
            (∫ r in 0..d, fderiv ℝ f ![r,X (realTimeClamp r) w] (Pi.single 0 1)) +
            I (realTimeClamp d) w + J (realTimeClamp d) w/2 := by
  classical
  dsimp only
  let K := fun t => (finitePrefixTime (T := T) R hR t).val
  let V := fun t w => ![K t,X t w]
  let XX : Fin 2 → ClosedTime T → Ω → ℝ := ![(fun t _ => K t),X]
  let AA : Fin 2 → ClosedTime T → Ω → ℝ := ![(fun t _ => K t),A]
  let MM : Fin 2 → ClosedTime T → Ω → ℝ := ![(fun _ _ => 0),M]
  let CC := fun (i j : Fin 2) => if i = 1 ∧ j = 1 then C else (fun _ _ => 0)
  have hx i : SemimartingaleDecomposition P F (XX i) (AA i) (MM i) := by
    fin_cases i
    · exact clipped_clock_semimartingale P hT F hF R hR
    · exact hX
  have hz (N : ClosedTime T → Ω → ℝ) : LocalCovarianceWitness P F (fun _ _ => 0) N (fun _ _ => 0) := by
    refine ⟨?_,?_⟩
    · simpa only [zero_mul,sub_zero] using zero_local_process P hT F
    · simpa only [zero_mul] using hC.variation.smul F 0
  have hcv i j : LocalCovarianceWitness P F (MM i) (MM j) (CC i j) := by
    fin_cases i <;> fin_cases j
    · exact hz _
    · exact hz _
    · exact (hz M).symm P F
    · exact hC
  obtain ⟨Z,J,hZ,hJ,he⟩ := constructed_multivariate_ito P hT F hF hle hnull
    XX AA MM CC hx hcv f hf c hc hcm hcT hcc
  have hJzero i j (hij : ¬(i=1 ∧ j=1)) : ∀ᵐ w ∂P, ∀ t, t < ⊤ → J i j t w = 0 := by
    have hj := hJ i j
    simp only [CC,if_neg hij] at hj
    exact hj.unique P c hc hcc _ _ (fun _ _ => 0) _ (zero_variation_integral P c hc _)
  obtain ⟨D,N,hDN,hD,hN⟩ := hZ 0
  have hn : ∀ᵐ w ∂P, ∀ t, t < ⊤ → N t w = 0 :=
    integral_against_zero_martingale P hT F hF hle hnull N _ hDN.martingale hN
  have hz0 : ∀ᵐ w ∂P, ∀ t, t < ⊤ → Z 0 t w = D t w := by
    filter_upwards [hn] with w hw
    intro t ht
    rw [hDN.decomposition t ht w,hw t ht,add_zero]
  have hvec t w : (fun i => XX i t w) = V t w := by ext i; fin_cases i <;> rfl
  refine ⟨Z 1,J 1 1,?_,?_,?_⟩
  · simpa only [hvec,V,K,AA,MM,Matrix.cons_val_one,Matrix.cons_val_zero] using hZ 1
  · simpa only [hvec,V,K,CC,ite_true,and_self] using hJ 1 1
  intro d hd hdR
  have hdT : (d:EReal) < T := (EReal.coe_le_coe hdR).trans_lt hRT
  have hdt : realTimeClamp (T := T) d < ⊤ := by
    change (realTimeClamp d : EReal) < T
    rw [real_time_clamp_eq d hd hdT.le]; exact hdT
  have hDtime := clipped_clock_variation_integral P R hR hRT.le D _ c hc hcT hcc hD d hd hdR hdT
  filter_upwards [he,hz0,hDtime,hJzero 0 0 (by decide),hJzero 0 1 (by decide),hJzero 1 0 (by decide)]
    with w hew hzw hdw h00 h01 h10
  have hh := hew (realTimeClamp d) hdt
  have hv t : (fun i => XX i t w) = V t w := by ext i; fin_cases i <;> rfl
  simp only [Fin.sum_univ_two,h00 _ hdt,h01 _ hdt,h10 _ hdt,zero_add,add_zero,hzw _ hdt] at hh
  rw [hdw] at hh
  have hkd : K (realTimeClamp d) = d := finite_prefix_time_of_real R d hR ⟨hd,hdR⟩ hRT.le
  have hk0 : K ⊥ = 0 := by
    change (min (0:EReal) (R:EReal)).toReal = 0
    rw [min_eq_left (by exact_mod_cast hR),EReal.toReal_zero]
  simp only [hv,V,hkd,hk0] at hh
  have hint : (∫ r in 0..d, fderiv ℝ f ![K (realTimeClamp r),X (realTimeClamp r) w] (Pi.single 0 1)) =
      ∫ r in 0..d, fderiv ℝ f ![r,X (realTimeClamp r) w] (Pi.single 0 1) := by
    apply intervalIntegral.integral_congr
    intro r hr
    have hr' : r ∈ Icc 0 d := by simpa [uIcc_of_le hd] using hr
    have hkr : K (realTimeClamp r) = r := finite_prefix_time_of_real R r hR
      (Icc_subset_Icc_right hdR hr') hRT.le
    dsimp only
    rw [hkr]
  rw [hint] at hh
  simpa only [add_assoc] using hh

end Asakura.Chapter5
