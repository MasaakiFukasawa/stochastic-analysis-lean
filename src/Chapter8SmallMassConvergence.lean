import Chapter8DampedGivenNoiseMoment
import Chapter8DampedDriftMoment
import Chapter8SmallMassErrorMoment
import Chapter8SmallMassGronwallAssembly

open MeasureTheory Set Filter
open scoped NNReal ENNReal RealInnerProductSpace BigOperators Topology
namespace Asakura.Chapter8
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- Assemble the last part of the small-mass proof from the position
identity: the remainder is not assumed small. Its three terms are the
initial velocity, actual drift integral, and actual Ito convolution. -/
theorem small_mass_convergence_from_position_formula {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P n)
    (Γ M : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (α T C L : ℝ) (hα : 0<α) (hT : 0≤T) (hC : 0≤C)
    (hΓ : ∀ x,α*‖x‖^2≤⟪x,Γ x⟫) (b : Fin n → EuclideanSpace ℝ (Fin d))
    (V : Ω → EuclideanSpace ℝ (Fin d)) (hV : MemLp V 2 P)
    (H K : ℝ → Ω × ℝ → EuclideanSpace ℝ (Fin d))
    (hHm : ∀ m,Measurable (H m)) (hKm : ∀ m,Measurable (K m))
    (hH2 : ∀ m,0<m → m≤1 → ∀ t∈Icc 0 T,MemLp (H m) 2 (P.prod (volume.restrict (Ioc 0 t))))
    (hK2 : ∀ m,0<m → m≤1 → ∀ t∈Icc 0 T,MemLp (K m) 2 (P.prod (volume.restrict (Ioc 0 t))))
    (hHb : ∀ m,0<m → m≤1 → ∀ s∈Icc 0 T,(∫ w,‖H m (w,s)‖^2 ∂P)≤C)
    (N : ℝ → ℝ → Fin d → Fin n → HalfClosedTime → Ω → ℝ)
    (hN : ∀ m,0<m → m≤1 → ∀ t∈Icc 0 T,∀ i j,LocalMProcessWitness P B.F (N m t i j))
    (hNI : ∀ m,0<m → m≤1 → ∀ t∈Icc 0 T,∀ i j,ItoCovarianceFormula P B.F (B.W j)
      (fun z => (NormedSpace.exp ((t-z.2) • (-m⁻¹ • Γ)) (b j)) i) (N m t i j))
    (D : ℝ → ℝ → Ω → EuclideanSpace ℝ (Fin d))
    (hc : ∀ m,0<m → m≤1 → ContinuousOn (fun t => ∫ w,‖D m t w‖^2 ∂P) (Icc 0 T))
    (hKb : ∀ m,0<m → m≤1 → ∀ s∈Icc 0 T,(∫ w,‖K m (w,s)‖^2 ∂P)≤L^2*(∫ w,‖D m s w‖^2 ∂P))
    (he : ∀ m,0<m → m≤1 → ∀ t∈Icc 0 T,∀ᵐ w ∂P,
      D m t w=
        (m • M (V w-NormedSpace.exp (t • (-m⁻¹ • Γ)) (V w))+
          M (∫ s in 0..t,NormedSpace.exp ((t-s) • (-m⁻¹ • Γ)) (H m (w,s)))+
          (-M) (WithLp.toLp 2 (fun i => ∑ j,N m t i j (realTimeClamp t) w)))+
        (∫ s in 0..t,(-M) (K m (w,s)))) :
    Tendsto (fun m => sSup ((fun t => ∫ w,‖D m t w‖^2 ∂P) '' Icc 0 T)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  let CV := 4*‖M‖^2*(∫ w,‖V w‖^2 ∂P)
  let CH := ‖M‖^2*C/α^2
  let CN := ‖M‖^2*(∑ j,‖b j‖^2)/(2*α)
  let CR := 3*(CV+CH+CN)
  let A := 3*T*‖M‖^2*L^2+1
  have hCV : 0≤CV := by dsimp [CV]; exact mul_nonneg (by positivity) (integral_nonneg (fun _ => sq_nonneg _))
  have hCH : 0≤CH := by dsimp [CH]; positivity
  have hCN : 0≤CN := by dsimp [CN]; positivity
  have hCR : 0≤CR := by dsimp [CR]; positivity
  have hA : 0<A := by dsimp [A]; positivity
  apply (small_mass_error_sup_limit (fun m t => ∫ w,‖D m t w‖^2 ∂P) T (3*CR) A hT (by positivity) hA hc
    (fun _ _ _ _ _ => integral_nonneg (fun _ => sq_nonneg _)) ?_).2
  intro m hm hm1 t ht
  let E0 := NormedSpace.exp (t • (-m⁻¹ • Γ))
  have hE : ‖E0‖≤1 := (damped_semigroup_norm_bound Γ α m hm hΓ t ht.1).trans
    (Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hα.le) ht.1) hm.le))
  let R0 := fun w => m • M (V w-E0 (V w))
  let RH := fun w => M (∫ s in 0..t,NormedSpace.exp ((t-s) • (-m⁻¹ • Γ)) (H m (w,s)))
  let RN := fun w => (-M) (WithLp.toLp 2 (fun i => ∑ j,N m t i j (realTimeClamp t) w))
  have hv := initial_velocity_second_moment P M E0 hE m hm.le V hV
  have hh := damped_drift_second_moment P Γ α m t C hα hm ht.1 hC hΓ (H m) (hHm m) (hH2 m hm hm1 t ht)
    (fun s hs => hHb m hm hm1 s ⟨hs.1,hs.2.trans ht.2⟩)
  have hhM := random_linear_second_moment P M _ hh.1
  have hn := damped_noise_given_second_moment P B Γ α m t hα hm ht.1 hΓ b (N m t) (hN m hm hm1 t ht) (hNI m hm hm1 t ht)
  have hnM := random_linear_second_moment P (-M) _ hn.1
  have hvb : (∫ w,‖R0 w‖^2 ∂P)≤CV*m^2 := by convert hv.2 using 1 <;> dsimp [CV] <;> ring
  have hhb : (∫ w,‖RH w‖^2 ∂P)≤CH*m^2 := by
    have h := hhM.2.trans (mul_le_mul_of_nonneg_left hh.2 (sq_nonneg ‖M‖))
    convert h using 1 <;> dsimp [CH] <;> ring
  have hnb : (∫ w,‖RN w‖^2 ∂P)≤CN*m := by
    have h := hnM.2.trans (mul_le_mul_of_nonneg_left hn.2 (sq_nonneg ‖-M‖))
    simp only [norm_neg] at h
    convert h using 1 <;> dsimp [CN] <;> ring
  have hrem := small_mass_remainder_moment P R0 RH RN hv.1 hhM.1 hnM.1 m CV CH CN hm.le hm1 hCV hCH hvb hhb hnb
  have hRi : MemLp (fun w => R0 w+RH w+RN w) 2 P := (hv.1.add hhM.1).add hnM.1
  have hu : ContinuousOn (fun s => ∫ w,‖D m s w‖^2 ∂P) (Icc 0 t) :=
    (hc m hm hm1).mono (Icc_subset_Icc le_rfl ht.2)
  have herr := small_mass_error_moment P M t ht.1 (K m) (hKm m) (hK2 m hm hm1 t ht) (D m t)
    (fun w => R0 w+RH w+RN w) hRi (he m hm hm1 t ht) _ hu L
    (fun s hs => hKb m hm hm1 s ⟨hs.1,hs.2.trans ht.2⟩)
  have hi : 0≤∫ s in 0..t,(∫ w,‖D m s w‖^2 ∂P) := intervalIntegral.integral_nonneg ht.1
    (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))
  have hcoef : 3*t*‖M‖^2*L^2≤3*T*‖M‖^2*L^2 := by gcongr; exact ht.2
  have hhcoef := mul_le_mul_of_nonneg_right hcoef hi
  dsimp only [A,CR] at *
  nlinarith
end Asakura.Chapter8
