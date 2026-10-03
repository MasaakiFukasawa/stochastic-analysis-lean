import Chapter3RegularizedBDGConstruction
import Chapter3MomentHolder
import Chapter3DoobSquareMoment

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- Actual Holder and Doob steps following the constructed regularized integral. -/
theorem regularized_bdg_upper_moment
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X A : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X) (hA : LocalCovarianceWitness P F X X A)
    (hAm : ∀ ω, MonotoneOn (fun t => A t ω) (Iio ⊤))
    (hAc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => A s ω) t)
    (hA0 : ∀ ω, A ⊥ ω = 0)
    (ε p : ℝ) (hε : 0 < ε) (hp : 0 < p) (hp2 : p < 2)
    (b : ClosedTime T) (hb : b < ⊤) (K : ℝ) (hK : 0 ≤ K)
    (hbound : ∀ᵐ ω ∂P, A b ω ≤ K) :
    ∃ hx : ∀ ω, Continuous (fun t => X (min b t) ω),
      Integrable (fun ω => ‖continuousPath (fun t ω => X (min b t) ω) hx ω‖^p) P ∧
      (∫ ω, ‖continuousPath (fun t ω => X (min b t) ω) hx ω‖^p ∂P) ≤
        2^p*(4*(2/p)*(∫ ω, (ε+A b ω)^(p/2)-ε^(p/2) ∂P))^(p/2)*
          (∫ ω, (ε+A b ω)^(p/2) ∂P)^(1-p/2) := by
  obtain ⟨Y,hY,hy,hM2,henergy,hpath⟩ := regularized_bdg_upper_construction P hT F hF hle hnull
    X A hX hA hAm hAc hA0 ε p hε hp hp2 b hb K hK hbound
  have hAp ω : 0 ≤ A b ω := by
    rw [← hA0 ω]
    exact hAm ω hT hb bot_le
  have hx ω : Continuous (fun t => X (min b t) ω) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (hX.path P F ω _ ((min_le_left b t).trans_lt hb)).comp
      (continuous_const.min continuous_id).continuousAt
  let S := fun ω => ‖continuousPath (fun t ω => X (min b t) ω) hx ω‖
  let R := fun ω => ‖continuousPath (fun t ω => Y (min b t) ω) hM2.path ω‖
  have hSm : Measurable S := (continuous_path_measurable _ hx (by
    intro t
    exact (hX.adapted P F _ ((min_le_left b t).trans_lt hb)).mono (hle _) le_rfl)).norm
  have hR2 := continuous_m2_path_square_moment P F hF hle _ hM2
  change Integrable (fun ω => R ω^2) P ∧ (∫ ω, R ω^2 ∂P) ≤ 4*(∫ ω, Y (min b ⊤) ω^2 ∂P) at hR2
  simp only [min_top_right] at hR2
  have hVm : Measurable (fun ω => (ε+A b ω)^(p/2)) :=
    (Real.continuous_rpow_const (by positivity : 0 ≤ p/2)).measurable.comp
      (measurable_const.add ((hA.adapted P F hX hX b hb).mono (hle b) le_rfl))
  have hVi : Integrable (fun ω => (ε+A b ω)^(p/2)) P := by
    apply (integrable_const ((ε+K)^(p/2))).mono' hVm.aestronglyMeasurable
    filter_upwards [hbound] with ω hω
    rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (by linarith [hAp ω]) _)]
    exact Real.rpow_le_rpow (by linarith [hAp ω]) (by linarith) (by positivity)
  have hh := fractional_moment_holder P (fun ω => R ω^2) (fun ω => (ε+A b ω)^(p/2))
    hR2.1 hVi (fun ω => sq_nonneg _) (fun ω => Real.rpow_nonneg (by linarith [hAp ω]) _)
    (p/2) (by linarith) (by linarith)
  have hSbound : ∀ᵐ ω ∂P, S ω ≤ 2*R ω*(ε+A b ω)^((2-p)/4) := by
    filter_upwards [hpath] with ω hω
    apply (ContinuousMap.norm_le _ (mul_nonneg (mul_nonneg (by norm_num) (norm_nonneg _))
      (Real.rpow_nonneg (by linarith [hAp ω]) _))).mpr
    intro t
    have hRb s (hs : s ≤ b) : |Y s ω| ≤ R ω := by
      have hbnd := (continuousPath (fun t ω => Y (min b t) ω) hM2.path ω).norm_coe_le_norm s
      simpa only [R,continuousPath,ContinuousMap.coe_mk,min_eq_right hs,Real.norm_eq_abs] using hbnd
    simpa only [R,continuousPath,ContinuousMap.coe_mk,Real.norm_eq_abs] using
      hω b hb (R ω) (norm_nonneg _) hRb (min b t) (min_le_left b t)
  have hdom : ∀ᵐ ω ∂P, S ω^p ≤ 2^p*((R ω^2)^(p/2)*((ε+A b ω)^(p/2))^(1-p/2)) := by
    filter_upwards [hSbound] with ω hω
    have hr : 0 ≤ R ω := norm_nonneg _
    have hq : 0 ≤ ε+A b ω := by linarith [hAp ω]
    have he : (2*R ω*(ε+A b ω)^((2-p)/4))^p =
        2^p*((R ω^2)^(p/2)*((ε+A b ω)^(p/2))^(1-p/2)) := by
      rw [Real.mul_rpow (mul_nonneg (by norm_num) hr) (Real.rpow_nonneg hq _),
        Real.mul_rpow (by norm_num) hr,← Real.rpow_mul hq,
        ← Real.rpow_two,← Real.rpow_mul hr,← Real.rpow_mul hq]
      have e1 : (2:ℝ)*(p/2) = p := by ring
      have e2 : ((2-p)/4)*p = (p/2)*(1-p/2) := by ring
      rw [e1,e2]
      ring
    exact (Real.rpow_le_rpow (norm_nonneg _) hω hp.le).trans_eq he
  have hSi : Integrable (fun ω => S ω^p) P := by
    apply (hh.1.const_mul (2^p)).mono'
      ((Real.continuous_rpow_const hp.le).measurable.comp hSm).aestronglyMeasurable
    filter_upwards [hdom] with ω hω
    change ‖S ω^p‖ ≤ _
    rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (show 0 ≤ S ω from norm_nonneg _) p)]
    exact hω
  refine ⟨hx,hSi,?_⟩
  change (∫ ω, S ω^p ∂P) ≤ _
  calc
    _ ≤ ∫ ω, 2^p*((R ω^2)^(p/2)*((ε+A b ω)^(p/2))^(1-p/2)) ∂P :=
      integral_mono_ae hSi (hh.1.const_mul _) hdom
    _ = 2^p*(∫ ω, (R ω^2)^(p/2)*((ε+A b ω)^(p/2))^(1-p/2) ∂P) := integral_const_mul _ _
    _ ≤ 2^p*((∫ ω, R ω^2 ∂P)^(p/2)*(∫ ω, (ε+A b ω)^(p/2) ∂P)^(1-p/2)) :=
      mul_le_mul_of_nonneg_left hh.2 (by positivity)
    _ ≤ _ := by
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (integral_nonneg (fun ω =>
        Real.rpow_nonneg (by linarith [hAp ω]) _)) _)
      apply Real.rpow_le_rpow (integral_nonneg (fun ω => sq_nonneg _)) _ (by positivity)
      rw [henergy] at hR2
      nlinarith [hR2.2]

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.regularized_bdg_upper_moment
