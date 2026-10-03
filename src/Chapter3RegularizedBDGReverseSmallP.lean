import Chapter3DecreasingPowerPathBound
import Chapter3DecreasingPowerEnergy
import Chapter3MomentHolder

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false

/-- The complete regularized reverse small-p estimate, before alpha tends to zero. -/
theorem regularized_bdg_reverse_small_p
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X A K : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X) (hA : LocalCovarianceWitness P F X X A)
    (hAm : ∀ ω, MonotoneOn (fun t => A t ω) (Iio ⊤))
    (hAc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => A s ω) t)
    (hA0 : ∀ ω, A ⊥ ω = 0)
    (hKa : ∀ t, t < ⊤ → Measurable[F t] (K t))
    (hKc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => K s ω) t)
    (hKm : ∀ ω, MonotoneOn (fun t => K t ω) (Iio ⊤))
    (hKp : ∀ ω t, t < ⊤ → 0 ≤ K t ω)
    (hK0 : ∀ᵐ ω ∂P, K ⊥ ω = 0)
    (hXK : ∀ ω t, t < ⊤ → |X t ω| ≤ K t ω)
    (α p : ℝ) (hα : 0 < α) (hp : 0 < p) (hp2 : p < 2)
    (b : ClosedTime T) (hb : b < ⊤) (M : ℝ) (hM : 0 ≤ M)
    (hAb : ∀ᵐ ω ∂P, A b ω ≤ M)
    (L : ℝ) (hL : 0 ≤ L) (hKb : ∀ᵐ ω ∂P, K b ω ≤ L) :
    (∫ ω, A b ω^(p/2) ∂P) ≤ (2/p)^p*(∫ ω, (α+K b ω)^p ∂P) := by
  obtain ⟨Y,hY,hy,hpath⟩ := decreasing_power_ito_path_bound P hT F hF hle hnull X K hX
    hKa hKc hKm hKp hK0 hXK α p hα hp hp2 b hb
  obtain ⟨B,hB,hM2,hBi,henergy,hlower⟩ := decreasing_power_ito_energy_bound P hT F hF hle hnull X A K Y
    hX hA hAm hAc hA0 hKa hKc hKm hKp α p hα hp hp2 hY hy b hb M hM hAb
  have hAp ω : 0 ≤ A b ω := by
    rw [← hA0 ω]
    exact hAm ω hT hb bot_le
  have hbase ω : 0 < α+K b ω := by linarith [hKp ω b hb]
  let U := fun ω => A b ω*(α+K b ω)^(p-2)
  let V := fun ω => (α+K b ω)^p
  have hUp ω : 0 ≤ U ω := mul_nonneg (hAp ω) (Real.rpow_nonneg (hbase ω).le _)
  have hVp ω : 0 ≤ V ω := Real.rpow_nonneg (hbase ω).le _
  have hreg := shifted_power_process_regularity F K hKa hKc hKp α (p-2) hα
  have hUm : Measurable U :=
    ((hA.adapted P F hX hX b hb).mul (hreg.1 b hb)).mono (hle b) le_rfl
  have hVm : Measurable V := (Real.continuous_rpow_const hp.le).measurable.comp
    (measurable_const.add ((hKa b hb).mono (hle b) le_rfl))
  have hUi : Integrable U P := by
    apply (integrable_const (M*α^(p-2))).mono' hUm.aestronglyMeasurable
    filter_upwards [hAb] with ω hω
    rw [Real.norm_eq_abs,abs_of_nonneg (hUp ω)]
    exact mul_le_mul hω (Real.rpow_le_rpow_of_nonpos hα
      (by linarith [hKp ω b hb]) (by linarith))
      (Real.rpow_nonneg (hbase ω).le _) hM
  have hVi : Integrable V P := by
    apply (integrable_const ((α+L)^p)).mono' hVm.aestronglyMeasurable
    filter_upwards [hKb] with ω hω
    rw [Real.norm_eq_abs,abs_of_nonneg (hVp ω)]
    exact Real.rpow_le_rpow (hbase ω).le (by linarith) hp.le
  have hh := fractional_moment_holder P U V hUi hVi hUp hVp (p/2) (by linarith) (by linarith)
  have hidentity ω : U ω^(p/2)*V ω^(1-p/2) = A b ω^(p/2) := by
    dsimp [U,V]
    rw [Real.mul_rpow (hAp ω) (Real.rpow_nonneg (hbase ω).le _),
      ← Real.rpow_mul (hbase ω).le,← Real.rpow_mul (hbase ω).le,mul_assoc,← Real.rpow_add (hbase ω)]
    have he : (p-2)*(p/2)+p*(1-p/2) = 0 := by ring
    rw [he,Real.rpow_zero,mul_one]
  have hYi : Integrable (fun ω => Y b ω^2) P := by
    simpa only [min_top_right] using
      (memLp_two_iff_integrable_sq (hM2.moment ⊤).aestronglyMeasurable).mp (hM2.moment ⊤)
  have hYupper : ∀ᵐ ω ∂P, Y b ω^2 ≤ (2/p)^2*V ω := by
    filter_upwards [hpath] with ω hω
    have hc : 0 ≤ 2/p-1 := by apply sub_nonneg.mpr; exact (le_div_iff₀ hp).mpr (by linarith)
    have hu : |Y b ω| ≤ (2/p)*(α+K b ω)^(p/2) :=
      hω.trans (sub_le_self _ (mul_nonneg hc (Real.rpow_nonneg hα.le _)))
    have hs := (sq_le_sq₀ (abs_nonneg (Y b ω))
      (mul_nonneg (by positivity : 0 ≤ 2/p) (Real.rpow_nonneg (hbase ω).le (p/2)))).mpr hu
    rw [sq_abs,mul_pow,← Real.rpow_two ((α+K b ω)^(p/2)),← Real.rpow_mul (hbase ω).le] at hs
    have he : (p/2)*2 = p := by ring
    simpa only [he,V] using hs
  have hUle : (∫ ω, U ω ∂P) ≤ (2/p)^2*(∫ ω, V ω ∂P) := by
    calc
      _ ≤ ∫ ω, B b ω ∂P := integral_mono_ae hUi hBi (hlower.mono (fun ω hω => by simpa only [U,mul_comm] using hω))
      _ = ∫ ω, Y b ω^2 ∂P := henergy
      _ ≤ ∫ ω, (2/p)^2*V ω ∂P := integral_mono_ae hYi (hVi.const_mul _) hYupper
      _ = _ := integral_const_mul _ _
  have hUpi : 0 ≤ ∫ ω, U ω ∂P := integral_nonneg hUp
  have hVpi : 0 ≤ ∫ ω, V ω ∂P := integral_nonneg hVp
  have hholder : (∫ ω, A b ω^(p/2) ∂P) ≤
      (∫ ω, U ω ∂P)^(p/2)*(∫ ω, V ω ∂P)^(1-p/2) := by simpa only [hidentity] using hh.2
  calc
    _ ≤ ((2/p)^2*(∫ ω, V ω ∂P))^(p/2)*(∫ ω, V ω ∂P)^(1-p/2) :=
      hholder.trans (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hUpi hUle (by positivity))
        (Real.rpow_nonneg hVpi _))
    _ = _ := by
      rw [Real.mul_rpow (sq_nonneg _) hVpi,← Real.rpow_two (2/p),
        ← Real.rpow_mul (by positivity : 0 ≤ 2/p),mul_assoc,
        ← Real.rpow_add_of_nonneg hVpi (by positivity : 0 ≤ p/2) (by linarith : 0 ≤ 1-p/2)]
      have he1 : (2:ℝ)*(p/2) = p := by ring
      have he2 : p/2+(1-p/2) = 1 := by ring
      rw [he1,he2,Real.rpow_one]

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.regularized_bdg_reverse_small_p
