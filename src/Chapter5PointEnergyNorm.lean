import Chapter5FiniteEnergyNorm
import Chapter5PerturbationTimeSup

open MeasureTheory Set Filter Asymptotics
open scoped Topology ENNReal
namespace Asakura.Chapter5
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false

noncomputable def pointEnergyNorm
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (H : Ω → ℝ) : ℝ :=
  Real.sqrt (∫ w,H w^2 ∂P)

lemma pointEnergyNorm_nonneg
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (H : Ω → ℝ) : 0≤pointEnergyNorm P H := Real.sqrt_nonneg _

lemma pointEnergyNorm_sub_comm
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (H G : Ω → ℝ) :
    pointEnergyNorm P (fun w => H w-G w)=pointEnergyNorm P (fun w => G w-H w) := by
  unfold pointEnergyNorm
  simp_rw [sub_sq_comm (H _) (G _)]

lemma point_norm_from_weighted_estimate
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (H : Ω → ℝ) (β t ε mu D : ℝ) (hβ : 0≤β) (ht : 0≤t) (hmu : 0<mu) (hD : 0≤D)
    (hh : (∫ w,Real.exp (β*t)*H w^2 ∂P)≤ε^2*D^2/mu^2) :
    pointEnergyNorm P H≤|ε|/mu*D := by
  have hi : 0≤∫ w,H w^2 ∂P := integral_nonneg (fun _ => sq_nonneg _)
  have hs : (pointEnergyNorm P H)^2=∫ w,H w^2 ∂P := Real.sq_sqrt hi
  rw [integral_const_mul] at hh
  have hex : 1≤Real.exp (β*t) := Real.one_le_exp_iff.mpr (mul_nonneg hβ ht)
  have hsmall : (pointEnergyNorm P H)^2≤ε^2*D^2/mu^2 := by
    rw [hs]
    have hiw : (∫ w,H w^2 ∂P)≤Real.exp (β*t)*(∫ w,H w^2 ∂P) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hex hi
    exact hiw.trans hh
  have hsR : (|ε|/mu*D)^2=ε^2*D^2/mu^2 := by rw [mul_pow,div_pow,sq_abs]; ring
  exact (sq_le_sq₀ (pointEnergyNorm_nonneg P H) (by positivity)).mp (hsmall.trans_eq hsR.symm)

/-- An eventual bound uniform over the time parameter yields a bound
for the actual supremum, and multiplies the perturbation order by epsilon. -/
theorem uniform_time_bound_bigO {ι : Type*} [Nonempty ι]
    (U : ι → ℝ → ℝ) (E : ℝ → ℝ) (K : ℝ) (hK : 0≤K) (k : ℕ)
    (hU : ∀ i ε,0≤U i ε) (hE : ∀ ε,0≤E ε)
    (hb : ∀ᶠ ε in 𝓝 0,∀ i,U i ε≤K*|ε| *E ε)
    (he : E =O[𝓝 0] (fun ε : ℝ => |ε|^k)) :
    (fun ε => ⨆ i,U i ε) =O[𝓝 0] (fun ε : ℝ => |ε|^(k+1)) := by
  obtain ⟨C,hC,hc⟩ := he.exists_nonneg
  apply IsBigO.of_bound (K*C)
  filter_upwards [hb,hc.bound] with ε hbe hce
  have hEbound : E ε≤C*|ε|^k := by simpa only [Real.norm_eq_abs,abs_of_nonneg (hE ε),abs_pow,abs_abs] using hce
  have hall i : U i ε≤K*C*|ε|^(k+1) := by
    calc
      _ ≤ K*|ε| *E ε := hbe i
      _ ≤ K*|ε| *(C*|ε|^k) := mul_le_mul_of_nonneg_left hEbound (by positivity)
      _ = _ := by ring
  have hbd : BddAbove (range (fun i => U i ε)) := ⟨K*C*|ε|^(k+1),by rintro x ⟨i,rfl⟩; exact hall i⟩
  have h0 : 0≤⨆ i,U i ε := (hU (Classical.choice inferInstance) ε).trans (le_ciSup hbd _)
  simpa only [Real.norm_eq_abs,abs_of_nonneg h0,abs_pow,abs_abs] using ciSup_le hall

end Asakura.Chapter5
