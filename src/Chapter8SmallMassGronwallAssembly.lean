import Chapter8RandomPositionMoment

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter8
open Asakura.FullAudit
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

/-- The first Gronwall step has constants independent of the mass. The
input inequality is obtained from the actual position representation by
random_position_moment_inequality. -/
theorem small_mass_position_uniform_bound (u : ℝ → ℝ → ℝ) (T CA CN L G : ℝ)
    (hT : 0≤T) (hCA : 0≤CA) (hCN : 0≤CN) (hG : 0≤G)
    (hc : ∀ m,0<m → m≤1 → ContinuousOn (u m) (Icc 0 T))
    (hn : ∀ m,0<m → m≤1 → ∀ t∈Icc 0 T,0≤u m t)
    (hi : ∀ m,0<m → m≤1 → ∀ t∈Icc 0 T,
      u m t≤3*(CA+CN)+3*t*L^2*G*(t+∫ s in 0..t,u m s)) :
    ∀ m,0<m → m≤1 → ∀ t∈Icc 0 T,
      u m t≤(3*(CA+CN)+3*T^2*L^2*G)*Real.exp ((3*T*L^2*G+1)*T) := by
  let A := 3*(CA+CN)+3*T^2*L^2*G
  let B := 3*T*L^2*G+1
  have hA : 0≤A := by dsimp [A]; positivity
  have hB : 0<B := by dsimp [B]; positivity
  intro m hm hm1 t ht
  have hineq s (hs : s∈Icc 0 T) : u m s≤A+B*∫ r in 0..s,u m r := by
    have hint : 0≤∫ r in 0..s,u m r := intervalIntegral.integral_nonneg hs.1
      (fun r hr => hn m hm hm1 r ⟨hr.1,hr.2.trans hs.2⟩)
    have hcoef : 3*s*L^2*G≤3*T*L^2*G := by gcongr <;> first | exact hs.1 | exact hs.2
    have hconst : 3*s^2*L^2*G≤3*T^2*L^2*G := by gcongr <;> first | exact hs.1 | exact hs.2
    have hprod := mul_le_mul_of_nonneg_right hcoef hint
    have hh := hi m hm hm1 s hs
    dsimp only [A,B]
    nlinarith
  have hh := ch4_gronwall_written (u m) A B T hT (hc m hm hm1) hB hineq t ht
  exact hh.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 hB.le)) hA)

/-- From the O(m) mean-square remainder the second Gronwall step gives
uniform convergence on the full compact time interval, expressed by its supremum. -/
theorem small_mass_error_sup_limit (u : ℝ → ℝ → ℝ) (T C B : ℝ)
    (hT : 0≤T) (hC : 0≤C) (hB : 0<B)
    (hc : ∀ m,0<m → m≤1 → ContinuousOn (u m) (Icc 0 T))
    (hn : ∀ m,0<m → m≤1 → ∀ t∈Icc 0 T,0≤u m t)
    (hi : ∀ m,0<m → m≤1 → ∀ t∈Icc 0 T,u m t≤C*m+B*∫ s in 0..t,u m s) :
    (∀ m,0<m → m≤1 → ∀ t∈Icc 0 T,u m t≤C*Real.exp (B*T)*m) ∧
      Tendsto (fun m => sSup (u m '' Icc 0 T)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hb m (hm : 0<m) (hm1 : m≤1) t (ht : t∈Icc 0 T) : u m t≤C*Real.exp (B*T)*m := by
    have hh := ch4_gronwall_written (u m) (C*m) B T hT (hc m hm hm1) hB (hi m hm hm1) t ht
    have hmono := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 hB.le)
    have hx := hh.trans (mul_le_mul_of_nonneg_left hmono (mul_nonneg hC hm.le))
    convert hx using 1 <;> ring
  refine ⟨hb,?_⟩
  have he : ∀ᶠ m : ℝ in 𝓝[>] 0,0<m ∧ m≤1 := by
    filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds (eventually_lt_nhds (by norm_num : (0:ℝ)<1))] with m hm hm1
    exact ⟨hm,hm1.le⟩
  apply squeeze_zero'
  · filter_upwards [he] with m hm
    have hbd : BddAbove (u m '' Icc 0 T) := ⟨C*Real.exp (B*T)*m,by
      rintro _ ⟨t,ht,rfl⟩
      exact hb m hm.1 hm.2 t ht⟩
    exact (hn m hm.1 hm.2 0 ⟨le_rfl,hT⟩).trans (le_csSup hbd ⟨0,⟨le_rfl,hT⟩,rfl⟩)
  · filter_upwards [he] with m hm
    apply csSup_le
    · exact ⟨u m 0,0,⟨le_rfl,hT⟩,rfl⟩
    · rintro _ ⟨t,ht,rfl⟩
      exact hb m hm.1 hm.2 t ht
  · simpa using (tendsto_const_nhds.mul (show Tendsto (fun m : ℝ => m) (𝓝[>] 0) (𝓝 0) from nhdsWithin_le_nhds) :
      Tendsto (fun m : ℝ => (C*Real.exp (B*T))*m) (𝓝[>] 0) (𝓝 ((C*Real.exp (B*T))*0)))
end Asakura.Chapter8
