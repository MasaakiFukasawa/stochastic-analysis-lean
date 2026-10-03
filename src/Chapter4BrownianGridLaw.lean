import Chapter4NoiseGridAlgebra
import Chapter4SDERestart

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false

/-- The entire finite noise grid is independent of the initial sigma
algebra. Its law is determined by the time step alone, including all
coordinates jointly, by Levy's calculation and C5. -/
theorem brownian_finite_grid_law
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {d : ℕ}
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (W : Fin d → HalfClosedTime → Ω → ℝ)
    (C : Fin d → Fin d → HalfClosedTime → Ω → ℝ)
    (hW : ∀ j,LocalMProcessWitness P F (W j))
    (hC : ∀ j k,LocalCovarianceWitness P F (W j) (W k) (C j k))
    (hclock : ∀ j k w (r : ℝ),0≤r → C j k (realTimeClamp r) w=if j=k then r else 0)
    (h : ℝ) (hh : 0≤h) (n : ℕ) :
    let Z := finiteNoiseGrid (fun j r => W j (realTimeClamp r)) h n
    Measurable[m] Z ∧ charFunDual (@Measure.map Ω _ m _ Z P)=gridNoiseCharacteristic n d h ∧
      Indep (MeasurableSpace.comap Z inferInstance) (F ⊥) P := by
  classical
  letI : MeasurableSpace Ω := m
  dsimp only
  let Z := finiteNoiseGrid (fun j r => W j (realTimeClamp r)) h n
  let G := fun k : ℕ => F (realTimeClamp ((k:ℝ)*h))
  have hGm : Monotone G := fun k l hkl => hF (real_time_clamp_mono (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hkl) hh))
  have hGl k : G k≤m := hle _
  have htimes (k : ℕ) : 0≤(k:ℝ)*h := mul_nonneg (Nat.cast_nonneg k) hh
  have hWa k j : Measurable[G k] (W j (realTimeClamp ((k:ℝ)*h))) :=
    (hW j).adapted P F _ (real_time_below _ (htimes k) (EReal.coe_lt_top _))
  have hz : realTimeClamp (T:=⊤) 0=⊥ := by
    apply Subtype.ext
    exact real_time_clamp_eq 0 le_rfl le_top
  have hG0 : G 0=F ⊥ := by dsimp only [G];simp only [Nat.cast_zero,zero_mul,hz]
  have hZm : Measurable[m] Z := by
    apply measurable_pi_iff.mpr
    intro k
    apply measurable_pi_iff.mpr
    intro j
    have hm := ((hWa (k.val+1) j).mono (hGl _) le_rfl).sub ((hWa k.val j).mono (hGl _) le_rfl)
    change Measurable[m] (fun w => W j (realTimeClamp (((k.val+1:ℕ):ℝ)*h)) w-W j (realTimeClamp ((k.val:ℝ)*h)) w) at hm
    simpa only [Z,finiteNoiseGrid,Nat.cast_add,Nat.cast_one] using hm
  refine ⟨hZm,?_⟩
  apply independence_of_constant_conditional_characteristic P (F ⊥) (hle ⊥) Z hZm (gridNoiseCharacteristic n d h)
  intro L
  let u := fun k : ℕ => if hk : k<n then fun j => L (Pi.single ⟨k,hk⟩ (Pi.single j 1)) else fun _ => 0
  let Q := fun k w => ∑ j,u k j*(W j (realTimeClamp (((k:ℝ)+1)*h)) w-W j (realTimeClamp ((k:ℝ)*h)) w)
  let K := fun k => Complex.exp (-(h:ℂ)*((∑ j,(u k j)^2:ℝ):ℂ)/2)
  have hQa k : Measurable[G (k+1)] (Q k) := by
    letI : MeasurableSpace Ω := G (k+1)
    apply Finset.measurable_sum
    intro j _
    have hstart := (hWa k j).mono (hGm (Nat.le_succ k)) le_rfl
    have hend : Measurable[G (k+1)] (W j (realTimeClamp (((k:ℝ)+1)*h))) := by
      simpa only [Nat.cast_add,Nat.cast_one] using hWa (k+1) j
    exact (hend.sub hstart).const_mul _
  have hchar k : P[(fun w => Complex.exp ((Q k w:ℂ)*Complex.I)) | G k]=ᵐ[P] fun _ => K k := by
    have hks : (k:ℝ)*h≤((k:ℝ)+1)*h := by nlinarith
    have hr0 : 0≤((k:ℝ)+1)*h := by positivity
    have he := vector_levy_conditional_characteristic P (EReal.coe_lt_top 0) F hF hle hnull W C hW hC
      (fun j l w r hr _ => hclock j l w r hr) (((k:ℝ)+1)*h) hr0 (EReal.coe_lt_top _)
      ((k:ℝ)*h) ⟨htimes k,hks⟩ (u k)
    have hd : ((k:ℝ)+1)*h-(k:ℝ)*h=h := by ring
    simpa only [hd] using he
  have he := conditional_characteristic_product P G hGm hGl Q hQa K hchar n
  rw [hG0] at he
  have hsum w : (∑ k∈Finset.range n,Q k w)=L (Z w) := by
    rw [← Fin.sum_univ_eq_sum_range,dual_matrix_expansion]
    apply Finset.sum_congr rfl
    intro k _
    dsimp only [Q,Z,finiteNoiseGrid]
    have huk : u k.val=fun j => L (Pi.single k (Pi.single j 1)) := by simp only [u,dif_pos k.isLt]
    rw [huk]
  have hprod : (∏ k∈Finset.range n,K k)=gridNoiseCharacteristic n d h L := by
    rw [← Fin.prod_univ_eq_prod_range]
    apply Finset.prod_congr rfl
    intro k _
    dsimp only [K,gridNoiseCharacteristic]
    have huk : u k.val=fun j => L (Pi.single k (Pi.single j 1)) := by simp only [u,dif_pos k.isLt]
    rw [huk]
  simpa only [hsum,hprod] using he

end Asakura.Chapter4
