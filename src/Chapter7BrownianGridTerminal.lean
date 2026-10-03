import Chapter7BrownianCellTerminal

open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- Identification at T for any actual integral of the grid integrand. -/
theorem brownian_grid_terminal_identity {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (K : Fin d → Fin d → ℝ) (hK : ∀ i j,K i j=K j i)
    (T a : ℝ) (hT : 0<T) (n : ℕ) (hn : 0<n)
    (N : Fin d → HalfClosedTime → Ω → ℝ) (hN : ∀ i,LocalMProcessWitness P B.F (N i))
    (hNI : ∀ i,ItoCovarianceFormula P B.F (B.W i)
      (fun z => a*brownianGridIntegrand B (K i) (T/n) (n+1) z) (N i)) :
    ∀ᵐ w ∂P,2*(∑ i,N i (realTimeClamp T) w)=a*∑ k : Fin n,
      ((∑ i,∑ j,K i j*(B.W i (realTimeClamp (((k:ℝ)+1)*(T/n))) w-B.W i (realTimeClamp ((k:ℝ)*(T/n))) w)*
        (B.W j (realTimeClamp (((k:ℝ)+1)*(T/n))) w-B.W j (realTimeClamp ((k:ℝ)*(T/n))) w))-(T/n)*(∑ i,K i i)) := by
  have htop : (0:EReal)<⊤ := by simp
  have hnR : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  let h := T/(n:ℝ)
  have hh : 0≤h := div_nonneg hT.le (Nat.cast_nonneg _)
  let s := fun k : Fin (n+1) => (k:ℝ)*h
  let e := fun k : Fin (n+1) => ((k:ℝ)+1)*h
  have hs k : 0≤s k := mul_nonneg (by positivity) hh
  have hse k : s k≤e k := by dsimp only [s,e]; nlinarith
  have hex k := brownian_cell_terminal P B K hK (s k) (e k) (max (e k) T) (hs k) (hse k) (le_max_left _ _)
  choose Z hZ hZi hZzero hZend using hex
  let V := fun i t w => a*∑ k,Z k i t w
  have hV i : LocalMProcessWitness P B.F (V i) :=
    (local_martingale_finset_sum P htop B.F B.mono B.le univ (fun k => Z k i) (fun k _ => hZ k i)).smul P B.F a
  have hVI i : ItoCovarianceFormula P B.F (B.W i)
      (fun z => a*brownianGridIntegrand B (K i) h (n+1) z) (V i) := by
    have hi := finite_ito_sum P htop B.F B.mono B.le B.null (B.W i) (B.martingale i) univ
      (fun k => brownianCellIntegrand B (K i) (s k) (e k)) (fun k => Z k i) (fun k _ => hZi k i)
    have ha := hi.add_smul P B.F B.mono B.le _ _ _ _ _ hi (a-1)
    convert ha using 1 <;> ext z w <;> dsimp only [brownianGridIntegrand,V,s,e] <;> ring
  have heq i := ItoCovarianceFormula.unique P htop B.F B.mono B.le B.null (B.W i) (N i) (V i) _
    (B.martingale i) (hN i) (hV i) (hNI i) (hVI i)
  have hNall : ∀ᵐ w ∂P,∀ i,∀ t,t<⊤ → N i t w=V i t w := ae_all_iff.mpr heq
  have hlast : s (Fin.last n)=T := by dsimp [s,h]; field_simp
  have hzero : ∀ᵐ w ∂P,∀ i,Z (Fin.last n) i (realTimeClamp T) w=0 := by
    apply ae_all_iff.mpr
    intro i
    exact hZzero (Fin.last n) i T hT.le (by rw [hlast])
  have hcells : ∀ᵐ w ∂P,∀ k,Z k = Z k ∧
      2*(∑ i,Z k i (realTimeClamp (max (e k) T)) w)=
        (∑ i,∑ j,K i j*(B.W i (realTimeClamp (e k)) w-B.W i (realTimeClamp (s k)) w)*
          (B.W j (realTimeClamp (e k)) w-B.W j (realTimeClamp (s k)) w))-(e k-s k)*(∑ i,K i i) := by
    apply ae_all_iff.mpr
    intro k
    exact (hZend k).mono (fun w hw => ⟨rfl,hw⟩)
  filter_upwards [hNall,hzero,hcells] with w hw hz hc
  have hfin (k : Fin n) : e k.castSucc≤T := by
    have hk : (k:ℝ)+1≤n := by exact_mod_cast (Nat.succ_le_of_lt k.isLt)
    calc
      _ ≤ (n:ℝ)*h := mul_le_mul_of_nonneg_right hk hh
      _ = T := by dsimp [h]; field_simp
  have hterm (k : Fin n) := (hc k.castSucc).2
  have hlen k : e k-s k=h := by dsimp [e,s]; ring
  have hcalc : (∑ k : Fin (n+1),2*(∑ i,Z k i (realTimeClamp T) w))=
      ∑ k : Fin n,((∑ i,∑ j,K i j*(B.W i (realTimeClamp (e k.castSucc)) w-B.W i (realTimeClamp (s k.castSucc)) w)*
        (B.W j (realTimeClamp (e k.castSucc)) w-B.W j (realTimeClamp (s k.castSucc)) w))-h*(∑ i,K i i)) := by
    rw [Fin.sum_univ_castSucc]
    simp only [hz,sum_const_zero,mul_zero,add_zero]
    apply sum_congr rfl
    intro k _
    simpa only [max_eq_right (hfin k),hlen] using hterm k
  simp only [hw _ _ (real_time_below T hT.le (EReal.coe_lt_top _)),V]
  calc
    _ = a*(∑ k : Fin (n+1),2*(∑ i,Z k i (realTimeClamp T) w)) := by
      rw [← mul_sum,← mul_sum,sum_comm]
      ring
    _ = _ := by rw [hcalc]; rfl

end Asakura.Chapter7
