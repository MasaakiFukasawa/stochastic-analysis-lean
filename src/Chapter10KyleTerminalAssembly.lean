import Chapter10KyleL2Terminal
import Chapter10KylePriceExtension

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.Chapter10
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- The actual order integral supplies the pathwise endpoint, and the actual
equilibrium variance identifies it with the asset value by Fatou. -/
theorem kyle_terminal_price {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (p B : ℝ → Ω → ℝ) (V : Ω → ℝ) (p0 l σ S0 T : ℝ)
    (hT : 0<T) (hl : 0<l) (hS : 0≤S0)
    (hm : Measurable (fun z : ℝ × Ω => p z.1 z.2-V z.2))
    (hV : AEStronglyMeasurable V P)
    (h2 : ∀ t,MemLp (fun w => p t w-V w) 2 P)
    (hvar : ∀ t∈Ioo 0 T,(∫ w,(p t w-V w)^2 ∂P)=S0*(T-t)/T)
    (hB : ∀ᵐ w ∂P,ContinuousOn (fun t => B t w) (Icc 0 T))
    (hp : ∀ᵐ w ∂P,∀ t∈Ioo 0 T,
      p t w=p0+l*((∫ s in 0..t,(V w-p s w)/(l*(T-s)))+σ*B t w))
    (hendpoint : AEStronglyMeasurable
      (fun w => p0+l*((∫ s in 0..T,(V w-p s w)/(l*(T-s)))+σ*B T w)) P) :
    (fun w => p0+l*((∫ s in 0..T,(V w-p s w)/(l*(T-s)))+σ*B T w)) =ᵐ[P] V := by
  have hnegm : Measurable (fun z : ℝ × Ω => V z.2-p z.1 z.2) := by
    have hh : Measurable (fun z : ℝ × Ω => -(p z.1 z.2-V z.2)) := hm.neg
    simpa only [neg_sub] using hh
  have hneg2 t : MemLp (fun w => V w-p t w) 2 P := by
    have hh : MemLp (fun w => -(p t w-V w)) 2 P := (h2 t).neg
    simpa only [neg_sub] using hh
  have hnegvar t (ht : t∈Ioo 0 T) : (∫ w,(V w-p t w)^2 ∂P)=S0*(T-t)/T := by
    convert hvar t ht using 1
    congr 1
    funext w
    ring
  obtain ⟨_,hα⟩ := kyle_absolute_orders_integrable P (fun t w => V w-p t w)
    hnegm hneg2 S0 T l hS hT hl hnegvar
  have hpath : ∀ᵐ w ∂P,Tendsto (fun t => p t w) (𝓝[<] T)
      (𝓝 (p0+l*((∫ s in 0..T,(V w-p s w)/(l*(T-s)))+σ*B T w))) := by
    filter_upwards [hα,hB,hp] with w hw hb hh
    exact kyle_price_continuous_extension _ _ _ T p0 l σ hT hw hb hh
  let b := fun n : ℕ => T-(T-T/2)/((n:ℝ)+1)
  have hb n : b n∈Ioo 0 T := by
    have hd0 : 0<(n:ℝ)+1 := by positivity
    have hd1 : 1≤(n:ℝ)+1 := by have h := Nat.cast_nonneg (α := ℝ) n;linarith
    have hf := div_le_self (show 0≤T-T/2 by linarith) hd1
    exact ⟨by dsimp only [b];linarith,sub_lt_self T (div_pos (by linarith) hd0)⟩
  have hbT : Tendsto b atTop (𝓝[<] T) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_,Eventually.of_forall fun n => (hb n).2⟩
    have hh := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (T-T/2)
    convert (tendsto_const_nhds (x := T)).sub hh using 1 <;> simp [b,div_eq_mul_inv]
  apply terminal_identification P (fun n => p (b n)) _ V
    (fun n => by
      have hh : AEStronglyMeasurable (fun w => (p (b n) w-V w)+V w) P :=
        (h2 (b n)).aestronglyMeasurable.add hV
      simpa only [sub_add_cancel] using hh)
    hendpoint hV
  · exact hpath.mono fun w hw => hw.comp hbT
  · exact (kyle_error_L2_terminal P (fun t w => p t w-V w) S0 T hT
      (fun t _ => h2 t) hvar).comp hbT

end Asakura.Chapter10
