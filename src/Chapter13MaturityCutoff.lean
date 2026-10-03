import Chapter13MarketSupport

open MeasureTheory Set
namespace Asakura.Chapter13
set_option maxHeartbeats 1800000

/-- Removing the already matured part of a maturity interval gives the
max-endpoint expression used in both Cheyette and the market model. -/
theorem maturity_cutoff_integral {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g:ℝ → E) (a b t:ℝ) (hab:a≤b) :
    (∫s in a..b,if t≤s then g s else 0)=∫s in max a t..max b t,g s := by
  have he:(∫s in a..b,if t≤s then g s else 0)=(∫s in a..b,(Ioi t).indicator g s) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [volume.ae_ne t] with s hst _
    by_cases h:t<s
    · simp [h,h.le]
    · have hh:¬t≤s := fun hx => h (lt_of_le_of_ne hx (Ne.symm hst))
      simp [h,hh]
  rw [he,intervalIntegral.integral_of_le hab,integral_indicator measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi]
  by_cases htb:t≤b
  · have hset:Ioi t ∩ Ioc a b=Ioc (max a t) b := by
      ext s
      simp only [mem_inter_iff,mem_Ioi,mem_Ioc,max_lt_iff]
      tauto
    rw [hset,max_eq_left htb,intervalIntegral.integral_of_le (max_le hab htb)]
  · have hbt:b≤t := (le_of_not_ge htb)
    have hset:Ioi t ∩ Ioc a b=∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro s ⟨hs,_,hsb⟩
      exact (not_lt_of_ge (hsb.trans hbt)) hs
    rw [hset,Measure.restrict_empty,integral_zero_measure,max_eq_right (hab.trans hbt),max_eq_right hbt,
      intervalIntegral.integral_same]
end Asakura.Chapter13
#print axioms Asakura.Chapter13.maturity_cutoff_integral
