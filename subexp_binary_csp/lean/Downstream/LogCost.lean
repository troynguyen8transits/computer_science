import Downstream.NumericOverheads
import CliqueLevelsStatement

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! Uniform logarithmic absorption, including the clique theorem's polynomial
factor and natural-ceiling budget. All domain-bit lengths b>=1 are allowed. -/

namespace CSPConsequence.LogCost

noncomputable def scale (k b : ℝ) : ℝ := b*k/Real.sqrt (Real.log k)
noncomputable def polyCoefficient (Δ : ℝ) : ℝ := Real.log 17+Real.log Δ+6

theorem scale_pos {k b : ℝ} (hk : 2 ≤ k) (hb : 1 ≤ b) : 0 < scale k b := by
  unfold scale
  exact div_pos (by positivity) (Real.sqrt_pos.mpr (Real.log_pos (by linarith)))

theorem one_le_scale {k b : ℝ} (hk : 2 ≤ k) (hb : 1 ≤ b) : 1 ≤ scale k b := by
  have hsp : 0 < Real.sqrt (Real.log k) := Real.sqrt_pos.mpr (Real.log_pos (by linarith))
  have hs : Real.sqrt (Real.log k) ≤ k := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by linarith,?_⟩
    have := Real.log_le_sub_one_of_pos (by linarith : 0 < k)
    nlinarith
  unfold scale
  exact (le_div_iff₀ hsp).mpr (by nlinarith)

theorem sqrt_logb_comparison {K k : ℝ} (hK : 2 ≤ K) (hk : 2 ≤ k)
    (hu : k ≤ K^320) :
    Real.sqrt (Real.log k) ≤ 18*Real.sqrt (Real.logb 2 K) := by
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg (by linarith)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog21 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at h
    exact h
  have hlogb : Real.log K ≤ Real.logb 2 K := by
    rw [Real.logb]
    apply (le_div_iff₀ hlog2).mpr
    nlinarith
  have hb0 : 0 ≤ Real.logb 2 K := hlogK.trans hlogb
  have hku := NumericOverheads.log_upper hK hk hu
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity,?_⟩
  rw [mul_pow,Real.sq_sqrt hb0]
  nlinarith

theorem rate_transfer {K k A e : ℝ} (hK : 2 ≤ K) (hk : 2 ≤ k)
    (hu : k ≤ K^320) (hA : 0 ≤ A) (he : e ≤ A/Real.sqrt (Real.logb 2 K)) :
    e ≤ 18*A/Real.sqrt (Real.log k) := by
  have hsp : 0 < Real.sqrt (Real.log k) := Real.sqrt_pos.mpr (Real.log_pos (by linarith))
  have hbp : 0 < Real.sqrt (Real.logb 2 K) :=
    Real.sqrt_pos.mpr (Real.logb_pos (by norm_num) (by linarith))
  apply he.trans
  apply (div_le_div_iff₀ hbp hsp).mpr
  have hs := sqrt_logb_comparison hK hk hu
  nlinarith [mul_le_mul_of_nonneg_left hs hA]

theorem leading_term {K k b Δ A e L : ℝ} (hK : 2 ≤ K) (hk : 2 ≤ k)
    (hb : 1 ≤ b) (hΔ : 1 ≤ Δ) (hu : k ≤ K^320) (hA : 0 ≤ A) (he0 : 0 ≤ e)
    (he : e ≤ A/Real.sqrt (Real.logb 2 K)) (hL : K^2*L ≤ 5*Δ*b*k) :
    e*K^2*L ≤ 90*A*Δ*scale k b := by
  have hr := rate_transfer hK hk hu hA he
  have hsp : 0 < Real.sqrt (Real.log k) := Real.sqrt_pos.mpr (Real.log_pos (by linarith))
  calc
    _ = e*(K^2*L) := by ring
    _ ≤ e*(5*Δ*b*k) := mul_le_mul_of_nonneg_left hL he0
    _ ≤ (18*A/Real.sqrt (Real.log k))*(5*Δ*b*k) :=
      mul_le_mul_of_nonneg_right hr (by positivity)
    _ = _ := by unfold scale; ring

theorem logarithmic_argument {k b Δ X : ℝ} (hk : 2 ≤ k) (hb : 1 ≤ b)
    (hΔ : 1 ≤ Δ) (hX : 0 < X) (hXu : X ≤ 17*Δ*b*k^5) :
    Real.log X ≤ polyCoefficient Δ*(Real.log k+Real.log b+1) := by
  have hk0 : 0 < k := by linarith
  have hb0 : 0 < b := by linarith
  have hΔ0 : 0 < Δ := by linarith
  have hlogk : 0 ≤ Real.log k := Real.log_nonneg (by linarith)
  have hlogb : 0 ≤ Real.log b := Real.log_nonneg hb
  have hlogΔ : 0 ≤ Real.log Δ := Real.log_nonneg hΔ
  have hlog17 : 0 ≤ Real.log 17 := Real.log_nonneg (by norm_num)
  have hu := Real.log_le_log hX hXu
  rw [Real.log_mul (by positivity) (by positivity),Real.log_pow,
    Real.log_mul (by positivity) hb0.ne',Real.log_mul (by norm_num) hΔ0.ne'] at hu
  norm_num at hu
  unfold polyCoefficient
  nlinarith [mul_nonneg (show 0 ≤ Real.log 17+Real.log Δ+1 by positivity) hlogk,
    mul_nonneg (show 0 ≤ Real.log 17+Real.log Δ+5 by positivity) hlogb]

theorem polynomial_term {K k b Δ X : ℝ} (hK : 2 ≤ K) (hk : 2 ≤ k)
    (hb : 1 ≤ b) (hΔ : 1 ≤ Δ) (hl : K^32 ≤ k) (hu : k ≤ K^320)
    (hX : 0 < X) (hXu : X ≤ 17*Δ*b*k^5) :
    K^2*Real.log X ≤ 5796*polyCoefficient Δ*scale k b := by
  have ha := logarithmic_argument hk hb hΔ hX hXu
  have hp := NumericOverheads.polynomial_factor hK hk hb hl hu
  have hc : 0 ≤ polyCoefficient Δ := by
    unfold polyCoefficient
    have := Real.log_nonneg hΔ
    have := Real.log_nonneg (by norm_num : (1:ℝ)≤17)
    positivity
  calc
    _ ≤ K^2*(polyCoefficient Δ*(Real.log k+Real.log b+1)) :=
      mul_le_mul_of_nonneg_left ha (by positivity)
    _ = polyCoefficient Δ*(K^2*(Real.log k+Real.log b+1)) := by ring
    _ ≤ polyCoefficient Δ*(5796*b*k/Real.sqrt (Real.log k)) :=
      mul_le_mul_of_nonneg_left hp hc
    _ = _ := by unfold scale; ring

theorem bound_log (e : ℝ) (K C₀ L B : ℕ) (hK : 1 ≤ K) (hL : 1 ≤ L) :
    Real.log (CliqueLevels.bound e K C₀ L B) =
      (e*(K:ℝ)^2*L)*Real.log 2 + (C₀:ℝ)*(K:ℝ)^2*Real.log ((K:ℝ)*(L+B)) := by
  unfold CliqueLevels.bound
  rw [Real.log_mul (by positivity) (by positivity),Real.log_rpow (by norm_num),Real.log_pow]
  push_cast
  ring

theorem bound_log_le {e A k b Δ : ℝ} (K C₀ L B : ℕ)
    (hK : 2 ≤ K) (hL : 1 ≤ L) (hk : 2 ≤ k) (hb : 1 ≤ b) (hΔ : 1 ≤ Δ)
    (hl : (K:ℝ)^32 ≤ k) (hu : k ≤ (K:ℝ)^320) (hA : 0 ≤ A) (he0 : 0 ≤ e)
    (he : e ≤ A/Real.sqrt (Real.logb 2 K))
    (hscaled : (K:ℝ)^2*L ≤ 5*Δ*b*k)
    (harg : (K:ℝ)*(L+B) ≤ 17*Δ*b*k^5) :
    Real.log (CliqueLevels.bound e K C₀ L B) ≤
      (90*A*Δ*Real.log 2+5796*C₀*polyCoefficient Δ)*scale k b := by
  have hKr : (2:ℝ) ≤ K := by exact_mod_cast hK
  have hlead := leading_term hKr hk hb hΔ hu hA he0 he hscaled
  have hpoly := polynomial_term hKr hk hb hΔ hl hu (by positivity : (0:ℝ)<(K:ℝ)*(L+B)) harg
  rw [bound_log e K C₀ L B (by omega) hL]
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hc0 : (0:ℝ) ≤ C₀ := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hlead hlog2,mul_le_mul_of_nonneg_left hpoly hc0]

theorem bound_one_le {e : ℝ} (K C₀ L B : ℕ) (hK : 1 ≤ K) (hL : 1 ≤ L)
    (he : 0 ≤ e) : 1 ≤ CliqueLevels.bound e K C₀ L B := by
  have h1 : (1:ℝ) ≤ (2:ℝ)^(e*(K:ℝ)^2*L) := Real.one_le_rpow (by norm_num) (by positivity)
  have hbase : (1:ℝ) ≤ (K:ℝ)*(L+B) := by exact_mod_cast (show 1 ≤ K*(L+B) by nlinarith)
  have h2 : (1:ℝ) ≤ ((K:ℝ)*(L+B))^(C₀*K^2) := one_le_pow₀ hbase
  unfold CliqueLevels.bound
  nlinarith

theorem ceil_log {x C k b : ℝ} (hx : 1 ≤ x) (hC : Real.log x ≤ C*scale k b)
    (hk : 2 ≤ k) (hb : 1 ≤ b) :
    Real.log (⌈x⌉₊:ℝ) ≤ (C+Real.log 2)*scale k b := by
  have hc : (⌈x⌉₊:ℝ) ≤ x+1 := (Nat.ceil_lt_add_one (by linarith : 0 ≤ x)).le
  have hc0 : (0:ℝ) < (⌈x⌉₊:ℝ) := by have := Nat.le_ceil x; linarith
  have hh : (⌈x⌉₊:ℝ) ≤ 2*x := by linarith
  have hl := Real.log_le_log hc0 hh
  rw [Real.log_mul (by norm_num) (by linarith)] at hl
  have hs := one_le_scale hk hb
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  nlinarith [mul_le_mul_of_nonneg_left hs hlog2]

#print axioms one_le_scale
#print axioms rate_transfer
#print axioms leading_term
#print axioms polynomial_term
#print axioms bound_log
#print axioms bound_log_le
#print axioms ceil_log

end CSPConsequence.LogCost
