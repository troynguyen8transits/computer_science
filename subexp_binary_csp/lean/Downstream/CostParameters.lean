import Downstream.BitNetworkValidity
import Downstream.NumericOverheads
import ExplicitCost.GroupingDefs

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! Bounds on the actual network and grouping parameters. These use the checked
provider's B=s+s^2+1, retaining its polynomial growth instead of assuming B=1. -/

namespace CSPConsequence.CostParameters

open Groundwork Finset

theorem total_le {g : ℕ} (N : Eight.SecNetworks.Net g) {P B : ℕ} (hN : N.Is P B) :
    N.U ≤ g*P := by
  calc
    _ ≤ ∑ _a : Fin g, P := Finset.sum_le_sum fun a _ => hN.i a
    _ = g*P := by simp [mul_comm]

theorem entry_bound {k g : ℕ} (hk : 1 ≤ k) :
    (k/g+1)+(k/g+1)*(k/g+1)+1 ≤ 7*k^2 := by
  have hs : k/g+1 ≤ 2*k := by have := Nat.div_le_self k g; omega
  have hsq : (k/g+1)^2 ≤ (2*k)^2 := Nat.pow_le_pow_left hs 2
  nlinarith

theorem row_bound {k g b Δ : ℕ} (hk : 1 ≤ k) :
    Δ*b*(k/g+1) ≤ 2*Δ*b*k := by
  have hs : k/g+1 ≤ 2*k := by have := Nat.div_le_self k g; omega
  calc
    _ ≤ Δ*b*(2*k) := Nat.mul_le_mul_left _ hs
    _ = _ := by ring

theorem scaled_length {K g P : ℕ} (N : Eight.SecNetworks.Net g)
    (hK : 1 ≤ K) :
    (K:ℝ)^2*(AppRunningTime.Lof K g ((1:ℝ)/(2*K)) P N.U) ≤
      N.U+(g:ℝ)*P/K+(K:ℝ)^2 := by
  have hKp : (0:ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hn : (0:ℝ) ≤ ((N.U:ℝ)+2*((1:ℝ)/(2*K))*g*P)/(K:ℝ)^2 := by positivity
  have hc := (Nat.ceil_lt_add_one hn).le
  unfold AppRunningTime.Lof
  calc
    _ ≤ (K:ℝ)^2*(((N.U:ℝ)+2*((1:ℝ)/(2*K))*g*P)/(K:ℝ)^2+1) :=
      mul_le_mul_of_nonneg_left hc (by positivity)
    _ = _ := by field_simp [ne_of_gt hKp]

theorem length_bound {K k g P Δ b : ℕ} (N : Eight.SecNetworks.Net g)
    (hK : 1 ≤ K) (hKsq : K^2 ≤ k) (hk : 1 ≤ k) (hb : 1 ≤ b) (hΔ : 1 ≤ Δ)
    (hU : N.U ≤ 2*Δ*k*b) (hvol : g*P ≤ 2*Δ*k*b) :
    AppRunningTime.Lof K g ((1:ℝ)/(2*K)) P N.U ≤ 5*Δ*b*k := by
  have hl := scaled_length (P := P) N hK
  have hkr : (1:ℝ) ≤ K := by exact_mod_cast hK
  have hsq : (K:ℝ)^2 ≤ k := by exact_mod_cast hKsq
  have hur : (N.U:ℝ) ≤ 2*Δ*k*b := by exact_mod_cast hU
  have hvr : (g:ℝ)*P ≤ 2*Δ*k*b := by exact_mod_cast hvol
  have hdiv : (g:ℝ)*P/K ≤ (g:ℝ)*P := div_le_self (by positivity) hkr
  have hkdb : (k:ℝ) ≤ Δ*b*k := by
    exact_mod_cast (show k ≤ Δ*b*k by
      simpa using Nat.mul_le_mul_right k (Nat.mul_pos hΔ hb))
  have hL : (0:ℝ) ≤ AppRunningTime.Lof K g ((1:ℝ)/(2*K)) P N.U := by positivity
  have hsq1 : (1:ℝ) ≤ (K:ℝ)^2 := one_le_pow₀ hkr
  have hh : (AppRunningTime.Lof K g ((1:ℝ)/(2*K)) P N.U : ℝ) ≤ 5*Δ*b*k := by
    nlinarith [mul_le_mul_of_nonneg_right hsq1 hL]
  exact_mod_cast hh

theorem bits_bound {K k g P B Δ b : ℕ}
    (hk : 1 ≤ k) (hb : 1 ≤ b) (hΔ : 1 ≤ Δ) (hKk : K ≤ k) (hgk : g ≤ k)
    (hvol : g*P ≤ 2*Δ*k*b) (hB : B ≤ 7*k^2) :
    AppRunningTime.B'of K g P B ≤ 12*Δ*b*k^4 := by
  have hgb : g^2*B ≤ 7*k^4 := by
    calc
      _ ≤ k^2*(7*k^2) := Nat.mul_le_mul (Nat.pow_le_pow_left hgk 2) hB
      _ = _ := by ring
  have hk4 : k ≤ k^4 := le_self_pow hk (by decide)
  have hdb : 1 ≤ Δ*b := Nat.mul_pos hΔ hb
  have hbase : 2*g*P+K+g^2*B ≤ 12*Δ*b*k^4 := by nlinarith
  unfold AppRunningTime.B'of
  calc
    _ ≤ (2*g*P+K-1)+g^2*B := Nat.add_le_add_right (Nat.div_le_self _ _) _
    _ ≤ 2*g*P+K+g^2*B := Nat.add_le_add_right (Nat.sub_le _ _) _
    _ ≤ _ := hbase

theorem factor_bound {k g P B Δ b : ℕ}
    (hk : 1 ≤ k) (hb : 1 ≤ b) (hΔ : 1 ≤ Δ) (hgk : g ≤ k)
    (hP : P ≤ 2*Δ*b*k) (hB : B ≤ 7*k^2) :
    g*(P+B) ≤ 9*Δ*b*k^3 := by
  have hk2 : k ≤ k^2 := le_self_pow hk (by decide)
  have hdb : 1 ≤ Δ*b := Nat.mul_pos hΔ hb
  have hp : P+B ≤ 9*Δ*b*k^2 := by nlinarith
  calc
    _ ≤ k*(9*Δ*b*k^2) := Nat.mul_le_mul hgk hp
    _ = _ := by ring

theorem clique_argument_bound {K k L B' Δ b : ℕ}
    (hk : 1 ≤ k) (hb : 1 ≤ b) (hΔ : 1 ≤ Δ) (hKk : K ≤ k)
    (hL : L ≤ 5*Δ*b*k) (hB : B' ≤ 12*Δ*b*k^4) :
    K*(L+B') ≤ 17*Δ*b*k^5 := by
  have hk4 : k ≤ k^4 := le_self_pow hk (by decide)
  have hp : L+B' ≤ 17*Δ*b*k^4 := by nlinarith
  calc
    _ ≤ k*(17*Δ*b*k^4) := Nat.mul_le_mul hKk hp
    _ = _ := by ring

#print axioms total_le
#print axioms scaled_length
#print axioms length_bound
#print axioms bits_bound
#print axioms factor_bound
#print axioms clique_argument_bound

end CSPConsequence.CostParameters
