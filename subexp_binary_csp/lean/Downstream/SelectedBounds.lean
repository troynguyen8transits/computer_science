import Downstream.CostParameters
import Downstream.LevelSelection

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! Apply the numeric parameter bounds to the actual bit network and the
selected grouping size. No resource bound is assumed for an abstract provider. -/

namespace CSPConsequence.SelectedBounds

open Groundwork

structure Bounds (K k g P B U Δ b L B' : ℕ) : Prop where
  k_two : 2 ≤ k
  K_le : K ≤ k
  K_sq_le : K^2 ≤ k
  g_le : g ≤ k
  volume : g*P ≤ 2*Δ*k*b
  total : U ≤ 2*Δ*k*b
  row : P ≤ 2*Δ*b*k
  entry : B ≤ 7*k^2
  scaled : (K:ℝ)^2*L ≤ 5*Δ*b*k
  length : L ≤ 5*Δ*b*k
  bits : B' ≤ 12*Δ*b*k^4
  argument : K*(L+B') ≤ 17*Δ*b*k^5
  factor : g*(P+B) ≤ 9*Δ*b*k^3

theorem actual {k D g : ℕ} (I : Instance k D) (b Δ K : ℕ) (hg : 0 < g)
    (hpos : 0 < D) (hb : 1 ≤ b) (hD : D ≤ 2^b) (hΔ : 1 ≤ Δ)
    (hdeg : ∀ a, I.degree a ≤ Δ) (hK : 2 ≤ K) (hsize : K^32 ≤ k)
    (hgK : g = 3*K^8) :
    let N := BitNetwork.data I ⟨0,hpos⟩ b (balanced hg)
    let P := Δ*b*(k/g+1)
    let B := (k/g+1)+(k/g+1)*(k/g+1)+1
    Bounds K k g P B N.U Δ b (AppRunningTime.Lof K g ((1:ℝ)/(2*K)) P N.U)
      (AppRunningTime.B'of K g P B) := by
  intro N P B
  have hK1 : 1 ≤ K := by omega
  have hKk : K ≤ k := (le_self_pow hK1 (by decide : 32 ≠ 0)).trans hsize
  have hk : 1 ≤ k := by omega
  have hk2 : 2 ≤ k := by omega
  have hKsq : K^2 ≤ k :=
    (Nat.pow_le_pow_right hK1 (by decide : 2 ≤ 32)).trans hsize
  have hgk : g ≤ k := by rw [hgK]; exact LevelSelection.grouping_fits hK hsize
  have hvol : g*P ≤ 2*Δ*k*b := balanced_volume hgk
  have hn : N.Is P B := BitNetwork.is_valid I ⟨0,hpos⟩ hg hb hD hΔ hdeg
  have hU : N.U ≤ 2*Δ*k*b := (CostParameters.total_le N hn).trans hvol
  have hP : P ≤ 2*Δ*b*k := CostParameters.row_bound hk
  have hB : B ≤ 7*k^2 := CostParameters.entry_bound hk
  have hscaled : (K:ℝ)^2*(AppRunningTime.Lof K g ((1:ℝ)/(2*K)) P N.U) ≤ 5*Δ*b*k := by
    have hl := CostParameters.scaled_length (P := P) N hK1
    have hkr : (1:ℝ) ≤ K := by exact_mod_cast hK1
    have hsq : (K:ℝ)^2 ≤ k := by exact_mod_cast hKsq
    have hur : (N.U:ℝ) ≤ 2*Δ*k*b := by exact_mod_cast hU
    have hvr : (g:ℝ)*P ≤ 2*Δ*k*b := by exact_mod_cast hvol
    have hdiv : (g:ℝ)*P/K ≤ (g:ℝ)*P := div_le_self (by positivity) hkr
    have hkdb : (k:ℝ) ≤ Δ*b*k := by
      exact_mod_cast (show k ≤ Δ*b*k by
        simpa using Nat.mul_le_mul_right k (Nat.mul_pos hΔ hb))
    linarith
  have hL := CostParameters.length_bound N hK1 hKsq hk hb hΔ hU hvol
  have hbits := CostParameters.bits_bound hk hb hΔ hKk hgk hvol hB
  exact ⟨hk2,hKk,hKsq,hgk,hvol,hU,hP,hB,hscaled,hL,hbits,
    CostParameters.clique_argument_bound hk hb hΔ hKk hL hbits,
    CostParameters.factor_bound hk hb hΔ hgk hP hB⟩

#print axioms actual

end CSPConsequence.SelectedBounds
