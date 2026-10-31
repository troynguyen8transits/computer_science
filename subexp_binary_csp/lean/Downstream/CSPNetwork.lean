import Groundwork.Net.Net
import Groundwork.Net.ColouringNet
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.SplitIfs

set_option autoImplicit false

/-! Exact binary-CSP semantics for the shorter network route.

Directly reuses Anthropic's `Groundwork.Network.value_merge` and
`merge_shaped` (Apache-2.0, pinned repository revision recorded externally).
This file proves semantics and combinatorial shape, not a machine time bound.
-/

namespace CSPConsequence

open Finset Groundwork

structure Instance (k D : ℕ) where
  edge : Fin k → Fin k → Bool
  symmetric : ∀ a b, edge a b = edge b a
  relation : Fin k → Fin k → Fin D → Fin D → Bool

namespace Instance

variable {k D : ℕ} (I : Instance k D)

/-- The relation table for an unordered pair is read in increasing vertex order. -/
def accepts (a b : Fin k) (x y : Fin D) : Bool :=
  if a < b then I.relation a b x y else I.relation b a y x

def valid (z : Fin k → Fin D) : Prop :=
  ∀ a b, a < b → I.edge a b = true → I.relation a b (z a) (z b) = true

instance (z : Fin k → Fin D) : Decidable (I.valid z) := by
  unfold valid
  infer_instance

def count : ℕ := #{z : Fin k → Fin D | I.valid z}

/-- Nonedges have one label, so they contribute one rather than a domain factor. -/
def network (d : Fin D) (b : ℕ) : Network (Fin k) (Fin D) (Fin D) where
  S _ := univ
  W _ _ := 1
  Θ a v := if I.edge a v then univ else {d}
  f a v z θ := if I.edge a v then
      if a < v then (if z = θ then 1 else 0)
      else (if I.relation v a θ z then 1 else 0)
    else 1
  c a v := if I.edge a v then b else 0

theorem interaction (d : Fin D) (b : ℕ) (a v : Fin k) (hav : a < v)
    (x y : Fin D) :
    (I.network d b).Ψ a v x y =
      if I.edge a v then (if I.relation a v x y then 1 else 0) else 1 := by
  simp only [Network.Ψ, Network.lab, min_eq_left hav.le, max_eq_right hav.le]
  by_cases he : I.edge a v = true
  · have he' : I.edge v a = true := (I.symmetric v a).trans he
    simp [network, he, he', hav, hav.not_gt]
    rw [Finset.sum_eq_single x] <;> simp_all
    intro v hv _
    exact Ne.symm hv
  · have he0 : I.edge a v = false := Bool.eq_false_iff.mpr he
    have he' : I.edge v a = false := (I.symmetric v a).trans he0
    simp [network, he0, he']

theorem value_eq_count (d : Fin D) (b : ℕ) :
    (I.network d b).value = (I.count : ℤ) := by
  classical
  have ht (z : Fin k → Fin D) :
      (∏ p ∈ pairs (Fin k), (I.network d b).Ψ p.1 p.2 (z p.1) (z p.2)) =
        if I.valid z then (1 : ℤ) else 0 := by
    by_cases h : I.valid z
    · rw [if_pos h]
      refine prod_eq_one fun p hp => ?_
      have hp' : p.1 < p.2 := (mem_filter.mp hp).2
      rw [I.interaction d b _ _ hp']
      by_cases he : I.edge p.1 p.2 = true
      · rw [if_pos he, if_pos (h _ _ hp' he)]
      · rw [if_neg he]
    · rw [if_neg h]
      have hex : ∃ a v, a < v ∧ I.edge a v = true ∧
          I.relation a v (z a) (z v) ≠ true := by
        simpa only [valid, not_forall, Classical.not_imp, exists_prop] using h
      obtain ⟨a, v, hav, he, hr⟩ := hex
      apply prod_eq_zero (i := (a,v)) (by simp [pairs, hav])
      rw [I.interaction d b _ _ hav]
      simp [he, hr]
  unfold Network.value
  simp only [network, prod_const_one, one_mul]
  change (∑ z ∈ Fintype.piFinset (fun _ : Fin k => (univ : Finset (Fin D))),
      ∏ p ∈ pairs (Fin k), (I.network d b).Ψ p.1 p.2 (z p.1) (z p.2)) = _
  simp_rw [ht]
  simp [count, Fintype.piFinset_univ]

def degree (a : Fin k) : ℕ := #{v ∈ univ.erase a | I.edge a v = true}

theorem shaped (d : Fin D) {b Δ : ℕ} (_hb : 1 ≤ b) (hD : D ≤ 2^b)
    (hΔ : 1 ≤ Δ) (hdeg : ∀ a, I.degree a ≤ Δ) :
    (I.network d b).Shaped (Δ*b) := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a
    simp only [network, card_univ, Fintype.card_fin]
    exact hD.trans (Nat.pow_le_pow_right (by norm_num) (by nlinarith))
  · intro a v
    simp [network, I.symmetric a v]
  · intro a
    change (∑ v ∈ univ.erase a, if I.edge a v then b else 0) ≤ Δ*b
    have heq : (∑ v ∈ univ.erase a, if I.edge a v then b else 0) = I.degree a*b := by
      simp [degree, ← Finset.sum_filter, mul_comm]
    rw [heq]
    exact Nat.mul_le_mul_right b (hdeg a)
  · intro a v hav
    unfold Network.lab
    have hsym : I.edge (min a v) (max a v) = I.edge a v := by
      rcases le_total a v with h | h
      · simp [min_eq_left h, max_eq_right h]
      · simp [min_eq_right h, max_eq_left h, I.symmetric v a]
    simp only [network, hsym]
    by_cases he : I.edge a v = true
    · simp [he, hD]
    · have he0 : I.edge a v = false := Bool.eq_false_iff.mpr he
      simp [he0]

/-- Direct application of the existing exact merge theorem, without a new assumption. -/
theorem coarsened_count {g : ℕ} (d : Fin D) (b : ℕ) (χ : Fin k → Fin g) :
    ((I.network d b).merge χ d d).value = (I.count : ℤ) := by
  rw [Network.value_merge, I.value_eq_count]

/-- Existing shape theorem applied to a balanced coarsening of this actual CSP network. -/
theorem coarsened_shaped {g s b Δ : ℕ} (d : Fin D) (χ : Fin k → Fin g)
    (hb : 1 ≤ b) (hD : D ≤ 2^b) (hΔ : 1 ≤ Δ)
    (hdeg : ∀ a, I.degree a ≤ Δ) (hχ : ∀ G, #{a | χ a = G} ≤ s) :
    ((I.network d b).merge χ d d).Shaped (Δ*b*s) :=
  Network.merge_shaped _ _ _ _ (I.shaped d hb hD hΔ hdeg) hχ

#print axioms value_eq_count
#print axioms shaped
#print axioms coarsened_count
#print axioms coarsened_shaped

end Instance

end CSPConsequence
