import Downstream.CSPNetwork

set_option autoImplicit false

/-! Computable balanced coarsening and its actual capacity bounds.
No clique algorithm or running-time theorem is assumed here.
-/

namespace CSPConsequence

open Finset Groundwork

def balanced {k g : ℕ} (hg : 0 < g) (a : Fin k) : Fin g :=
  ⟨a.val % g, Nat.mod_lt _ hg⟩

theorem balanced_fiber {k g : ℕ} (hg : 0 < g) (G : Fin g) :
    #{a : Fin k | balanced hg a = G} ≤ k/g+1 := by
  classical
  have hc := Finset.card_le_card_of_injOn (fun a : Fin k => a.val/g)
    (s := univ.filter fun a : Fin k => balanced hg a = G)
    (t := range (k/g+1))
  rw [card_range] at hc
  apply hc
  · intro a _
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (Nat.le_of_lt a.isLt)))
  · intro a ha v hv heq
    change a.val/g = v.val/g at heq
    have ha' : a.val % g = G.val := congrArg Fin.val ((mem_filter.mp ha).2)
    have hv' : v.val % g = G.val := congrArg Fin.val ((mem_filter.mp hv).2)
    apply Fin.ext
    have h1 := Nat.mod_add_div a.val g
    have h2 := Nat.mod_add_div v.val g
    rw [ha', heq] at h1
    rw [hv'] at h2
    omega

theorem balanced_volume {k g Δ b : ℕ} (hgk : g ≤ k) :
    g*(Δ*b*(k/g+1)) ≤ 2*Δ*k*b := by
  calc
    g*(Δ*b*(k/g+1)) = Δ*b*((k/g)*g+g) := by ring
    _ ≤ Δ*b*(k+g) := Nat.mul_le_mul_left _
      (Nat.add_le_add_right (Nat.div_mul_le_self k g) g)
    _ ≤ Δ*b*(2*k) := Nat.mul_le_mul_left _ (by omega)
    _ = 2*Δ*k*b := by ring

namespace Instance

variable {k D g b Δ : ℕ} (I : Instance k D)

theorem balanced_count (d : Fin D) (hg : 0 < g) :
    ((I.network d b).merge (balanced hg) d d).value = (I.count : ℤ) :=
  I.coarsened_count d b (balanced hg)

theorem balanced_shaped (d : Fin D) (hg : 0 < g) (hb : 1 ≤ b)
    (hD : D ≤ 2^b) (hΔ : 1 ≤ Δ) (hdeg : ∀ a, I.degree a ≤ Δ) :
    ((I.network d b).merge (balanced hg) d d).Shaped (Δ*b*(k/g+1)) :=
  I.coarsened_shaped d (balanced hg) hb hD hΔ hdeg (balanced_fiber hg)

/-- The total actually used after merging; internal edges have disappeared. -/
theorem balanced_total (d : Fin D) (hg : 0 < g) (hgk : g ≤ k) (hb : 1 ≤ b)
    (hD : D ≤ 2^b) (hΔ : 1 ≤ Δ) (hdeg : ∀ a, I.degree a ≤ Δ) :
    ((I.network d b).merge (balanced hg) d d).U ≤ 2*Δ*k*b := by
  have hs := I.balanced_shaped d hg hb hD hΔ hdeg
  calc
    _ ≤ ∑ _a : Fin g, Δ*b*(k/g+1) := Finset.sum_le_sum fun a _ => hs.sum_c a
    _ = g*(Δ*b*(k/g+1)) := by simp [mul_comm]
    _ ≤ 2*Δ*k*b := balanced_volume hgk

#print axioms balanced_count
#print axioms balanced_shaped
#print axioms balanced_total

end Instance

#print axioms balanced_fiber
#print axioms balanced_volume

end CSPConsequence
