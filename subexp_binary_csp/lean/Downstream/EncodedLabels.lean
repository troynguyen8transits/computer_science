import Downstream.CSPBounds
import Downstream.FiniteEncoding
import Mathlib.Data.List.ProdSigma

set_option autoImplicit false

/-! Concrete bit encodings of the labels on actual crossing CSP edges.
Nonedges and indices outside the crossing get the fixed default label. They
consume no bits. This avoids enumerating an exponential label table at runtime.
-/

namespace CSPConsequence.EncodedLabels

open Finset Groundwork DomainCodec

variable {k D g : ℕ} (I : Instance k D) (d : Fin D) (b : ℕ)
  (χ : Fin k → Fin g)

def crossing (G H : Fin g) : List (Fin k × Fin k) :=
  ((List.finRange k).product (List.finRange k)).filter fun p =>
    decide (χ p.1 = G ∧ χ p.2 = H ∧ I.edge p.1 p.2 = true)

theorem mem_crossing (G H : Fin g) (p : Fin k × Fin k) :
    p ∈ crossing I χ G H ↔ χ p.1 = G ∧ χ p.2 = H ∧ I.edge p.1 p.2 = true := by
  rcases p with ⟨a,v⟩
  simp [crossing, List.mem_product]

theorem nodup_crossing (G H : Fin g) : (crossing I χ G H).Nodup :=
  ((List.nodup_finRange k).product (List.nodup_finRange k)).filter _

theorem base_labels (a v : Fin k) :
    (I.network d b).lab a v = if I.edge a v then univ else {d} := by
  have he : I.edge (min a v) (max a v) = I.edge a v := by
    rcases le_total a v with h | h
    · simp [min_eq_left h, max_eq_right h]
    · simp [min_eq_right h, max_eq_left h, I.symmetric v a]
  change (if I.edge (min a v) (max a v) then univ else {d}) = _
  rw [he]

theorem labels_eq (G H : Fin g) (hGH : G < H) :
    ((I.network d b).merge χ d d).lab G H = assignments d (crossing I χ G H) := by
  ext t
  simp only [Network.lab, min_eq_left hGH.le, max_eq_right hGH.le]
  change t ∈ tuples (fun p : Fin k × Fin k => χ p.1 = G ∧ χ p.2 = H)
      (fun p => (I.network d b).lab p.1 p.2) d ↔ _
  rw [mem_tuples, mem_assignments]
  constructor
  · intro h p hnp
    by_cases hc : χ p.1 = G ∧ χ p.2 = H
    · have he : I.edge p.1 p.2 ≠ true := fun he => hnp ((mem_crossing I χ G H p).mpr ⟨hc.1,hc.2,he⟩)
      have hp := (h p).1 hc
      rw [base_labels I d b] at hp
      simpa [he] using hp
    · exact (h p).2 hc
  · intro h p
    refine ⟨?_, ?_⟩
    · intro hc
      rw [base_labels I d b]
      by_cases he : I.edge p.1 p.2 = true
      · simp [he]
      · simp only [if_neg he, mem_singleton]
        apply h p
        rw [mem_crossing]
        simp [he]
    · intro hc
      apply h p
      rw [mem_crossing]
      intro hp
      exact hc ⟨hp.1,hp.2.1⟩

theorem label_sum (hD : D ≤ 2^b) (G H : Fin g) (hGH : G < H)
    (F : (Fin k × Fin k → Fin D) → ℤ) :
    (∑ w ∈ encodedStates D b (crossing I χ G H),
      F (decode d b (crossing I χ G H) w)) =
    ∑ t ∈ ((I.network d b).merge χ d d).lab G H, F t := by
  rw [labels_eq I d b χ G H hGH]
  rw [sum_encoded d _ (nodup_crossing I χ G H) hD]
  apply Finset.sum_congr rfl
  intro t ht
  rw [decode_encode_assignment d _ (nodup_crossing I χ G H) hD t ht]

#print axioms labels_eq
#print axioms label_sum

end CSPConsequence.EncodedLabels
