import Downstream.EncodedSettings
import Downstream.EncodedLabels
import Eight.SecNetworks_Defs

set_option autoImplicit false

/-! Concrete bit-network data for the shorter CSP route.
The local predicates inspect input strings and finite lists; they do not decide
membership by generating the exponentially large semantic finite sets.
-/

namespace CSPConsequence.BitNetwork

open Finset Groundwork DomainCodec

variable {k D g : ℕ} (I : Instance k D) (d : Fin D) (b : ℕ)
  (χ : Fin k → Fin g)

def legalLabel (e : List (Fin k × Fin k)) (w : List Bool) : Bool :=
  decide (w.length = b*e.length) &&
    e.all (fun p => decide (ofWord (cut (fun _ => b) [] e w p) < D))

theorem legalLabel_iff (e : List (Fin k × Fin k)) (w : List Bool) :
    legalLabel (D := D) b e w = true ↔ legal (D := D) b e w := by
  simp [legalLabel, legal, List.all_eq_true]

theorem legal_filter (e : List (Fin k × Fin k)) :
    (words (b*e.length)).filter (fun w => legalLabel (D := D) b e w) =
      encodedStates D b e := by
  ext w
  simp [legalLabel, encodedStates, List.all_eq_true, mem_words, and_assoc]

theorem label_capacity (G H : Fin g) :
    ((I.network d b).merge χ d d).c G H =
      b*(EncodedLabels.crossing I χ G H).length := by
  classical
  have heq : (EncodedLabels.crossing I χ G H).toFinset =
      univ.filter (fun p : Fin k × Fin k => χ p.1 = G ∧ χ p.2 = H ∧ I.edge p.1 p.2 = true) := by
    ext p
    simp [EncodedLabels.mem_crossing]
  change (∑ p ∈ univ.filter (fun p : Fin k × Fin k => χ p.1 = G ∧ χ p.2 = H),
    if I.edge p.1 p.2 then b else 0) = _
  rw [← Finset.sum_filter, Finset.filter_filter]
  have hpred : (univ.filter (fun p : Fin k × Fin k =>
      (χ p.1 = G ∧ χ p.2 = H) ∧ I.edge p.1 p.2 = true)) =
      (EncodedLabels.crossing I χ G H).toFinset := by
    rw [heq]
    ext p
    simp [and_assoc]
  rw [hpred]
  simp [List.toFinset_card_of_nodup (EncodedLabels.nodup_crossing I χ G H), mul_comm]

def labels (G H : Fin g) : List (Fin k × Fin k) :=
  EncodedLabels.crossing I χ (min G H) (max G H)

def data : Eight.SecNetworks.Net g where
  len G := b*(EncodedSettings.members χ G).length
  S G := encodedStates D b (EncodedSettings.members χ G)
  W G w := ((I.network d b).merge χ d d).W G
    (decode d b (EncodedSettings.members χ G) w)
  Ψ G H w w' := ((I.network d b).merge χ d d).Ψ G H
    (decode d b (EncodedSettings.members χ G) w)
    (decode d b (EncodedSettings.members χ H) w')
  c G H := ((I.network d b).merge χ d d).c G H
  f G H w θ := if legalLabel (D := D) b (labels I χ G H) θ then
    ((I.network d b).merge χ d d).f G H
      (decode d b (EncodedSettings.members χ G) w)
      (decode d b (labels I χ G H) θ) else 0

theorem value_eq_count (hD : D ≤ 2^b) : (data I d b χ).value = (I.count : ℤ) :=
  EncodedSettings.count_as_bits I d b χ hD

theorem factor_lt (hD : D ≤ 2^b) (G H : Fin g) (hGH : G < H)
    (w w' : List Bool) :
    (data I d b χ).Ψ G H w w' =
      ∑ θ ∈ words ((data I d b χ).c G H),
        (data I d b χ).f G H w θ * (data I d b χ).f H G w' θ := by
  let M := (I.network d b).merge χ d d
  let x := decode d b (EncodedSettings.members χ G) w
  let y := decode d b (EncodedSettings.members χ H) w'
  let e := EncodedLabels.crossing I χ G H
  let F := fun θ => M.f G H x (decode d b e θ) * M.f H G y (decode d b e θ)
  have hsum : M.Ψ G H x y = ∑ θ ∈ encodedStates D b e, F θ :=
    (EncodedLabels.label_sum I d b χ hD G H hGH
      (fun t => M.f G H x t * M.f H G y t)).symm
  have he1 : labels I χ G H = e := by simp [labels, e, min_eq_left hGH.le, max_eq_right hGH.le]
  have he2 : labels I χ H G = e := by simp [labels, e, min_eq_right hGH.le, max_eq_left hGH.le]
  calc
    _ = ∑ θ ∈ encodedStates D b e, F θ := hsum
    _ = ∑ θ ∈ words (b*e.length), if legalLabel (D := D) b e θ then F θ else 0 := by
      rw [← legal_filter b e, Finset.sum_filter]
    _ = _ := by
      change _ = ∑ θ ∈ words (M.c G H),
        (data I d b χ).f G H w θ * (data I d b χ).f H G w' θ
      rw [label_capacity I d b χ G H]
      apply Finset.sum_congr rfl
      intro θ _
      by_cases ht : legalLabel (D := D) b e θ = true
      · simp only [data, he1, he2, if_pos ht]
        rfl
      · simp only [data, he1, he2, if_neg ht, zero_mul]

#print axioms label_capacity
#print axioms value_eq_count
#print axioms factor_lt

end CSPConsequence.BitNetwork
