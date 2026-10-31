import Downstream.ProviderLabels

set_option autoImplicit false

/-! Exact crossing-list order, label validity and label decoding for the
concrete finite-input provider, including both orders of the group endpoints.
-/

namespace CSPConsequence.LabelRefinement

open Groundwork DomainCodec FiniteInput ProviderParameters ProviderTables
  NodeRefinement PairDecoder ProviderLabels

theorem product_map {α β γ δ : Type} (f : α → β) (g : γ → δ) (l : List α) (r : List γ) :
    (l.map f).product (r.map g) = (l.product r).map (fun p => (f p.1,g p.2)) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    change ((r.map g).map (fun b => (f a,b)) ++ (l.map f).product (r.map g)) =
      ((r.map (fun v => (a,v))) ++ l.product r).map (fun p => (f p.1,g p.2))
    rw [List.map_append, ih]
    simp [List.map_map, Function.comp_def]

variable {k D g : ℕ} (I : Instance k D) (b : ℕ) (hg : 0 < g)

theorem crossingPairs_of (G H : Fin g) :
    crossingPairs (paramsOf I g b,(G.val,H.val)) =
      (BitNetwork.labels I (balanced hg) G H).map pairValues := by
  have hv : vertexList (paramsOf I g b) = List.range k := by
    simp [vertexList, paramsOf, vertices_tabulate]
  have hc : groupCount (paramsOf I g b) = g := by simp [groupCount, paramsOf]
  unfold crossingPairs
  simp only [hv, hc]
  rw [← map_finRange_val k, product_map, List.filter_map]
  unfold BitNetwork.labels EncodedLabels.crossing
  apply congrArg (List.map pairValues)
  apply List.filter_congr
  intro p _
  rcases p with ⟨a,v⟩
  apply Bool.eq_iff_iff.mpr
  by_cases h : G ≤ H
  · have hv : G.val ≤ H.val := h
    simp [pairValues, paramsOf, edgeAt_tabulate, min_eq_left h, max_eq_right h,
      min_eq_left hv, max_eq_right hv, balanced, Fin.ext_iff, and_assoc]
  · have h' : H ≤ G := le_of_not_ge h
    have hv : H.val ≤ G.val := h'
    simp [pairValues, paramsOf, edgeAt_tabulate, min_eq_right h', max_eq_left h',
      min_eq_right hv, max_eq_left hv, balanced, Fin.ext_iff, and_assoc]

theorem labelValue_of (hD : 0 < D) (G H : Fin g) (θ : List Bool) (p : Fin k × Fin k) :
    labelValue (paramsOf I g b,(G.val,H.val),θ,pairValues p) =
      (decode ⟨0,hD⟩ b (BitNetwork.labels I (balanced hg) G H) θ p).val := by
  unfold labelValue
  rw [crossingPairs_of I b hg G H]
  simpa [paramsOf, blockWidth, domain_tabulate] using
    decodePairNat_eq hD b (BitNetwork.labels I (balanced hg) G H) θ p

theorem labelLegal_of (G H : Fin g) (θ : List Bool) :
    labelLegal (paramsOf I g b,(G.val,H.val),θ) =
      BitNetwork.legalLabel (D := D) b (BitNetwork.labels I (balanced hg) G H) θ := by
  apply Bool.eq_iff_iff.mpr
  unfold labelLegal
  rw [crossingPairs_of I b hg G H]
  simp [paramsOf, blockWidth, domain_tabulate, List.all_map, List.all_eq_true,
    readPairBlock_eq, BitNetwork.legalLabel]

#print axioms crossingPairs_of
#print axioms labelValue_of
#print axioms labelLegal_of

end CSPConsequence.LabelRefinement
