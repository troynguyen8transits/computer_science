import Downstream.BitInputCodec

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! Polynomial-time variable-length list slicing for the sparse bit codec.
Counts are binary numbers; taking/dropping past the end never writes a unary
count or materializes a list of that count. -/

namespace CSPConsequence.ListSlices

open Groundwork

def slice {α : Type} (counts : List ℕ) (i : ℕ) (w : List α) : List α :=
  (w.drop ((counts.take i).sum)).take (counts.getD i 0)

def split {α : Type} (counts : List ℕ) (w : List α) : List (List α) :=
  (List.range counts.length).map (fun i => slice counts i w)

theorem split_polyT {α β : Type} [Enc α] [Enc β]
    (counts : α → List ℕ) (w : α → List β) (hc : PolyT counts) (hw : PolyT w) :
    PolyT (fun x => split (counts x) (w x)) := by
  have hr := PolyT.range (Unary.of_length hc)
  unfold split slice
  apply PolyT.map
  · fun_prop
  · exact hr

theorem slice_flatten {α : Type} (rows : List (List α)) (i : ℕ) (hi : i < rows.length) :
    slice (rows.map List.length) i rows.flatten = rows[i] := by
  induction rows generalizing i with
  | nil => simp at hi
  | cons a rows ih =>
    cases i with
    | zero =>
      simp only [slice,List.map_cons,List.take_zero,List.sum_nil,List.drop_zero,
        List.getD_cons_zero,List.flatten_cons,List.getElem_cons_zero]
      exact List.take_left
    | succ i =>
      have hs : (a ++ rows.flatten).drop (a.length+((rows.map List.length).take i).sum) =
          rows.flatten.drop (((rows.map List.length).take i).sum) := by
        rw [← List.drop_drop,List.drop_left]
      simpa only [slice,List.map_cons,List.take_succ_cons,List.sum_cons,
        List.getD_cons_succ,List.flatten_cons,List.getElem_cons_succ,hs] using
        ih i (by simpa using hi)

theorem split_flatten {α : Type} (rows : List (List α)) :
    split (rows.map List.length) rows.flatten = rows := by
  apply List.ext_getElem
  · simp [split]
  · intro i hi hj
    simpa only [split,List.getElem_map,List.getElem_range] using slice_flatten rows i hj

#print axioms split_polyT
#print axioms split_flatten

end CSPConsequence.ListSlices
