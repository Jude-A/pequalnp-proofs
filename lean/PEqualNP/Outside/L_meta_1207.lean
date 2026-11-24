import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1207 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 5) || (x 6 && x 7)) x := by
  refine ⟨{ gates := [⟨.or, [1, 2]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [1, 5]⟩,
    ⟨.and, [3, 10]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [4, 12]⟩, ⟨.and, [6, 7]⟩,
    ⟨.or, [9, 11]⟩, ⟨.or, [15, 13]⟩, ⟨.or, [16, 14]⟩], output := 17 }, ?_, by decide, ?_⟩
  · intro g hg
    simp at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    simp only [List.ofFn_succ, List.ofFn_zero, PEqualNP.CircuitLowerBounds.Circuit.eval,
      PEqualNP.CircuitLowerBounds.Circuit.wires, List.foldl_cons, List.foldl_nil,
      PEqualNP.CircuitLowerBounds.GateOp.eval, List.map_cons, List.map_nil,
      List.all_cons, List.all_nil, List.any_cons, List.any_nil, Bool.and_true, Bool.or_false, id]
    change
      ((((x 0 && (x 1 || x 2)) || (x 3 && (x 1 || x 5))) ||
        (x 4 && (x 2 || x 5))) || (x 6 && x 7)) = _
    simp only [Bool.and_or_distrib_left, Bool.and_comm,
      Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]
