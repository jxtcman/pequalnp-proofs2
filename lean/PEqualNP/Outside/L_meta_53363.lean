import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53363
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [1, 4]⟩,
        ⟨GateOp.or, [3, 4]⟩,
        ⟨GateOp.and, [0, 5]⟩,
        ⟨GateOp.or, [0, 1]⟩,
        ⟨GateOp.not, [5]⟩,
        ⟨GateOp.and, [2, 9]⟩,
        ⟨GateOp.or, [6, 7]⟩,
        ⟨GateOp.or, [8, 8]⟩,
        ⟨GateOp.and, [11, 12]⟩,
        ⟨GateOp.or, [10, 13]⟩ ],
    output := 14 }

end PEqualNP.Outside.L_meta_53363

theorem PEqualNP.Outside.L_meta_53363 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (13086 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_53363.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_53363.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
