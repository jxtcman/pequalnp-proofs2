import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53388
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.not, [4]⟩,
        ⟨GateOp.and, [0, 1]⟩,
        ⟨GateOp.or, [2, 6]⟩,
        ⟨GateOp.or, [3, 7]⟩,
        ⟨GateOp.or, [0, 1]⟩,
        ⟨GateOp.and, [4, 9]⟩,
        ⟨GateOp.and, [5, 8]⟩,
        ⟨GateOp.or, [9, 11]⟩,
        ⟨GateOp.and, [11, 12]⟩,
        ⟨GateOp.or, [10, 13]⟩ ],
    output := 14 }

end PEqualNP.Outside.L_meta_53388

theorem PEqualNP.Outside.L_meta_53388 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (275358 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_53388.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_53388.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
