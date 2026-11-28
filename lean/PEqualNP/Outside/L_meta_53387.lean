import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53387
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [0, 1]⟩,
        ⟨GateOp.or, [2, 4]⟩,
        ⟨GateOp.and, [5, 6]⟩,
        ⟨GateOp.or, [1, 4]⟩,
        ⟨GateOp.or, [7, 8]⟩,
        ⟨GateOp.not, [9]⟩,
        ⟨GateOp.and, [7, 8]⟩,
        ⟨GateOp.or, [10, 11]⟩ ],
    output := 12 }

end PEqualNP.Outside.L_meta_53387

theorem PEqualNP.Outside.L_meta_53387 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (275097 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_53387.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_53387.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
