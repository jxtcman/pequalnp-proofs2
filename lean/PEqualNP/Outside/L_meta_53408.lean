import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53408
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.and, [1, 3]⟩,
        ⟨GateOp.and, [0, 2]⟩,
        ⟨GateOp.or, [1, 6]⟩,
        ⟨GateOp.or, [3, 7]⟩,
        ⟨GateOp.not, [4]⟩,
        ⟨GateOp.not, [8]⟩,
        ⟨GateOp.or, [0, 9]⟩,
        ⟨GateOp.and, [10, 11]⟩,
        ⟨GateOp.or, [5, 12]⟩ ],
    output := 13 }

end PEqualNP.Outside.L_meta_53408

theorem PEqualNP.Outside.L_meta_53408 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4369 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_53408.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_53408.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
