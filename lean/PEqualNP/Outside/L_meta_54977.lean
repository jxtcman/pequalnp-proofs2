import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54977
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [4, 5]⟩,
        ⟨GateOp.not, [6]⟩,
        ⟨GateOp.and, [0, 7]⟩,
        ⟨GateOp.and, [2, 3]⟩,
        ⟨GateOp.or, [0, 9]⟩,
        ⟨GateOp.not, [10]⟩,
        ⟨GateOp.and, [7, 11]⟩,
        ⟨GateOp.not, [8]⟩,
        ⟨GateOp.or, [1, 13]⟩,
        ⟨GateOp.or, [0, 12]⟩,
        ⟨GateOp.and, [14, 15]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_54977

theorem PEqualNP.Outside.L_meta_54977 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2114482 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_54977.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_54977.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
