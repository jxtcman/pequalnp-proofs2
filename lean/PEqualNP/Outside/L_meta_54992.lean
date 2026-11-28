import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54992
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.not, [2]⟩,
        ⟨GateOp.or, [1, 2]⟩,
        ⟨GateOp.or, [3, 6]⟩,
        ⟨GateOp.and, [7, 8]⟩,
        ⟨GateOp.or, [4, 9]⟩,
        ⟨GateOp.not, [10]⟩,
        ⟨GateOp.not, [5]⟩,
        ⟨GateOp.or, [0, 11]⟩,
        ⟨GateOp.and, [1, 4]⟩,
        ⟨GateOp.and, [12, 13]⟩,
        ⟨GateOp.or, [14, 15]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_54992

theorem PEqualNP.Outside.L_meta_54992 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2114847 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_54992.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_54992.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
