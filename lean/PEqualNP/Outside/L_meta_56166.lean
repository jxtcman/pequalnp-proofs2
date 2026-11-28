import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_56166
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [1, 0]⟩,
        ⟨GateOp.not, [6]⟩,
        ⟨GateOp.and, [7, 5]⟩,
        ⟨GateOp.or, [3, 5]⟩,
        ⟨GateOp.or, [9, 0]⟩,
        ⟨GateOp.and, [10, 2]⟩,
        ⟨GateOp.or, [2, 8]⟩,
        ⟨GateOp.and, [3, 6]⟩,
        ⟨GateOp.or, [12, 13]⟩,
        ⟨GateOp.not, [14]⟩,
        ⟨GateOp.or, [15, 11]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_56166

theorem PEqualNP.Outside.L_meta_56166 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (274894007 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_56166.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_56166.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
