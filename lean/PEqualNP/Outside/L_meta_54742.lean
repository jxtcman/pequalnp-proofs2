import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54742
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.and, [1, 5]⟩,
        ⟨GateOp.or, [0, 6]⟩,
        ⟨GateOp.and, [3, 4]⟩,
        ⟨GateOp.or, [2, 2]⟩,
        ⟨GateOp.or, [5, 8]⟩,
        ⟨GateOp.not, [1]⟩,
        ⟨GateOp.not, [10]⟩,
        ⟨GateOp.or, [9, 11]⟩,
        ⟨GateOp.and, [12, 13]⟩,
        ⟨GateOp.or, [7, 14]⟩ ],
    output := 15 }

end PEqualNP.Outside.L_meta_54742

theorem PEqualNP.Outside.L_meta_54742 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (270649663 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_54742.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_54742.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
