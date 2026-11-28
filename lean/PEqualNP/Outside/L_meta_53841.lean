import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53841
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.and, [0, 1]⟩,
        ⟨GateOp.or, [0, 1]⟩,
        ⟨GateOp.or, [4, 6]⟩,
        ⟨GateOp.or, [5, 8]⟩,
        ⟨GateOp.and, [2, 3]⟩,
        ⟨GateOp.or, [7, 10]⟩,
        ⟨GateOp.not, [9]⟩,
        ⟨GateOp.and, [11, 12]⟩ ],
    output := 13 }

end PEqualNP.Outside.L_meta_53841

theorem PEqualNP.Outside.L_meta_53841 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (33677 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_53841.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_53841.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
