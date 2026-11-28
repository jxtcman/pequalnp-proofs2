import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53807
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.not, [4]⟩,
        ⟨GateOp.or, [0, 6]⟩,
        ⟨GateOp.or, [1, 5]⟩,
        ⟨GateOp.or, [3, 8]⟩,
        ⟨GateOp.or, [2, 3]⟩,
        ⟨GateOp.not, [9]⟩,
        ⟨GateOp.and, [1, 10]⟩,
        ⟨GateOp.or, [11, 12]⟩,
        ⟨GateOp.and, [7, 13]⟩ ],
    output := 14 }

end PEqualNP.Outside.L_meta_53807

theorem PEqualNP.Outside.L_meta_53807 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17173 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_53807.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_53807.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
