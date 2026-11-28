import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53400
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [0, 2]⟩,
        ⟨GateOp.or, [1, 3]⟩,
        ⟨GateOp.and, [0, 1]⟩,
        ⟨GateOp.and, [2, 3]⟩,
        ⟨GateOp.or, [7, 8]⟩,
        ⟨GateOp.not, [9]⟩,
        ⟨GateOp.or, [5, 6]⟩,
        ⟨GateOp.and, [10, 11]⟩ ],
    output := 12 }

end PEqualNP.Outside.L_meta_53400

theorem PEqualNP.Outside.L_meta_53400 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (807901 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_53400.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_53400.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
