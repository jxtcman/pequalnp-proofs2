import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53391
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [0, 2]⟩,
        ⟨GateOp.and, [1, 2]⟩,
        ⟨GateOp.not, [4]⟩,
        ⟨GateOp.or, [1, 5]⟩,
        ⟨GateOp.and, [3, 8]⟩,
        ⟨GateOp.or, [6, 9]⟩,
        ⟨GateOp.not, [10]⟩,
        ⟨GateOp.or, [0, 11]⟩,
        ⟨GateOp.or, [7, 8]⟩,
        ⟨GateOp.and, [12, 13]⟩ ],
    output := 14 }

end PEqualNP.Outside.L_meta_53391

theorem PEqualNP.Outside.L_meta_53391 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (283231 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_53391.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_53391.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
