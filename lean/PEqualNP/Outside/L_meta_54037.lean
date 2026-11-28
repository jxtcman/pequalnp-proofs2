import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54037
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [0, 1]⟩,
        ⟨GateOp.or, [2, 6]⟩,
        ⟨GateOp.or, [4, 5]⟩,
        ⟨GateOp.or, [2, 8]⟩,
        ⟨GateOp.and, [7, 8]⟩,
        ⟨GateOp.not, [9]⟩,
        ⟨GateOp.or, [6, 11]⟩,
        ⟨GateOp.or, [2, 3]⟩,
        ⟨GateOp.and, [12, 13]⟩,
        ⟨GateOp.or, [10, 14]⟩ ],
    output := 15 }

end PEqualNP.Outside.L_meta_54037

theorem PEqualNP.Outside.L_meta_54037 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2297660 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_54037.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_54037.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
