import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53808
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.and, [1, 3]⟩,
        ⟨GateOp.or, [3, 4]⟩,
        ⟨GateOp.or, [0, 6]⟩,
        ⟨GateOp.and, [7, 8]⟩,
        ⟨GateOp.or, [5, 7]⟩,
        ⟨GateOp.or, [0, 10]⟩,
        ⟨GateOp.not, [11]⟩,
        ⟨GateOp.and, [2, 12]⟩,
        ⟨GateOp.or, [9, 13]⟩ ],
    output := 14 }

end PEqualNP.Outside.L_meta_53808

theorem PEqualNP.Outside.L_meta_53808 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17176 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_53808.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_53808.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
