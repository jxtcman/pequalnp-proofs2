import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53961
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [2, 1]⟩,
        ⟨GateOp.or, [4, 2]⟩,
        ⟨GateOp.or, [1, 5]⟩,
        ⟨GateOp.and, [7, 8]⟩,
        ⟨GateOp.not, [9]⟩,
        ⟨GateOp.or, [8, 3]⟩,
        ⟨GateOp.or, [7, 11]⟩,
        ⟨GateOp.and, [6, 10]⟩,
        ⟨GateOp.and, [0, 12]⟩,
        ⟨GateOp.or, [13, 14]⟩ ],
    output := 15 }

end PEqualNP.Outside.L_meta_53961

theorem PEqualNP.Outside.L_meta_53961 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (117438 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_53961.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_53961.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
