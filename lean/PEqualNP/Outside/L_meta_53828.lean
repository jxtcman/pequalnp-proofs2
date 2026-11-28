import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53828
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [0, 1]⟩,
        ⟨GateOp.not, [6]⟩,
        ⟨GateOp.or, [3, 4]⟩,
        ⟨GateOp.and, [7, 8]⟩,
        ⟨GateOp.or, [0, 2]⟩,
        ⟨GateOp.and, [1, 10]⟩,
        ⟨GateOp.or, [9, 11]⟩,
        ⟨GateOp.or, [5, 12]⟩,
        ⟨GateOp.not, [13]⟩ ],
    output := 14 }

end PEqualNP.Outside.L_meta_53828

theorem PEqualNP.Outside.L_meta_53828 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (18077 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_53828.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_53828.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
