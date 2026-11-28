import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54793
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [2, 1]⟩,
        ⟨GateOp.and, [6, 4]⟩,
        ⟨GateOp.or, [3, 0]⟩,
        ⟨GateOp.and, [2, 8]⟩,
        ⟨GateOp.or, [9, 7]⟩,
        ⟨GateOp.not, [10]⟩,
        ⟨GateOp.not, [5]⟩,
        ⟨GateOp.or, [0, 12]⟩,
        ⟨GateOp.or, [13, 6]⟩,
        ⟨GateOp.and, [14, 11]⟩ ],
    output := 15 }

end PEqualNP.Outside.L_meta_54793

theorem PEqualNP.Outside.L_meta_54793 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (274877371 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_54793.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_54793.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
