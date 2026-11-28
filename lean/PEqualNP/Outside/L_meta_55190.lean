import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_55190
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [0, 4]⟩,
        ⟨GateOp.or, [5, 4]⟩,
        ⟨GateOp.or, [2, 0]⟩,
        ⟨GateOp.not, [7]⟩,
        ⟨GateOp.and, [3, 9]⟩,
        ⟨GateOp.not, [6]⟩,
        ⟨GateOp.and, [7, 8]⟩,
        ⟨GateOp.and, [12, 6]⟩,
        ⟨GateOp.or, [10, 1]⟩,
        ⟨GateOp.and, [14, 11]⟩,
        ⟨GateOp.or, [15, 13]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_55190

theorem PEqualNP.Outside.L_meta_55190 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2198448 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_55190.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_55190.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
