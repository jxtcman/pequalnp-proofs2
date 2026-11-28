import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_55537
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.and, [0, 1]⟩,
        ⟨GateOp.or, [2, 6]⟩,
        ⟨GateOp.not, [5]⟩,
        ⟨GateOp.or, [0, 1]⟩,
        ⟨GateOp.or, [4, 9]⟩,
        ⟨GateOp.or, [4, 5]⟩,
        ⟨GateOp.and, [9, 11]⟩,
        ⟨GateOp.and, [7, 8]⟩,
        ⟨GateOp.and, [3, 10]⟩,
        ⟨GateOp.or, [12, 14]⟩,
        ⟨GateOp.or, [13, 15]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_55537

theorem PEqualNP.Outside.L_meta_55537 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (4312894 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_55537.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_55537.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
