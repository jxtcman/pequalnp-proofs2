import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54780
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [5, 4]⟩,
        ⟨GateOp.or, [0, 5]⟩,
        ⟨GateOp.or, [6, 3]⟩,
        ⟨GateOp.or, [0, 1]⟩,
        ⟨GateOp.and, [1, 8]⟩,
        ⟨GateOp.and, [8, 9]⟩,
        ⟨GateOp.or, [10, 7]⟩,
        ⟨GateOp.not, [12]⟩,
        ⟨GateOp.and, [7, 11]⟩,
        ⟨GateOp.or, [14, 13]⟩ ],
    output := 15 }

end PEqualNP.Outside.L_meta_54780

theorem PEqualNP.Outside.L_meta_54780 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (274844088 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_54780.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_54780.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
