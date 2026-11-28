import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54748
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [5, 3]⟩,
        ⟨GateOp.or, [5, 1]⟩,
        ⟨GateOp.or, [4, 0]⟩,
        ⟨GateOp.and, [3, 8]⟩,
        ⟨GateOp.or, [9, 7]⟩,
        ⟨GateOp.or, [1, 0]⟩,
        ⟨GateOp.not, [10]⟩,
        ⟨GateOp.and, [11, 6]⟩,
        ⟨GateOp.and, [13, 7]⟩,
        ⟨GateOp.or, [12, 14]⟩ ],
    output := 15 }

end PEqualNP.Outside.L_meta_54748

theorem PEqualNP.Outside.L_meta_54748 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (270649909 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_54748.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_54748.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
