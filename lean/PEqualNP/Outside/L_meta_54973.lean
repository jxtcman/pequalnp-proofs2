import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54973
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [4, 3]⟩,
        ⟨GateOp.or, [2, 1]⟩,
        ⟨GateOp.or, [7, 4]⟩,
        ⟨GateOp.or, [1, 6]⟩,
        ⟨GateOp.and, [6, 8]⟩,
        ⟨GateOp.and, [9, 0]⟩,
        ⟨GateOp.or, [5, 0]⟩,
        ⟨GateOp.or, [10, 12]⟩,
        ⟨GateOp.or, [7, 7]⟩,
        ⟨GateOp.not, [13]⟩,
        ⟨GateOp.or, [11, 15]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_54973

theorem PEqualNP.Outside.L_meta_54973 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2113946 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_54973.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_54973.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
