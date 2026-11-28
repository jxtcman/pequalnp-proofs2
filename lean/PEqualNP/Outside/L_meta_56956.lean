import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_56956
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [3, 1]⟩,
        ⟨GateOp.or, [6, 0]⟩,
        ⟨GateOp.and, [2, 7]⟩,
        ⟨GateOp.or, [0, 4]⟩,
        ⟨GateOp.and, [9, 3]⟩,
        ⟨GateOp.or, [7, 2]⟩,
        ⟨GateOp.or, [10, 8]⟩,
        ⟨GateOp.or, [5, 12]⟩,
        ⟨GateOp.not, [13]⟩,
        ⟨GateOp.and, [5, 0]⟩,
        ⟨GateOp.or, [15, 14]⟩,
        ⟨GateOp.and, [11, 16]⟩ ],
    output := 17 }

end PEqualNP.Outside.L_meta_56956

theorem PEqualNP.Outside.L_meta_56956 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2180787 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_56956.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_56956.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
