import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_56076
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [2, 3]⟩,
        ⟨GateOp.or, [4, 6]⟩,
        ⟨GateOp.or, [0, 5]⟩,
        ⟨GateOp.not, [8]⟩,
        ⟨GateOp.not, [7]⟩,
        ⟨GateOp.and, [0, 10]⟩,
        ⟨GateOp.not, [1]⟩,
        ⟨GateOp.and, [9, 12]⟩,
        ⟨GateOp.and, [1, 8]⟩,
        ⟨GateOp.or, [11, 14]⟩,
        ⟨GateOp.or, [13, 15]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_56076

theorem PEqualNP.Outside.L_meta_56076 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (274843683 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_56076.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_56076.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
