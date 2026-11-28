import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53814
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [4, 5]⟩,
        ⟨GateOp.or, [3, 6]⟩,
        ⟨GateOp.and, [0, 6]⟩,
        ⟨GateOp.or, [0, 3]⟩,
        ⟨GateOp.and, [1, 9]⟩,
        ⟨GateOp.not, [7]⟩,
        ⟨GateOp.and, [2, 11]⟩,
        ⟨GateOp.or, [8, 12]⟩,
        ⟨GateOp.or, [10, 13]⟩ ],
    output := 14 }

end PEqualNP.Outside.L_meta_53814

theorem PEqualNP.Outside.L_meta_53814 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17206 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_53814.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_53814.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
