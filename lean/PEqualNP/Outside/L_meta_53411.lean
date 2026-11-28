import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53411
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.and, [0, 3]⟩,
        ⟨GateOp.or, [0, 2]⟩,
        ⟨GateOp.or, [1, 2]⟩,
        ⟨GateOp.or, [1, 3]⟩,
        ⟨GateOp.and, [6, 8]⟩,
        ⟨GateOp.or, [4, 9]⟩,
        ⟨GateOp.not, [10]⟩,
        ⟨GateOp.and, [7, 11]⟩,
        ⟨GateOp.or, [5, 12]⟩ ],
    output := 13 }

end PEqualNP.Outside.L_meta_53411

theorem PEqualNP.Outside.L_meta_53411 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4428 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_53411.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_53411.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
