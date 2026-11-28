import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53396
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.not, [0]⟩,
        ⟨GateOp.and, [2, 4]⟩,
        ⟨GateOp.or, [1, 6]⟩,
        ⟨GateOp.and, [5, 7]⟩,
        ⟨GateOp.or, [1, 5]⟩,
        ⟨GateOp.not, [3]⟩,
        ⟨GateOp.or, [4, 10]⟩,
        ⟨GateOp.and, [9, 11]⟩,
        ⟨GateOp.not, [12]⟩,
        ⟨GateOp.or, [8, 13]⟩ ],
    output := 14 }

end PEqualNP.Outside.L_meta_53396

theorem PEqualNP.Outside.L_meta_53396 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (287709 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_53396.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_53396.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
