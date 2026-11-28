import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53395
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.not, [4]⟩,
        ⟨GateOp.and, [2, 5]⟩,
        ⟨GateOp.not, [6]⟩,
        ⟨GateOp.and, [0, 4]⟩,
        ⟨GateOp.or, [0, 7]⟩,
        ⟨GateOp.or, [2, 8]⟩,
        ⟨GateOp.or, [1, 10]⟩,
        ⟨GateOp.and, [3, 5]⟩,
        ⟨GateOp.and, [9, 11]⟩,
        ⟨GateOp.or, [12, 13]⟩ ],
    output := 14 }

end PEqualNP.Outside.L_meta_53395

theorem PEqualNP.Outside.L_meta_53395 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (287582 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_53395.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_53395.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
