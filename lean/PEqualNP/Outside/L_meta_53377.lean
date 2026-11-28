import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53377
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.and, [2, 3]⟩,
        ⟨GateOp.or, [1, 4]⟩,
        ⟨GateOp.and, [1, 4]⟩,
        ⟨GateOp.or, [5, 6]⟩,
        ⟨GateOp.or, [0, 7]⟩,
        ⟨GateOp.not, [8]⟩,
        ⟨GateOp.or, [9, 10]⟩ ],
    output := 11 }

end PEqualNP.Outside.L_meta_53377

theorem PEqualNP.Outside.L_meta_53377 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (266783 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_53377.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_53377.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
