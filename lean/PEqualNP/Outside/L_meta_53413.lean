import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53413
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [1, 2]⟩,
        ⟨GateOp.or, [1, 3]⟩,
        ⟨GateOp.or, [0, 2]⟩,
        ⟨GateOp.and, [6, 7]⟩,
        ⟨GateOp.and, [0, 4]⟩,
        ⟨GateOp.or, [4, 8]⟩,
        ⟨GateOp.not, [10]⟩,
        ⟨GateOp.and, [5, 11]⟩,
        ⟨GateOp.or, [9, 12]⟩ ],
    output := 13 }

end PEqualNP.Outside.L_meta_53413

theorem PEqualNP.Outside.L_meta_53413 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4436 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_53413.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_53413.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
