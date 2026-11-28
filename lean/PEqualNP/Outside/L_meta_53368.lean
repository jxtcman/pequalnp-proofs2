import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53368
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [3, 4]⟩,
        ⟨GateOp.and, [2, 5]⟩,
        ⟨GateOp.and, [0, 1]⟩,
        ⟨GateOp.or, [2, 7]⟩,
        ⟨GateOp.not, [8]⟩,
        ⟨GateOp.or, [0, 1]⟩,
        ⟨GateOp.and, [9, 10]⟩,
        ⟨GateOp.or, [6, 11]⟩ ],
    output := 12 }

end PEqualNP.Outside.L_meta_53368

theorem PEqualNP.Outside.L_meta_53368 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (25433 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_53368.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_53368.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
