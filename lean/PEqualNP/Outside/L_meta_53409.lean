import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53409
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.not, [1]⟩,
        ⟨GateOp.or, [0, 3]⟩,
        ⟨GateOp.or, [2, 3]⟩,
        ⟨GateOp.or, [4, 6]⟩,
        ⟨GateOp.and, [5, 7]⟩,
        ⟨GateOp.or, [6, 9]⟩,
        ⟨GateOp.and, [8, 9]⟩,
        ⟨GateOp.not, [11]⟩,
        ⟨GateOp.and, [10, 12]⟩ ],
    output := 13 }

end PEqualNP.Outside.L_meta_53409

theorem PEqualNP.Outside.L_meta_53409 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4371 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_53409.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_53409.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
