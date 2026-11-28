import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53369
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.and, [0, 4]⟩,
        ⟨GateOp.or, [3, 4]⟩,
        ⟨GateOp.or, [1, 5]⟩,
        ⟨GateOp.and, [0, 2]⟩,
        ⟨GateOp.or, [0, 2]⟩,
        ⟨GateOp.not, [9]⟩,
        ⟨GateOp.and, [6, 9]⟩,
        ⟨GateOp.and, [7, 10]⟩,
        ⟨GateOp.or, [11, 12]⟩,
        ⟨GateOp.or, [8, 13]⟩ ],
    output := 14 }

end PEqualNP.Outside.L_meta_53369

theorem PEqualNP.Outside.L_meta_53369 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (25436 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_53369.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_53369.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
