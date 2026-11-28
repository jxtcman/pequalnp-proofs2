import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53401
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [1, 2]⟩,
        ⟨GateOp.or, [5, 0]⟩,
        ⟨GateOp.and, [1, 2]⟩,
        ⟨GateOp.or, [6, 5]⟩,
        ⟨GateOp.and, [5, 3]⟩,
        ⟨GateOp.or, [3, 8]⟩,
        ⟨GateOp.and, [4, 10]⟩,
        ⟨GateOp.or, [9, 11]⟩,
        ⟨GateOp.or, [7, 12]⟩,
        ⟨GateOp.not, [13]⟩ ],
    output := 14 }

end PEqualNP.Outside.L_meta_53401

theorem PEqualNP.Outside.L_meta_53401 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (17043535 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_53401.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_53401.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
