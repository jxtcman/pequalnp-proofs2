import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53415
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.and, [1, 3]⟩,
        ⟨GateOp.or, [3, 4]⟩,
        ⟨GateOp.or, [0, 5]⟩,
        ⟨GateOp.and, [6, 7]⟩,
        ⟨GateOp.or, [0, 6]⟩,
        ⟨GateOp.not, [9]⟩,
        ⟨GateOp.or, [8, 10]⟩ ],
    output := 11 }

end PEqualNP.Outside.L_meta_53415

theorem PEqualNP.Outside.L_meta_53415 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4568 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_53415.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_53415.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
