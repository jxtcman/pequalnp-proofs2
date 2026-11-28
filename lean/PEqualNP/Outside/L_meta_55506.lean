import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_55506
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [4, 2]⟩,
        ⟨GateOp.or, [3, 0]⟩,
        ⟨GateOp.or, [5, 1]⟩,
        ⟨GateOp.and, [0, 8]⟩,
        ⟨GateOp.and, [8, 6]⟩,
        ⟨GateOp.and, [7, 4]⟩,
        ⟨GateOp.or, [9, 2]⟩,
        ⟨GateOp.or, [11, 1]⟩,
        ⟨GateOp.or, [13, 12]⟩,
        ⟨GateOp.not, [10]⟩,
        ⟨GateOp.and, [15, 14]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_55506

theorem PEqualNP.Outside.L_meta_55506 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (4311734 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_55506.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_55506.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
