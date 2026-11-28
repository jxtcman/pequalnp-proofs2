import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_57006
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [4, 2]⟩,
        ⟨GateOp.and, [6, 3]⟩,
        ⟨GateOp.not, [6]⟩,
        ⟨GateOp.or, [5, 7]⟩,
        ⟨GateOp.or, [2, 3]⟩,
        ⟨GateOp.not, [4]⟩,
        ⟨GateOp.and, [1, 6]⟩,
        ⟨GateOp.not, [9]⟩,
        ⟨GateOp.and, [11, 0]⟩,
        ⟨GateOp.and, [10, 13]⟩,
        ⟨GateOp.or, [14, 15]⟩,
        ⟨GateOp.or, [12, 16]⟩ ],
    output := 17 }

end PEqualNP.Outside.L_meta_57006

theorem PEqualNP.Outside.L_meta_57006 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2180911 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_57006.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_57006.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
