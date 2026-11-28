import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53360
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [2, 3]⟩,
        ⟨GateOp.and, [1, 1]⟩,
        ⟨GateOp.or, [1, 4]⟩,
        ⟨GateOp.or, [2, 6]⟩,
        ⟨GateOp.and, [5, 7]⟩,
        ⟨GateOp.not, [9]⟩,
        ⟨GateOp.or, [4, 5]⟩,
        ⟨GateOp.and, [0, 11]⟩,
        ⟨GateOp.and, [8, 10]⟩,
        ⟨GateOp.or, [12, 13]⟩ ],
    output := 14 }

end PEqualNP.Outside.L_meta_53360

theorem PEqualNP.Outside.L_meta_53360 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (12894 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_53360.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_53360.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
