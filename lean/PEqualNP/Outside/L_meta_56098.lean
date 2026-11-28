import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_56098
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [1, 3]⟩,
        ⟨GateOp.and, [2, 6]⟩,
        ⟨GateOp.not, [5]⟩,
        ⟨GateOp.or, [7, 4]⟩,
        ⟨GateOp.or, [0, 9]⟩,
        ⟨GateOp.or, [1, 2]⟩,
        ⟨GateOp.or, [11, 8]⟩,
        ⟨GateOp.and, [10, 11]⟩,
        ⟨GateOp.or, [12, 0]⟩,
        ⟨GateOp.not, [13]⟩,
        ⟨GateOp.and, [14, 15]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_56098

theorem PEqualNP.Outside.L_meta_56098 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (274877113 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_56098.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_56098.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
