import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_56951
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.and, [4, 1]⟩,
        ⟨GateOp.or, [5, 3]⟩,
        ⟨GateOp.or, [1, 7]⟩,
        ⟨GateOp.or, [5, 2]⟩,
        ⟨GateOp.not, [4]⟩,
        ⟨GateOp.and, [9, 8]⟩,
        ⟨GateOp.not, [11]⟩,
        ⟨GateOp.and, [10, 7]⟩,
        ⟨GateOp.or, [13, 6]⟩,
        ⟨GateOp.or, [9, 14]⟩,
        ⟨GateOp.or, [0, 12]⟩,
        ⟨GateOp.and, [15, 16]⟩ ],
    output := 17 }

end PEqualNP.Outside.L_meta_56951

theorem PEqualNP.Outside.L_meta_56951 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2180652 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_56951.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_56951.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
