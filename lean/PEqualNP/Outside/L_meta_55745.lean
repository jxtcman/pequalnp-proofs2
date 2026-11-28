import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_55745
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.not, [2]⟩,
        ⟨GateOp.not, [5]⟩,
        ⟨GateOp.and, [7, 3]⟩,
        ⟨GateOp.or, [5, 4]⟩,
        ⟨GateOp.and, [0, 9]⟩,
        ⟨GateOp.or, [0, 9]⟩,
        ⟨GateOp.or, [10, 1]⟩,
        ⟨GateOp.and, [11, 2]⟩,
        ⟨GateOp.and, [6, 12]⟩,
        ⟨GateOp.or, [13, 14]⟩,
        ⟨GateOp.or, [8, 15]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_55745

theorem PEqualNP.Outside.L_meta_55745 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6524606 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_55745.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_55745.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
