import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_55956
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [2, 5]⟩,
        ⟨GateOp.or, [0, 1]⟩,
        ⟨GateOp.and, [5, 2]⟩,
        ⟨GateOp.or, [7, 8]⟩,
        ⟨GateOp.or, [7, 3]⟩,
        ⟨GateOp.not, [6]⟩,
        ⟨GateOp.or, [9, 11]⟩,
        ⟨GateOp.and, [4, 10]⟩,
        ⟨GateOp.not, [13]⟩,
        ⟨GateOp.or, [11, 14]⟩,
        ⟨GateOp.and, [14, 12]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_55956

theorem PEqualNP.Outside.L_meta_55956 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (270666671 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_55956.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_55956.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
