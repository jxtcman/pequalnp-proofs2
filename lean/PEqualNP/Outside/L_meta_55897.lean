import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_55897
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.not, [0]⟩,
        ⟨GateOp.or, [0, 2]⟩,
        ⟨GateOp.or, [7, 3]⟩,
        ⟨GateOp.and, [4, 8]⟩,
        ⟨GateOp.and, [5, 6]⟩,
        ⟨GateOp.or, [10, 7]⟩,
        ⟨GateOp.and, [11, 1]⟩,
        ⟨GateOp.or, [1, 10]⟩,
        ⟨GateOp.or, [13, 9]⟩,
        ⟨GateOp.not, [14]⟩,
        ⟨GateOp.or, [15, 12]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_55897

theorem PEqualNP.Outside.L_meta_55897 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (270584111 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_55897.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_55897.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
