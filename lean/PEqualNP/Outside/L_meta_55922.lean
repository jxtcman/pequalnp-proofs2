import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_55922
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [4, 3]⟩,
        ⟨GateOp.or, [3, 2]⟩,
        ⟨GateOp.and, [6, 1]⟩,
        ⟨GateOp.or, [0, 4]⟩,
        ⟨GateOp.and, [7, 9]⟩,
        ⟨GateOp.or, [10, 8]⟩,
        ⟨GateOp.not, [5]⟩,
        ⟨GateOp.or, [1, 0]⟩,
        ⟨GateOp.not, [11]⟩,
        ⟨GateOp.or, [13, 12]⟩,
        ⟨GateOp.and, [15, 14]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_55922

theorem PEqualNP.Outside.L_meta_55922 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (270584243 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_55922.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_55922.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
