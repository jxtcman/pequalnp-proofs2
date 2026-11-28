import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_55068
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.and, [4, 2]⟩,
        ⟨GateOp.or, [2, 5]⟩,
        ⟨GateOp.or, [6, 1]⟩,
        ⟨GateOp.or, [7, 4]⟩,
        ⟨GateOp.not, [1]⟩,
        ⟨GateOp.and, [7, 8]⟩,
        ⟨GateOp.and, [0, 10]⟩,
        ⟨GateOp.not, [9]⟩,
        ⟨GateOp.and, [3, 13]⟩,
        ⟨GateOp.or, [11, 14]⟩,
        ⟨GateOp.or, [15, 12]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_55068

theorem PEqualNP.Outside.L_meta_55068 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2165565 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_55068.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_55068.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
