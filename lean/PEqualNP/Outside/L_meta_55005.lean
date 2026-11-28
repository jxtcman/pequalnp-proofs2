import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_55005
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [0, 3]⟩,
        ⟨GateOp.or, [4, 5]⟩,
        ⟨GateOp.not, [7]⟩,
        ⟨GateOp.and, [3, 2]⟩,
        ⟨GateOp.or, [9, 1]⟩,
        ⟨GateOp.or, [2, 6]⟩,
        ⟨GateOp.and, [10, 11]⟩,
        ⟨GateOp.or, [8, 0]⟩,
        ⟨GateOp.or, [1, 13]⟩,
        ⟨GateOp.not, [12]⟩,
        ⟨GateOp.and, [15, 14]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_55005

theorem PEqualNP.Outside.L_meta_55005 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2116797 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_55005.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_55005.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
