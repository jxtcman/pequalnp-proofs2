import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_57107
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [2, 4]⟩,
        ⟨GateOp.not, [1]⟩,
        ⟨GateOp.or, [5, 2]⟩,
        ⟨GateOp.and, [6, 3]⟩,
        ⟨GateOp.or, [9, 7]⟩,
        ⟨GateOp.or, [8, 3]⟩,
        ⟨GateOp.and, [5, 10]⟩,
        ⟨GateOp.and, [0, 7]⟩,
        ⟨GateOp.or, [9, 12]⟩,
        ⟨GateOp.not, [14]⟩,
        ⟨GateOp.and, [11, 15]⟩,
        ⟨GateOp.or, [13, 16]⟩ ],
    output := 17 }

end PEqualNP.Outside.L_meta_57107

theorem PEqualNP.Outside.L_meta_57107 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2181949 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_57107.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_57107.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
