import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_55407
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.and, [4, 3]⟩,
        ⟨GateOp.or, [5, 0]⟩,
        ⟨GateOp.or, [0, 1]⟩,
        ⟨GateOp.or, [6, 2]⟩,
        ⟨GateOp.or, [4, 3]⟩,
        ⟨GateOp.and, [10, 9]⟩,
        ⟨GateOp.and, [2, 1]⟩,
        ⟨GateOp.or, [10, 12]⟩,
        ⟨GateOp.not, [13]⟩,
        ⟨GateOp.and, [8, 14]⟩,
        ⟨GateOp.or, [11, 15]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_55407

theorem PEqualNP.Outside.L_meta_55407 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (4294823 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_55407.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_55407.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
