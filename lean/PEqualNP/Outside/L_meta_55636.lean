import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_55636
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [2, 1]⟩,
        ⟨GateOp.or, [6, 3]⟩,
        ⟨GateOp.or, [6, 0]⟩,
        ⟨GateOp.and, [5, 0]⟩,
        ⟨GateOp.not, [4]⟩,
        ⟨GateOp.and, [8, 3]⟩,
        ⟨GateOp.or, [5, 11]⟩,
        ⟨GateOp.not, [12]⟩,
        ⟨GateOp.or, [10, 7]⟩,
        ⟨GateOp.and, [13, 14]⟩,
        ⟨GateOp.or, [15, 9]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_55636

theorem PEqualNP.Outside.L_meta_55636 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6374823 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_55636.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_55636.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
