import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_55860
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [3, 5]⟩,
        ⟨GateOp.or, [1, 5]⟩,
        ⟨GateOp.not, [1]⟩,
        ⟨GateOp.and, [0, 8]⟩,
        ⟨GateOp.or, [4, 7]⟩,
        ⟨GateOp.or, [2, 6]⟩,
        ⟨GateOp.and, [0, 7]⟩,
        ⟨GateOp.and, [10, 11]⟩,
        ⟨GateOp.or, [9, 13]⟩,
        ⟨GateOp.not, [14]⟩,
        ⟨GateOp.or, [12, 15]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_55860

theorem PEqualNP.Outside.L_meta_55860 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (270582946 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_55860.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_55860.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
