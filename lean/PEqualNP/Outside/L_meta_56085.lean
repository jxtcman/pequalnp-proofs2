import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_56085
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [2, 3]⟩,
        ⟨GateOp.and, [0, 5]⟩,
        ⟨GateOp.or, [1, 7]⟩,
        ⟨GateOp.or, [0, 6]⟩,
        ⟨GateOp.or, [1, 5]⟩,
        ⟨GateOp.or, [5, 9]⟩,
        ⟨GateOp.or, [4, 6]⟩,
        ⟨GateOp.not, [10]⟩,
        ⟨GateOp.and, [8, 11]⟩,
        ⟨GateOp.and, [12, 13]⟩,
        ⟨GateOp.or, [14, 15]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_56085

theorem PEqualNP.Outside.L_meta_56085 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (274844478 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_56085.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_56085.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
