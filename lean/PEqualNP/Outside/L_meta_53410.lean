import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53410
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [1, 4]⟩,
        ⟨GateOp.or, [3, 5]⟩,
        ⟨GateOp.and, [1, 3]⟩,
        ⟨GateOp.or, [0, 7]⟩,
        ⟨GateOp.or, [0, 6]⟩,
        ⟨GateOp.not, [9]⟩,
        ⟨GateOp.and, [6, 8]⟩,
        ⟨GateOp.or, [10, 11]⟩ ],
    output := 12 }

end PEqualNP.Outside.L_meta_53410

theorem PEqualNP.Outside.L_meta_53410 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4378 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_53410.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_53410.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
