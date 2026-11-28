import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53381
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [2, 4]⟩,
        ⟨GateOp.or, [3, 4]⟩,
        ⟨GateOp.or, [0, 1]⟩,
        ⟨GateOp.or, [5, 7]⟩,
        ⟨GateOp.and, [0, 1]⟩,
        ⟨GateOp.and, [4, 7]⟩,
        ⟨GateOp.or, [6, 9]⟩,
        ⟨GateOp.and, [8, 11]⟩,
        ⟨GateOp.not, [12]⟩,
        ⟨GateOp.or, [10, 13]⟩ ],
    output := 14 }

end PEqualNP.Outside.L_meta_53381

theorem PEqualNP.Outside.L_meta_53381 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (266965 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_53381.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_53381.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
