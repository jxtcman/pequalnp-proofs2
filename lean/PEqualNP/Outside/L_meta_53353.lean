import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53353
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [0, 3]⟩,
        ⟨GateOp.not, [2]⟩,
        ⟨GateOp.not, [5]⟩,
        ⟨GateOp.or, [1, 3]⟩,
        ⟨GateOp.and, [1, 7]⟩,
        ⟨GateOp.and, [6, 8]⟩,
        ⟨GateOp.and, [6, 9]⟩,
        ⟨GateOp.not, [10]⟩,
        ⟨GateOp.and, [5, 12]⟩,
        ⟨GateOp.or, [11, 13]⟩ ],
    output := 14 }

end PEqualNP.Outside.L_meta_53353

theorem PEqualNP.Outside.L_meta_53353 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (8789 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_53353.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_53353.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
