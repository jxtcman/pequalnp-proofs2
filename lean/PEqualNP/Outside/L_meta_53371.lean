import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53371
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.not, [4]⟩,
        ⟨GateOp.or, [0, 5]⟩,
        ⟨GateOp.or, [0, 1]⟩,
        ⟨GateOp.or, [2, 3]⟩,
        ⟨GateOp.or, [3, 7]⟩,
        ⟨GateOp.and, [7, 8]⟩,
        ⟨GateOp.or, [2, 10]⟩,
        ⟨GateOp.and, [9, 11]⟩,
        ⟨GateOp.not, [12]⟩,
        ⟨GateOp.and, [6, 13]⟩ ],
    output := 14 }

end PEqualNP.Outside.L_meta_53371

theorem PEqualNP.Outside.L_meta_53371 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (266323 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_53371.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_53371.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
