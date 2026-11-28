import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53366
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [0, 2]⟩,
        ⟨GateOp.and, [2, 4]⟩,
        ⟨GateOp.or, [1, 6]⟩,
        ⟨GateOp.and, [5, 7]⟩,
        ⟨GateOp.or, [1, 5]⟩,
        ⟨GateOp.not, [8]⟩,
        ⟨GateOp.and, [9, 10]⟩ ],
    output := 11 }

end PEqualNP.Outside.L_meta_53366

theorem PEqualNP.Outside.L_meta_53366 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (13149 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_53366.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_53366.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
