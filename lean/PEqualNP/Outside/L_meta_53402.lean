import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53402
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [2, 4]⟩,
        ⟨GateOp.or, [0, 4]⟩,
        ⟨GateOp.and, [5, 6]⟩,
        ⟨GateOp.or, [3, 7]⟩,
        ⟨GateOp.or, [0, 3]⟩,
        ⟨GateOp.and, [4, 9]⟩,
        ⟨GateOp.or, [2, 10]⟩,
        ⟨GateOp.or, [1, 11]⟩,
        ⟨GateOp.and, [8, 12]⟩,
        ⟨GateOp.not, [13]⟩ ],
    output := 14 }

end PEqualNP.Outside.L_meta_53402

theorem PEqualNP.Outside.L_meta_53402 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (17043659 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_53402.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_53402.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
