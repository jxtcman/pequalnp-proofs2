import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53816
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.and, [0, 2]⟩,
        ⟨GateOp.not, [1]⟩,
        ⟨GateOp.and, [3, 7]⟩,
        ⟨GateOp.or, [5, 6]⟩,
        ⟨GateOp.or, [4, 8]⟩,
        ⟨GateOp.not, [10]⟩,
        ⟨GateOp.not, [9]⟩,
        ⟨GateOp.or, [0, 11]⟩,
        ⟨GateOp.and, [12, 13]⟩ ],
    output := 14 }

end PEqualNP.Outside.L_meta_53816

theorem PEqualNP.Outside.L_meta_53816 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17307 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_53816.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_53816.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
