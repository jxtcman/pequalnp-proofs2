import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53824
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [1, 5]⟩,
        ⟨GateOp.or, [3, 4]⟩,
        ⟨GateOp.or, [6, 7]⟩,
        ⟨GateOp.or, [0, 1]⟩,
        ⟨GateOp.and, [7, 9]⟩,
        ⟨GateOp.not, [8]⟩,
        ⟨GateOp.and, [2, 11]⟩,
        ⟨GateOp.or, [10, 12]⟩ ],
    output := 13 }

end PEqualNP.Outside.L_meta_53824

theorem PEqualNP.Outside.L_meta_53824 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17948 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_53824.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_53824.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
