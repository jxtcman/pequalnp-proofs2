import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53406
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [3, 4]⟩,
        ⟨GateOp.or, [1, 5]⟩,
        ⟨GateOp.and, [0, 6]⟩,
        ⟨GateOp.or, [0, 5]⟩,
        ⟨GateOp.not, [8]⟩,
        ⟨GateOp.or, [7, 9]⟩ ],
    output := 10 }

end PEqualNP.Outside.L_meta_53406

theorem PEqualNP.Outside.L_meta_53406 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4314 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_53406.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_53406.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
