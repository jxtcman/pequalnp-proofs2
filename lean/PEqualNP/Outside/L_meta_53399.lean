import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53399
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [0, 1]⟩,
        ⟨GateOp.or, [2, 5]⟩,
        ⟨GateOp.or, [3, 6]⟩,
        ⟨GateOp.and, [3, 6]⟩,
        ⟨GateOp.not, [8]⟩,
        ⟨GateOp.and, [7, 9]⟩ ],
    output := 10 }

end PEqualNP.Outside.L_meta_53399

theorem PEqualNP.Outside.L_meta_53399 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (807639 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_53399.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_53399.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
