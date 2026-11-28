import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54968
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.not, [5]⟩,
        ⟨GateOp.or, [4, 3]⟩,
        ⟨GateOp.or, [1, 2]⟩,
        ⟨GateOp.or, [1, 0]⟩,
        ⟨GateOp.or, [0, 1]⟩,
        ⟨GateOp.and, [8, 6]⟩,
        ⟨GateOp.or, [10, 11]⟩,
        ⟨GateOp.and, [10, 11]⟩,
        ⟨GateOp.not, [13]⟩,
        ⟨GateOp.or, [14, 7]⟩,
        ⟨GateOp.and, [15, 12]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_54968

theorem PEqualNP.Outside.L_meta_54968 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (118329 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_54968.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_54968.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
