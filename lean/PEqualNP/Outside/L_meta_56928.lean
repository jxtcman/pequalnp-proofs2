import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_56928
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.and, [5, 0]⟩,
        ⟨GateOp.or, [5, 2]⟩,
        ⟨GateOp.or, [6, 1]⟩,
        ⟨GateOp.not, [5]⟩,
        ⟨GateOp.and, [4, 9]⟩,
        ⟨GateOp.or, [0, 7]⟩,
        ⟨GateOp.or, [8, 10]⟩,
        ⟨GateOp.or, [7, 10]⟩,
        ⟨GateOp.not, [13]⟩,
        ⟨GateOp.and, [12, 11]⟩,
        ⟨GateOp.and, [14, 3]⟩,
        ⟨GateOp.or, [16, 15]⟩ ],
    output := 17 }

end PEqualNP.Outside.L_meta_56928

theorem PEqualNP.Outside.L_meta_56928 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2165562 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_56928.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_56928.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
