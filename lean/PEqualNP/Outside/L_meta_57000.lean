import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_57000
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [2, 0]⟩,
        ⟨GateOp.or, [3, 1]⟩,
        ⟨GateOp.or, [2, 1]⟩,
        ⟨GateOp.not, [8]⟩,
        ⟨GateOp.and, [7, 6]⟩,
        ⟨GateOp.and, [9, 0]⟩,
        ⟨GateOp.and, [9, 4]⟩,
        ⟨GateOp.or, [12, 5]⟩,
        ⟨GateOp.or, [13, 10]⟩,
        ⟨GateOp.not, [14]⟩,
        ⟨GateOp.or, [15, 11]⟩,
        ⟨GateOp.and, [12, 3]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_57000

theorem PEqualNP.Outside.L_meta_57000 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2180797 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_57000.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_57000.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
