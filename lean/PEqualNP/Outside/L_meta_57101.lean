import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_57101
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.not, [4]⟩,
        ⟨GateOp.not, [1]⟩,
        ⟨GateOp.or, [6, 2]⟩,
        ⟨GateOp.or, [5, 2]⟩,
        ⟨GateOp.or, [5, 3]⟩,
        ⟨GateOp.and, [9, 10]⟩,
        ⟨GateOp.or, [0, 1]⟩,
        ⟨GateOp.not, [11]⟩,
        ⟨GateOp.or, [13, 12]⟩,
        ⟨GateOp.and, [14, 8]⟩,
        ⟨GateOp.or, [7, 10]⟩,
        ⟨GateOp.and, [15, 16]⟩ ],
    output := 17 }

end PEqualNP.Outside.L_meta_57101

theorem PEqualNP.Outside.L_meta_57101 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2181677 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_57101.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_57101.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
