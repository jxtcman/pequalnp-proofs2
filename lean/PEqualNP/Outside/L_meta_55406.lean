import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_55406
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [2, 3]⟩,
        ⟨GateOp.and, [3, 2]⟩,
        ⟨GateOp.and, [4, 6]⟩,
        ⟨GateOp.or, [6, 4]⟩,
        ⟨GateOp.or, [5, 2]⟩,
        ⟨GateOp.and, [0, 10]⟩,
        ⟨GateOp.not, [9]⟩,
        ⟨GateOp.and, [1, 12]⟩,
        ⟨GateOp.or, [13, 8]⟩,
        ⟨GateOp.or, [11, 14]⟩,
        ⟨GateOp.or, [15, 7]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_55406

theorem PEqualNP.Outside.L_meta_55406 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (4294822 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_55406.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_55406.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
