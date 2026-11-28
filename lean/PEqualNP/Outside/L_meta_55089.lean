import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_55089
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [4, 2]⟩,
        ⟨GateOp.or, [1, 3]⟩,
        ⟨GateOp.or, [2, 3]⟩,
        ⟨GateOp.and, [1, 5]⟩,
        ⟨GateOp.and, [7, 6]⟩,
        ⟨GateOp.or, [5, 10]⟩,
        ⟨GateOp.not, [11]⟩,
        ⟨GateOp.and, [7, 1]⟩,
        ⟨GateOp.and, [8, 12]⟩,
        ⟨GateOp.or, [14, 0]⟩,
        ⟨GateOp.or, [15, 9]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_55089

theorem PEqualNP.Outside.L_meta_55089 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2181695 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_55089.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_55089.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
