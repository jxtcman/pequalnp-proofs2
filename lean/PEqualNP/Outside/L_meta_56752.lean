import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_56752
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [1, 4]⟩,
        ⟨GateOp.or, [3, 2]⟩,
        ⟨GateOp.and, [7, 6]⟩,
        ⟨GateOp.or, [1, 7]⟩,
        ⟨GateOp.or, [1, 0]⟩,
        ⟨GateOp.and, [10, 4]⟩,
        ⟨GateOp.or, [5, 8]⟩,
        ⟨GateOp.not, [10]⟩,
        ⟨GateOp.or, [9, 11]⟩,
        ⟨GateOp.not, [12]⟩,
        ⟨GateOp.or, [2, 12]⟩,
        ⟨GateOp.and, [14, 15]⟩ ],
    output := 17 }

end PEqualNP.Outside.L_meta_56752

theorem PEqualNP.Outside.L_meta_56752 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2147486 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_56752.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_56752.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
