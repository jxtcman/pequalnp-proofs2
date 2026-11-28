import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_55635
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [2, 1]⟩,
        ⟨GateOp.and, [3, 6]⟩,
        ⟨GateOp.or, [7, 0]⟩,
        ⟨GateOp.or, [6, 3]⟩,
        ⟨GateOp.or, [5, 8]⟩,
        ⟨GateOp.or, [4, 9]⟩,
        ⟨GateOp.and, [11, 10]⟩,
        ⟨GateOp.and, [1, 3]⟩,
        ⟨GateOp.or, [9, 0]⟩,
        ⟨GateOp.not, [12]⟩,
        ⟨GateOp.and, [14, 15]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_55635

theorem PEqualNP.Outside.L_meta_55635 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6374817 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_55635.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_55635.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
