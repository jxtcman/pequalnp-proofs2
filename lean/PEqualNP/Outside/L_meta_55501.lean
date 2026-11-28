import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_55501
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [4, 1]⟩,
        ⟨GateOp.or, [1, 0]⟩,
        ⟨GateOp.or, [0, 2]⟩,
        ⟨GateOp.or, [5, 7]⟩,
        ⟨GateOp.and, [6, 3]⟩,
        ⟨GateOp.and, [9, 2]⟩,
        ⟨GateOp.or, [10, 8]⟩,
        ⟨GateOp.not, [11]⟩,
        ⟨GateOp.and, [12, 13]⟩,
        ⟨GateOp.and, [7, 5]⟩,
        ⟨GateOp.or, [14, 15]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_55501

theorem PEqualNP.Outside.L_meta_55501 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (4311611 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_55501.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_55501.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
