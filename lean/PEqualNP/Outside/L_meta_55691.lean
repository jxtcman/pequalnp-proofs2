import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_55691
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [3, 0]⟩,
        ⟨GateOp.or, [2, 0]⟩,
        ⟨GateOp.and, [1, 6]⟩,
        ⟨GateOp.not, [4]⟩,
        ⟨GateOp.not, [5]⟩,
        ⟨GateOp.and, [9, 7]⟩,
        ⟨GateOp.and, [10, 6]⟩,
        ⟨GateOp.or, [1, 12]⟩,
        ⟨GateOp.or, [13, 11]⟩,
        ⟨GateOp.not, [8]⟩,
        ⟨GateOp.and, [14, 15]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_55691

theorem PEqualNP.Outside.L_meta_55691 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6475197 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_55691.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_55691.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
