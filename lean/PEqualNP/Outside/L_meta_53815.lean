import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53815
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [0, 2]⟩,
        ⟨GateOp.or, [0, 3]⟩,
        ⟨GateOp.or, [5, 7]⟩,
        ⟨GateOp.or, [4, 8]⟩,
        ⟨GateOp.and, [2, 9]⟩,
        ⟨GateOp.not, [10]⟩,
        ⟨GateOp.and, [6, 11]⟩,
        ⟨GateOp.and, [1, 7]⟩,
        ⟨GateOp.or, [12, 13]⟩ ],
    output := 14 }

end PEqualNP.Outside.L_meta_53815

theorem PEqualNP.Outside.L_meta_53815 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17211 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_53815.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_53815.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
