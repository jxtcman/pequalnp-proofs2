import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_56343
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [5, 3]⟩,
        ⟨GateOp.or, [5, 4]⟩,
        ⟨GateOp.or, [3, 2]⟩,
        ⟨GateOp.and, [8, 7]⟩,
        ⟨GateOp.and, [6, 1]⟩,
        ⟨GateOp.or, [10, 9]⟩,
        ⟨GateOp.or, [0, 5]⟩,
        ⟨GateOp.or, [2, 4]⟩,
        ⟨GateOp.and, [12, 13]⟩,
        ⟨GateOp.or, [11, 14]⟩,
        ⟨GateOp.not, [15]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_56343

theorem PEqualNP.Outside.L_meta_56343 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (34630321579 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_56343.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_56343.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
