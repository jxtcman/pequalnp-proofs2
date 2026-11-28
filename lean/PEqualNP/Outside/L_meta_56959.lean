import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_56959
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [2, 1]⟩,
        ⟨GateOp.or, [1, 3]⟩,
        ⟨GateOp.and, [7, 2]⟩,
        ⟨GateOp.not, [6]⟩,
        ⟨GateOp.or, [5, 0]⟩,
        ⟨GateOp.and, [4, 9]⟩,
        ⟨GateOp.and, [9, 0]⟩,
        ⟨GateOp.or, [10, 8]⟩,
        ⟨GateOp.or, [13, 11]⟩,
        ⟨GateOp.not, [14]⟩,
        ⟨GateOp.or, [0, 12]⟩,
        ⟨GateOp.or, [12, 15]⟩ ],
    output := 17 }

end PEqualNP.Outside.L_meta_56959

theorem PEqualNP.Outside.L_meta_56959 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2180793 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_56959.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_56959.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
