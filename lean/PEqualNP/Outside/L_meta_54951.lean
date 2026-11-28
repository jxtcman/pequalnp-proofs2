import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54951
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [4, 5]⟩,
        ⟨GateOp.or, [1, 6]⟩,
        ⟨GateOp.not, [7]⟩,
        ⟨GateOp.and, [2, 8]⟩,
        ⟨GateOp.or, [3, 7]⟩,
        ⟨GateOp.or, [2, 3]⟩,
        ⟨GateOp.not, [11]⟩,
        ⟨GateOp.and, [1, 12]⟩,
        ⟨GateOp.or, [9, 13]⟩,
        ⟨GateOp.and, [0, 10]⟩,
        ⟨GateOp.or, [14, 15]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_54951

theorem PEqualNP.Outside.L_meta_54951 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (52414 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_54951.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_54951.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
