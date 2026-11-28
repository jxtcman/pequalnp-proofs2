import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_55953
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [0, 5]⟩,
        ⟨GateOp.and, [5, 1]⟩,
        ⟨GateOp.or, [1, 3]⟩,
        ⟨GateOp.or, [5, 4]⟩,
        ⟨GateOp.or, [9, 8]⟩,
        ⟨GateOp.and, [0, 10]⟩,
        ⟨GateOp.and, [9, 8]⟩,
        ⟨GateOp.or, [6, 12]⟩,
        ⟨GateOp.not, [13]⟩,
        ⟨GateOp.or, [11, 14]⟩,
        ⟨GateOp.or, [15, 7]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_55953

theorem PEqualNP.Outside.L_meta_55953 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (270650298 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_55953.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_55953.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
