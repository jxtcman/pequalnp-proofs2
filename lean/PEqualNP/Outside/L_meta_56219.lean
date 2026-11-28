import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_56219
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [2, 3]⟩,
        ⟨GateOp.or, [1, 0]⟩,
        ⟨GateOp.not, [5]⟩,
        ⟨GateOp.or, [8, 6]⟩,
        ⟨GateOp.and, [1, 6]⟩,
        ⟨GateOp.or, [2, 4]⟩,
        ⟨GateOp.and, [11, 3]⟩,
        ⟨GateOp.or, [10, 12]⟩,
        ⟨GateOp.or, [9, 7]⟩,
        ⟨GateOp.not, [13]⟩,
        ⟨GateOp.and, [14, 15]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_56219

theorem PEqualNP.Outside.L_meta_56219 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (279137471 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_56219.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_56219.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
