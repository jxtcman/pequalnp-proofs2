import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_56074
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [1, 2]⟩,
        ⟨GateOp.and, [6, 0]⟩,
        ⟨GateOp.not, [5]⟩,
        ⟨GateOp.and, [3, 4]⟩,
        ⟨GateOp.and, [1, 2]⟩,
        ⟨GateOp.or, [9, 7]⟩,
        ⟨GateOp.or, [10, 11]⟩,
        ⟨GateOp.or, [6, 8]⟩,
        ⟨GateOp.or, [0, 13]⟩,
        ⟨GateOp.not, [12]⟩,
        ⟨GateOp.and, [14, 15]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_56074

theorem PEqualNP.Outside.L_meta_56074 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (270782137 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_56074.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_56074.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
