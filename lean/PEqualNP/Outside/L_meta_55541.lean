import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_55541
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [4, 1]⟩,
        ⟨GateOp.or, [0, 3]⟩,
        ⟨GateOp.or, [6, 2]⟩,
        ⟨GateOp.or, [5, 3]⟩,
        ⟨GateOp.or, [4, 7]⟩,
        ⟨GateOp.not, [10]⟩,
        ⟨GateOp.and, [7, 6]⟩,
        ⟨GateOp.and, [0, 9]⟩,
        ⟨GateOp.or, [12, 11]⟩,
        ⟨GateOp.and, [14, 8]⟩,
        ⟨GateOp.or, [13, 15]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_55541

theorem PEqualNP.Outside.L_meta_55541 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (4344762 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_55541.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_55541.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
