import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_55697
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [5, 4]⟩,
        ⟨GateOp.or, [2, 5]⟩,
        ⟨GateOp.not, [7]⟩,
        ⟨GateOp.and, [6, 2]⟩,
        ⟨GateOp.and, [1, 0]⟩,
        ⟨GateOp.and, [8, 3]⟩,
        ⟨GateOp.not, [10]⟩,
        ⟨GateOp.or, [9, 11]⟩,
        ⟨GateOp.or, [13, 0]⟩,
        ⟨GateOp.or, [1, 14]⟩,
        ⟨GateOp.and, [12, 15]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_55697

theorem PEqualNP.Outside.L_meta_55697 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6492093 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_55697.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_55697.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
