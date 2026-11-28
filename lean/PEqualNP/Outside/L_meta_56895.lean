import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_56895
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [4, 1]⟩,
        ⟨GateOp.or, [6, 5]⟩,
        ⟨GateOp.not, [2]⟩,
        ⟨GateOp.or, [3, 4]⟩,
        ⟨GateOp.and, [8, 9]⟩,
        ⟨GateOp.and, [10, 7]⟩,
        ⟨GateOp.and, [0, 7]⟩,
        ⟨GateOp.not, [11]⟩,
        ⟨GateOp.or, [6, 10]⟩,
        ⟨GateOp.or, [14, 12]⟩,
        ⟨GateOp.and, [15, 13]⟩,
        ⟨GateOp.not, [11]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_56895

theorem PEqualNP.Outside.L_meta_56895 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2165162 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_56895.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_56895.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
