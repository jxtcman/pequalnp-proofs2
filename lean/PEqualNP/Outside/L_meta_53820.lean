import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53820
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.not, [3]⟩,
        ⟨GateOp.not, [0]⟩,
        ⟨GateOp.or, [1, 6]⟩,
        ⟨GateOp.or, [0, 4]⟩,
        ⟨GateOp.or, [5, 9]⟩,
        ⟨GateOp.or, [1, 7]⟩,
        ⟨GateOp.and, [10, 11]⟩,
        ⟨GateOp.not, [12]⟩,
        ⟨GateOp.and, [8, 13]⟩ ],
    output := 14 }

end PEqualNP.Outside.L_meta_53820

theorem PEqualNP.Outside.L_meta_53820 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17333 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_53820.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_53820.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
