import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53383
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.and, [1, 4]⟩,
        ⟨GateOp.and, [2, 3]⟩,
        ⟨GateOp.or, [4, 6]⟩,
        ⟨GateOp.or, [2, 3]⟩,
        ⟨GateOp.not, [7]⟩,
        ⟨GateOp.and, [8, 9]⟩,
        ⟨GateOp.or, [0, 10]⟩,
        ⟨GateOp.or, [5, 11]⟩ ],
    output := 12 }

end PEqualNP.Outside.L_meta_53383

theorem PEqualNP.Outside.L_meta_53383 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (267167 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_53383.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_53383.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
