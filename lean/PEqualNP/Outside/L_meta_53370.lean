import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53370
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.and, [1, 2]⟩,
        ⟨GateOp.or, [2, 4]⟩,
        ⟨GateOp.or, [3, 4]⟩,
        ⟨GateOp.and, [0, 3]⟩,
        ⟨GateOp.or, [5, 7]⟩,
        ⟨GateOp.or, [6, 8]⟩,
        ⟨GateOp.or, [1, 10]⟩,
        ⟨GateOp.or, [0, 9]⟩,
        ⟨GateOp.and, [11, 12]⟩,
        ⟨GateOp.not, [13]⟩ ],
    output := 14 }

end PEqualNP.Outside.L_meta_53370

theorem PEqualNP.Outside.L_meta_53370 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (266305 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_53370.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_53370.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
