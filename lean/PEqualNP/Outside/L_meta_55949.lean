import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_55949
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [5, 2]⟩,
        ⟨GateOp.or, [0, 1]⟩,
        ⟨GateOp.or, [0, 3]⟩,
        ⟨GateOp.and, [4, 8]⟩,
        ⟨GateOp.or, [3, 6]⟩,
        ⟨GateOp.or, [5, 9]⟩,
        ⟨GateOp.or, [1, 11]⟩,
        ⟨GateOp.and, [7, 10]⟩,
        ⟨GateOp.not, [12]⟩,
        ⟨GateOp.not, [4]⟩,
        ⟨GateOp.or, [14, 13]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_55949

theorem PEqualNP.Outside.L_meta_55949 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (270650157 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_55949.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_55949.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
