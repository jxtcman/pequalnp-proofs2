import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53520
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [8, 2]⟩,
        ⟨GateOp.or, [6, 0]⟩,
        ⟨GateOp.or, [7, 10]⟩,
        ⟨GateOp.or, [9, 12]⟩,
        ⟨GateOp.or, [6, 3]⟩,
        ⟨GateOp.or, [14, 12]⟩,
        ⟨GateOp.or, [5, 1]⟩,
        ⟨GateOp.and, [13, 11]⟩,
        ⟨GateOp.and, [15, 16]⟩,
        ⟨GateOp.or, [4, 17]⟩,
        ⟨GateOp.or, [19, 18]⟩ ],
    output := 20 }

end PEqualNP.Outside.L_meta_53520

theorem PEqualNP.Outside.L_meta_53520 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (817017 : ℕ).testBit (6 * u.val + v.val)) 11) := by
  unfold PEqualNP.Represents.RepSizeAtMost
  refine ⟨PEqualNP.Outside.L_meta_53520.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_53520.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · unfold PEqualNP.Represents.Represents
    decide +kernel
