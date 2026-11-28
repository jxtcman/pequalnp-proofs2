import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53485
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [2, 7]⟩,
        ⟨GateOp.or, [6, 1]⟩,
        ⟨GateOp.and, [10, 11]⟩,
        ⟨GateOp.or, [11, 2]⟩,
        ⟨GateOp.or, [12, 0]⟩,
        ⟨GateOp.or, [4, 5]⟩,
        ⟨GateOp.or, [9, 3]⟩,
        ⟨GateOp.or, [13, 16]⟩,
        ⟨GateOp.or, [17, 8]⟩,
        ⟨GateOp.or, [15, 14]⟩,
        ⟨GateOp.and, [18, 19]⟩ ],
    output := 20 }

end PEqualNP.Outside.L_meta_53485

theorem PEqualNP.Outside.L_meta_53485 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (815860 : ℕ).testBit (6 * u.val + v.val)) 11) := by
  unfold PEqualNP.Represents.RepSizeAtMost
  refine ⟨PEqualNP.Outside.L_meta_53485.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_53485.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · unfold PEqualNP.Represents.Represents
    decide +kernel
