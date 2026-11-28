import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53505
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [9, 3]⟩,
        ⟨GateOp.or, [7, 2]⟩,
        ⟨GateOp.or, [1, 6]⟩,
        ⟨GateOp.or, [8, 11]⟩,
        ⟨GateOp.or, [0, 4]⟩,
        ⟨GateOp.or, [5, 14]⟩,
        ⟨GateOp.or, [10, 6]⟩,
        ⟨GateOp.or, [11, 16]⟩,
        ⟨GateOp.and, [15, 17]⟩,
        ⟨GateOp.and, [12, 13]⟩,
        ⟨GateOp.or, [18, 19]⟩ ],
    output := 20 }

end PEqualNP.Outside.L_meta_53505

theorem PEqualNP.Outside.L_meta_53505 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (816684 : ℕ).testBit (6 * u.val + v.val)) 11) := by
  unfold PEqualNP.Represents.RepSizeAtMost
  refine ⟨PEqualNP.Outside.L_meta_53505.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_53505.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · unfold PEqualNP.Represents.Represents
    decide +kernel
