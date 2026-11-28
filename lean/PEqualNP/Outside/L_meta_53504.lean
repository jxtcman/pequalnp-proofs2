import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53504
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [5, 1]⟩,
        ⟨GateOp.or, [4, 10]⟩,
        ⟨GateOp.or, [11, 9]⟩,
        ⟨GateOp.or, [6, 11]⟩,
        ⟨GateOp.or, [0, 3]⟩,
        ⟨GateOp.or, [8, 14]⟩,
        ⟨GateOp.or, [7, 2]⟩,
        ⟨GateOp.or, [0, 13]⟩,
        ⟨GateOp.and, [12, 15]⟩,
        ⟨GateOp.or, [18, 16]⟩,
        ⟨GateOp.and, [19, 17]⟩ ],
    output := 20 }

end PEqualNP.Outside.L_meta_53504

theorem PEqualNP.Outside.L_meta_53504 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (816683 : ℕ).testBit (6 * u.val + v.val)) 11) := by
  unfold PEqualNP.Represents.RepSizeAtMost
  refine ⟨PEqualNP.Outside.L_meta_53504.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_53504.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · unfold PEqualNP.Represents.Represents
    decide +kernel
