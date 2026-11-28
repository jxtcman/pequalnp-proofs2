import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53444
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [2, 3]⟩,
        ⟨GateOp.or, [6, 7]⟩,
        ⟨GateOp.or, [8, 9]⟩,
        ⟨GateOp.or, [5, 4]⟩,
        ⟨GateOp.or, [11, 4]⟩,
        ⟨GateOp.or, [11, 12]⟩,
        ⟨GateOp.and, [0, 15]⟩,
        ⟨GateOp.and, [1, 14]⟩,
        ⟨GateOp.and, [10, 13]⟩,
        ⟨GateOp.or, [16, 17]⟩,
        ⟨GateOp.or, [19, 18]⟩ ],
    output := 20 }

end PEqualNP.Outside.L_meta_53444

theorem PEqualNP.Outside.L_meta_53444 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (799612 : ℕ).testBit (6 * u.val + v.val)) 11) := by
  unfold PEqualNP.Represents.RepSizeAtMost
  refine ⟨PEqualNP.Outside.L_meta_53444.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_53444.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · unfold PEqualNP.Represents.Represents
    decide +kernel
