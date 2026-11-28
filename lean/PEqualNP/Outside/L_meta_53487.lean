import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53487
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [4, 1]⟩,
        ⟨GateOp.or, [10, 9]⟩,
        ⟨GateOp.or, [0, 6]⟩,
        ⟨GateOp.or, [10, 5]⟩,
        ⟨GateOp.or, [8, 2]⟩,
        ⟨GateOp.or, [11, 14]⟩,
        ⟨GateOp.or, [7, 3]⟩,
        ⟨GateOp.and, [12, 15]⟩,
        ⟨GateOp.or, [2, 16]⟩,
        ⟨GateOp.and, [18, 13]⟩,
        ⟨GateOp.or, [19, 17]⟩ ],
    output := 20 }

end PEqualNP.Outside.L_meta_53487

theorem PEqualNP.Outside.L_meta_53487 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (815921 : ℕ).testBit (6 * u.val + v.val)) 11) := by
  unfold PEqualNP.Represents.RepSizeAtMost
  refine ⟨PEqualNP.Outside.L_meta_53487.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_53487.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · unfold PEqualNP.Represents.Represents
    decide +kernel
