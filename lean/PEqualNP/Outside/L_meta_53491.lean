import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53491
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [1, 4]⟩,
        ⟨GateOp.or, [2, 7]⟩,
        ⟨GateOp.or, [5, 10]⟩,
        ⟨GateOp.or, [3, 11]⟩,
        ⟨GateOp.or, [9, 8]⟩,
        ⟨GateOp.or, [14, 1]⟩,
        ⟨GateOp.or, [15, 11]⟩,
        ⟨GateOp.and, [13, 12]⟩,
        ⟨GateOp.or, [6, 0]⟩,
        ⟨GateOp.and, [16, 18]⟩,
        ⟨GateOp.or, [19, 17]⟩ ],
    output := 20 }

end PEqualNP.Outside.L_meta_53491

theorem PEqualNP.Outside.L_meta_53491 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (815928 : ℕ).testBit (6 * u.val + v.val)) 11) := by
  unfold PEqualNP.Represents.RepSizeAtMost
  refine ⟨PEqualNP.Outside.L_meta_53491.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_53491.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · unfold PEqualNP.Represents.Represents
    decide +kernel
