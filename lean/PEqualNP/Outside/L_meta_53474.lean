import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53474
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [9, 3]⟩,
        ⟨GateOp.or, [4, 0]⟩,
        ⟨GateOp.or, [1, 11]⟩,
        ⟨GateOp.or, [7, 8]⟩,
        ⟨GateOp.or, [5, 11]⟩,
        ⟨GateOp.or, [12, 6]⟩,
        ⟨GateOp.or, [5, 13]⟩,
        ⟨GateOp.or, [2, 16]⟩,
        ⟨GateOp.and, [15, 17]⟩,
        ⟨GateOp.and, [10, 14]⟩,
        ⟨GateOp.or, [19, 18]⟩ ],
    output := 20 }

end PEqualNP.Outside.L_meta_53474

theorem PEqualNP.Outside.L_meta_53474 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (808634 : ℕ).testBit (6 * u.val + v.val)) 11) := by
  unfold PEqualNP.Represents.RepSizeAtMost
  refine ⟨PEqualNP.Outside.L_meta_53474.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_53474.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · unfold PEqualNP.Represents.Represents
    decide +kernel
