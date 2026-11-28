import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53508
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [6, 1]⟩,
        ⟨GateOp.or, [0, 5]⟩,
        ⟨GateOp.or, [8, 2]⟩,
        ⟨GateOp.or, [6, 3]⟩,
        ⟨GateOp.or, [4, 11]⟩,
        ⟨GateOp.or, [10, 14]⟩,
        ⟨GateOp.or, [9, 13]⟩,
        ⟨GateOp.and, [16, 14]⟩,
        ⟨GateOp.or, [7, 12]⟩,
        ⟨GateOp.or, [18, 17]⟩,
        ⟨GateOp.and, [19, 15]⟩ ],
    output := 20 }

end PEqualNP.Outside.L_meta_53508

theorem PEqualNP.Outside.L_meta_53508 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (816700 : ℕ).testBit (6 * u.val + v.val)) 11) := by
  unfold PEqualNP.Represents.RepSizeAtMost
  refine ⟨PEqualNP.Outside.L_meta_53508.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_53508.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · unfold PEqualNP.Represents.Represents
    decide +kernel
