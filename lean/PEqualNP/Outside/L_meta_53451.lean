import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53451
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [7, 8]⟩,
        ⟨GateOp.or, [10, 9]⟩,
        ⟨GateOp.or, [1, 2]⟩,
        ⟨GateOp.or, [1, 3]⟩,
        ⟨GateOp.or, [5, 4]⟩,
        ⟨GateOp.or, [6, 4]⟩,
        ⟨GateOp.and, [0, 11]⟩,
        ⟨GateOp.and, [13, 14]⟩,
        ⟨GateOp.and, [12, 15]⟩,
        ⟨GateOp.or, [16, 17]⟩,
        ⟨GateOp.or, [19, 18]⟩ ],
    output := 20 }

end PEqualNP.Outside.L_meta_53451

theorem PEqualNP.Outside.L_meta_53451 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (807416 : ℕ).testBit (6 * u.val + v.val)) 11) := by
  unfold PEqualNP.Represents.RepSizeAtMost
  refine ⟨PEqualNP.Outside.L_meta_53451.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_53451.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · unfold PEqualNP.Represents.Represents
    decide +kernel
