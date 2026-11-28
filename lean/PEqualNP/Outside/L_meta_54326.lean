import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54326
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [4, 7]⟩,
        ⟨GateOp.or, [1, 3]⟩,
        ⟨GateOp.or, [4, 2]⟩,
        ⟨GateOp.or, [9, 8]⟩,
        ⟨GateOp.or, [13, 12]⟩,
        ⟨GateOp.or, [6, 5]⟩,
        ⟨GateOp.or, [0, 15]⟩,
        ⟨GateOp.and, [11, 10]⟩,
        ⟨GateOp.or, [14, 1]⟩,
        ⟨GateOp.or, [16, 17]⟩,
        ⟨GateOp.and, [18, 19]⟩ ],
    output := 20 }

end PEqualNP.Outside.L_meta_54326

theorem PEqualNP.Outside.L_meta_54326 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (287729 : ℕ).testBit (6 * u.val + v.val)) 11) := by
  unfold PEqualNP.Represents.RepSizeAtMost
  refine ⟨PEqualNP.Outside.L_meta_54326.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_54326.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · unfold PEqualNP.Represents.Represents
    decide +kernel
