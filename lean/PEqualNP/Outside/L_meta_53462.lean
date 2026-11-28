import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53462
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [5, 2]⟩,
        ⟨GateOp.or, [7, 10]⟩,
        ⟨GateOp.or, [1, 4]⟩,
        ⟨GateOp.or, [3, 6]⟩,
        ⟨GateOp.or, [10, 12]⟩,
        ⟨GateOp.and, [14, 13]⟩,
        ⟨GateOp.or, [8, 9]⟩,
        ⟨GateOp.and, [12, 11]⟩,
        ⟨GateOp.or, [15, 17]⟩,
        ⟨GateOp.and, [0, 16]⟩,
        ⟨GateOp.or, [18, 19]⟩ ],
    output := 20 }

end PEqualNP.Outside.L_meta_53462

theorem PEqualNP.Outside.L_meta_53462 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (807856 : ℕ).testBit (6 * u.val + v.val)) 11) := by
  unfold PEqualNP.Represents.RepSizeAtMost
  refine ⟨PEqualNP.Outside.L_meta_53462.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_53462.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · unfold PEqualNP.Represents.Represents
    decide +kernel
