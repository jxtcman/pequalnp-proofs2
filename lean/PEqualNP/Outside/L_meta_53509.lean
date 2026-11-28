import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53509
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [3, 8]⟩,
        ⟨GateOp.or, [2, 7]⟩,
        ⟨GateOp.or, [10, 11]⟩,
        ⟨GateOp.or, [5, 9]⟩,
        ⟨GateOp.or, [5, 1]⟩,
        ⟨GateOp.and, [14, 12]⟩,
        ⟨GateOp.or, [11, 13]⟩,
        ⟨GateOp.or, [6, 0]⟩,
        ⟨GateOp.and, [17, 16]⟩,
        ⟨GateOp.or, [18, 15]⟩,
        ⟨GateOp.or, [4, 19]⟩ ],
    output := 20 }

end PEqualNP.Outside.L_meta_53509

theorem PEqualNP.Outside.L_meta_53509 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (816747 : ℕ).testBit (6 * u.val + v.val)) 11) := by
  unfold PEqualNP.Represents.RepSizeAtMost
  refine ⟨PEqualNP.Outside.L_meta_53509.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_53509.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · unfold PEqualNP.Represents.Represents
    decide +kernel
