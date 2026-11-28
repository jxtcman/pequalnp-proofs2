import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54423 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (294522 : ℕ).testBit (6 * u.val + v.val)) 12 := by
  refine ⟨⟨[⟨.or, [4, 0]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [5, 1]⟩, ⟨.or, [2, 7]⟩, ⟨.or, [12, 3]⟩, ⟨.or, [10, 12]⟩, ⟨.and, [10, 14]⟩, ⟨.or, [16, 11]⟩, ⟨.and, [15, 2]⟩, ⟨.or, [17, 13]⟩, ⟨.or, [15, 6]⟩, ⟨.and, [19, 20]⟩], 21⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
