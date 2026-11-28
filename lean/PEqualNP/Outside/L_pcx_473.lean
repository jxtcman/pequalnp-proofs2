import Mathlib
import PEqualNP.Defs

-- Fix the deleted choices Z. Flip the shore S: X = { c | c ∈ C ↔ c ∉ S }. The flipped optimal pinned covers
-- with C ∩ D = Z form a family closed under union and intersection (the two mixtures of two optimal covers
-- are covers of the same total weight). Induct on the family: take an atom X1 above the bottom B; every member
-- either contains X1 or meets it in B, so its permutation is fixed by that of X ∪ X1 and one bit, and the bit
-- only matters when the readings of B and X1 differ, which uses up h rows that never change again.

namespace PEqualNP.Outside.L_pcx_473

open Finset

theorem core {n h N : ℕ} (hh : 0 < h) (S : Finset (Fin N)) (p : Fin n → Fin n → Fin N)
    (f : Finset (Fin N) → Fin n → Fin n) :
    ∀ (k : ℕ) (L : Finset (Finset (Fin N))), L.card ≤ k →
    (∀ X ∈ L, ∀ Y ∈ L, X ∪ Y ∈ L) → (∀ X ∈ L, ∀ Y ∈ L, X ∩ Y ∈ L) →
    (∀ X ∈ L, ∀ i j, (p i j ∈ X ↔ p i j ∉ S) ↔ f X i = j) →
    (∀ X ∈ L, ∀ Y ∈ L, f X ≠ f Y → h ≤ (Finset.univ.filter (fun i => f X i ≠ f Y i)).card) →
    ∀ B ∈ L, ∀ T ∈ L, (∀ X ∈ L, B ⊆ X ∧ X ⊆ T) →
    (L.image f).card ≤ 2 ^ ((Finset.univ.filter (fun i => f B i ≠ f T i)).card / h) := by
  classical
  intro k
  induction k with
  | zero =>
    intro L hk _ _ _ _ B hB
    have := Finset.card_eq_zero.1 (Nat.le_zero.1 hk)
    rw [this] at hB
    exact absurd hB (Finset.notMem_empty _)
  | succ k ih =>
    intro L hk hU hI hR hsep B hB T hT hBT
    by_cases hL0 : (L.erase B) = ∅
    · have himg : L.image f = {f B} := by
        ext g
        simp only [Finset.mem_image, Finset.mem_singleton]
        constructor
        · rintro ⟨X, hX, rfl⟩
          by_cases hXB : X = B
          · rw [hXB]
          · have hm := Finset.mem_erase.2 ⟨hXB, hX⟩
            rw [hL0] at hm
            exact absurd hm (Finset.notMem_empty _)
        · rintro rfl
          exact ⟨B, hB, rfl⟩
      rw [himg, Finset.card_singleton]
      exact Nat.one_le_two_pow
    · obtain ⟨X1, hX1, hmin⟩ := Finset.exists_min_image (L.erase B) Finset.card
        (Finset.nonempty_iff_ne_empty.2 hL0)
      have hX1L : X1 ∈ L := Finset.mem_of_mem_erase hX1
      have hX1B : X1 ≠ B := Finset.ne_of_mem_erase hX1
      have hBX1 : B ⊆ X1 := (hBT X1 hX1L).1
      have atom : ∀ X ∈ L, X1 ⊆ X ∨ X ∩ X1 = B := by
        intro X hX
        by_cases hc : X ∩ X1 = B
        · right; exact hc
        · left
          have hm : X ∩ X1 ∈ L.erase B := Finset.mem_erase.2 ⟨hc, hI X hX X1 hX1L⟩
          have hle := hmin _ hm
          have he : X ∩ X1 = X1 := Finset.eq_of_subset_of_card_le Finset.inter_subset_right hle
          rw [← he]
          exact Finset.inter_subset_left
      have hL'sub : L.filter (fun X => X1 ⊆ X) ⊆ L := Finset.filter_subset _ _
      have hBnot : B ∉ L.filter (fun X => X1 ⊆ X) := by
        intro hb
        have h1 : X1 ⊆ B := (Finset.mem_filter.1 hb).2
        exact hX1B (Finset.Subset.antisymm h1 hBX1)
      have hcard : (L.filter (fun X => X1 ⊆ X)).card ≤ k := by
        have hlt : (L.filter (fun X => X1 ⊆ X)).card < L.card :=
          Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hL'sub, fun e => hBnot (by rw [e]; exact hB)⟩)
        omega
      have hX1L' : X1 ∈ L.filter (fun X => X1 ⊆ X) :=
        Finset.mem_filter.2 ⟨hX1L, Finset.Subset.refl _⟩
      have hTL' : T ∈ L.filter (fun X => X1 ⊆ X) := Finset.mem_filter.2 ⟨hT, (hBT X1 hX1L).2⟩
      have IH := ih (L.filter (fun X => X1 ⊆ X)) hcard
        (fun X hX Y hY => Finset.mem_filter.2 ⟨hU X (hL'sub hX) Y (hL'sub hY),
          (Finset.mem_filter.1 hX).2.trans Finset.subset_union_left⟩)
        (fun X hX Y hY => Finset.mem_filter.2 ⟨hI X (hL'sub hX) Y (hL'sub hY),
          Finset.subset_inter (Finset.mem_filter.1 hX).2 (Finset.mem_filter.1 hY).2⟩)
        (fun X hX => hR X (hL'sub hX))
        (fun X hX Y hY => hsep X (hL'sub hX) Y (hL'sub hY))
        X1 hX1L' T hTL' (fun X hX => ⟨(Finset.mem_filter.1 hX).2, (hBT X (hL'sub hX)).2⟩)
      have P1 : ∀ i, f B i ≠ f X1 i → f T i = f X1 i := by
        intro i hne
        have hY := (hR X1 hX1L i (f X1 i)).2 rfl
        have hX : ¬ (p i (f X1 i) ∈ B ↔ p i (f X1 i) ∉ S) :=
          fun hc => hne ((hR B hB i (f X1 i)).1 hc)
        apply (hR T hT i (f X1 i)).1
        have h1 := @hBX1 (p i (f X1 i))
        have h2 := @(hBT X1 hX1L).2 (p i (f X1 i))
        tauto
      have G : ∀ X ∈ L, X ∩ X1 = B → ∀ i,
          f X i = if f B i ≠ f X1 i then f B i else f (X ∪ X1) i := by
        intro X hX hXB i
        have hsubB : ∀ c, c ∈ B ↔ (c ∈ X ∧ c ∈ X1) := by
          intro c; rw [← hXB, Finset.mem_inter]
        by_cases hne : f B i ≠ f X1 i
        · rw [ite_eq_left hne]
          apply (hR X hX i (f B i)).1
          have h0 := (hR B hB i (f B i)).2 rfl
          have h1 : ¬ (p i (f B i) ∈ X1 ↔ p i (f B i) ∉ S) :=
            fun hc => hne ((hR X1 hX1L i (f B i)).1 hc).symm
          have h2 := hsubB (p i (f B i))
          tauto
        · rw [ite_eq_right hne]
          have he : f B i = f X1 i := not_not.1 hne
          apply (hR X hX i _).1
          have h0 := (hR (X ∪ X1) (hU X hX X1 hX1L) i (f (X ∪ X1) i)).2 rfl
          rw [Finset.mem_union] at h0
          have h2 := hsubB (p i (f (X ∪ X1) i))
          have h3 := (hR X1 hX1L i (f (X ∪ X1) i))
          have h4 := (hR B hB i (f (X ∪ X1) i))
          rw [he] at h4
          tauto
      by_cases hfe : f B = f X1
      · have hsub : L.image f ⊆ (L.filter (fun X => X1 ⊆ X)).image f := by
          intro g hg
          obtain ⟨X, hX, rfl⟩ := Finset.mem_image.1 hg
          rcases atom X hX with h1 | h1
          · exact Finset.mem_image_of_mem f (Finset.mem_filter.2 ⟨hX, h1⟩)
          · have hfx : f X = f (X ∪ X1) := by
              funext i
              rw [G X hX h1 i, ite_eq_right (fun hq => hq (congrFun hfe i))]
            rw [hfx]
            exact Finset.mem_image_of_mem f
              (Finset.mem_filter.2 ⟨hU X hX X1 hX1L, Finset.subset_union_right⟩)
        calc (L.image f).card ≤ ((L.filter (fun X => X1 ⊆ X)).image f).card :=
              Finset.card_le_card hsub
          _ ≤ _ := by rw [hfe]; exact IH
      · have hsub : L.image f ⊆ (L.filter (fun X => X1 ⊆ X)).image f ∪
            ((L.filter (fun X => X1 ⊆ X)).image f).image
              (fun τ i => if f B i ≠ f X1 i then f B i else τ i) := by
          intro q hq
          obtain ⟨X, hX, rfl⟩ := Finset.mem_image.1 hq
          rcases atom X hX with h1 | h1
          · exact Finset.mem_union_left _
              (Finset.mem_image_of_mem f (Finset.mem_filter.2 ⟨hX, h1⟩))
          · apply Finset.mem_union_right
            refine Finset.mem_image.2 ⟨f (X ∪ X1), Finset.mem_image_of_mem f
              (Finset.mem_filter.2 ⟨hU X hX X1 hX1L, Finset.subset_union_right⟩), ?_⟩
            funext i
            exact (G X hX h1 i).symm
        have hd := hsep B hB X1 hX1L hfe
        have hdisj : Disjoint (Finset.univ.filter (fun i => f B i ≠ f X1 i))
            (Finset.univ.filter (fun i => f X1 i ≠ f T i)) := by
          rw [Finset.disjoint_left]
          intro i h1 h2
          exact (Finset.mem_filter.1 h2).2 (P1 i (Finset.mem_filter.1 h1).2).symm
        have hun : (Finset.univ.filter (fun i => f B i ≠ f X1 i)) ∪
            (Finset.univ.filter (fun i => f X1 i ≠ f T i)) ⊆
            (Finset.univ.filter (fun i => f B i ≠ f T i)) := by
          intro i hi
          rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter] at hi
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_⟩
          rcases hi with ⟨_, hi⟩ | ⟨_, hi⟩
          · rw [P1 i hi]; exact hi
          · have hq : f B i = f X1 i := by
              by_contra hc
              exact hi (P1 i hc).symm
            rw [hq]; exact hi
        have hdis := Finset.card_le_card hun
        rw [Finset.card_union_of_disjoint hdisj] at hdis
        have h1 : (L.image f).card ≤ 2 * ((L.filter (fun X => X1 ⊆ X)).image f).card := by
          have ha := Finset.card_le_card hsub
          have hb := Finset.card_union_le ((L.filter (fun X => X1 ⊆ X)).image f)
            (((L.filter (fun X => X1 ⊆ X)).image f).image
              (fun τ i => if f B i ≠ f X1 i then f B i else τ i))
          have hc := Finset.card_image_le (s := (L.filter (fun X => X1 ⊆ X)).image f)
            (f := fun τ i => if f B i ≠ f X1 i then f B i else τ i)
          omega
        have h2 : (Finset.univ.filter (fun i => f X1 i ≠ f T i)).card / h + 1 ≤
            (Finset.univ.filter (fun i => f B i ≠ f T i)).card / h := by
          rw [← Nat.add_div_right _ hh]
          exact Nat.div_le_div_right (by omega)
        calc (L.image f).card
            ≤ 2 * 2 ^ ((Finset.univ.filter (fun i => f X1 i ≠ f T i)).card / h) := by omega
          _ = 2 ^ ((Finset.univ.filter (fun i => f X1 i ≠ f T i)).card / h + 1) := by
              rw [pow_succ, mul_comm]
          _ ≤ _ := Nat.pow_le_pow_right (by norm_num) h2

theorem mix_opt {N : ℕ} (G : Finset (Fin N × Fin N)) (w : Fin N → ℕ) (D S C1 C2 : Finset (Fin N))
    (hbip : ∀ e ∈ G, e.1 ∉ D → e.2 ∉ D → (e.1 ∈ S ↔ e.2 ∉ S))
    (hc1 : ∀ e ∈ G, e.1 ∈ C1 ∨ e.2 ∈ C1) (hc2 : ∀ e ∈ G, e.1 ∈ C2 ∨ e.2 ∈ C2)
    (ho1 : ∀ B : Finset (Fin N), (∀ e ∈ G, e.1 ∈ B ∨ e.2 ∈ B) → C1.sum w ≤ B.sum w)
    (ho2 : ∀ B : Finset (Fin N), (∀ e ∈ G, e.1 ∈ B ∨ e.2 ∈ B) → C2.sum w ≤ B.sum w)
    (hD : C1 ∩ D = C2 ∩ D) :
    (∀ e ∈ G, e.1 ∈ (C1 ∩ C2) ∪ ((C1 ∪ C2) \ S) ∨ e.2 ∈ (C1 ∩ C2) ∪ ((C1 ∪ C2) \ S)) ∧
    (∀ e ∈ G, e.1 ∈ (C1 ∩ C2) ∪ ((C1 ∪ C2) ∩ S) ∨ e.2 ∈ (C1 ∩ C2) ∪ ((C1 ∪ C2) ∩ S)) ∧
    ((C1 ∩ C2) ∪ ((C1 ∪ C2) \ S)).sum w = C1.sum w ∧
    ((C1 ∩ C2) ∪ ((C1 ∪ C2) ∩ S)).sum w = C1.sum w := by
  classical
  have hD1 : ∀ c, c ∈ D → (c ∈ C1 ↔ c ∈ C2) := by
    intro c hc
    have := Finset.ext_iff.1 hD c
    rw [Finset.mem_inter, Finset.mem_inter] at this
    tauto
  have cA : ∀ e ∈ G, e.1 ∈ (C1 ∩ C2) ∪ ((C1 ∪ C2) \ S) ∨ e.2 ∈ (C1 ∩ C2) ∪ ((C1 ∪ C2) \ S) := by
    intro e he
    have h1 := hbip e he
    have h2 := hc1 e he
    have h3 := hc2 e he
    have h4 := hD1 e.1
    have h5 := hD1 e.2
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    grind
  have cB : ∀ e ∈ G, e.1 ∈ (C1 ∩ C2) ∪ ((C1 ∪ C2) ∩ S) ∨ e.2 ∈ (C1 ∩ C2) ∪ ((C1 ∪ C2) ∩ S) := by
    intro e he
    have h1 := hbip e he
    have h2 := hc1 e he
    have h3 := hc2 e he
    have h4 := hD1 e.1
    have h5 := hD1 e.2
    simp only [Finset.mem_union, Finset.mem_inter]
    grind
  have hU : ((C1 ∩ C2) ∪ ((C1 ∪ C2) \ S)) ∪ ((C1 ∩ C2) ∪ ((C1 ∪ C2) ∩ S)) = C1 ∪ C2 := by
    ext c
    by_cases a : c ∈ C1 <;> by_cases b : c ∈ C2 <;> by_cases s : c ∈ S <;>
      simp [a, b, s]
  have hI : ((C1 ∩ C2) ∪ ((C1 ∪ C2) \ S)) ∩ ((C1 ∩ C2) ∪ ((C1 ∪ C2) ∩ S)) = C1 ∩ C2 := by
    ext c
    by_cases a : c ∈ C1 <;> by_cases b : c ∈ C2 <;> by_cases s : c ∈ S <;>
      simp [a, b, s]
  have hs : ((C1 ∩ C2) ∪ ((C1 ∪ C2) \ S)).sum w + ((C1 ∩ C2) ∪ ((C1 ∪ C2) ∩ S)).sum w =
      C1.sum w + C2.sum w := by
    rw [← Finset.sum_union_inter, hU, hI, Finset.sum_union_inter]
  have a1 := ho1 _ cA
  have a2 := ho1 _ cB
  have a3 := ho1 _ hc2
  have a4 := ho2 _ hc1
  refine ⟨cA, cB, ?_, ?_⟩ <;> omega

def Sel {N : ℕ} (G : Finset (Fin N × Fin N)) (w : Fin N → ℕ) (I O : Finset (Fin N))
    (C : Finset (Fin N)) : Prop :=
  (∀ e ∈ G, e.1 ∈ C ∨ e.2 ∈ C) ∧
    (∀ B : Finset (Fin N), (∀ e ∈ G, e.1 ∈ B ∨ e.2 ∈ B) → C.sum w ≤ B.sum w) ∧
    I ⊆ C ∧ Disjoint O C

theorem zbound (n h N : ℕ) (A : Finset (Equiv.Perm (Fin n)))
    (G : Finset (Fin N × Fin N)) (w : Fin N → ℕ)
    (p : Fin n → Fin n → Fin N) (D S I O : Finset (Fin N)) (Z : Finset (Fin N))
    (hh : 0 < h)
    (hsep : ∀ σ ∈ A, ∀ τ ∈ A, σ ≠ τ →
      h ≤ (Finset.univ.filter (fun i : Fin n => σ i ≠ τ i)).card)
    (hbip : ∀ e ∈ G, e.1 ∉ D → e.2 ∉ D → (e.1 ∈ S ↔ e.2 ∉ S))
    (hsel : ∀ C : Finset (Fin N),
      ((∀ e ∈ G, e.1 ∈ C ∨ e.2 ∈ C) ∧
        (∀ B : Finset (Fin N), (∀ e ∈ G, e.1 ∈ B ∨ e.2 ∈ B) → C.sum w ≤ B.sum w) ∧
        I ⊆ C ∧ Disjoint O C) →
      ∃ σ ∈ A, ∀ i j, p i j ∈ C ↔ σ i = j) :
    ∃ R : Finset (Fin n → Fin n), R.card ≤ 2 ^ (n / h) ∧
      ∀ σ ∈ A, (∃ C : Finset (Fin N),
        ((∀ e ∈ G, e.1 ∈ C ∨ e.2 ∈ C) ∧
          (∀ B : Finset (Fin N), (∀ e ∈ G, e.1 ∈ B ∨ e.2 ∈ B) → C.sum w ≤ B.sum w) ∧
          I ⊆ C ∧ Disjoint O C) ∧ C ∩ D = Z ∧ (∀ i j, p i j ∈ C ↔ σ i = j)) →
        (fun i => σ i) ∈ R := by
  classical
  obtain ⟨T, hT⟩ : ∃ T : Finset (Fin N) → Finset (Fin N), ∀ C c, c ∈ T C ↔ (c ∈ C ↔ c ∉ S) :=
    ⟨fun C => Finset.univ.filter (fun c => (c ∈ C ↔ c ∉ S)), fun C c => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]⟩
  have hTmem : ∀ C c, c ∈ T (T C) ↔ c ∈ C := by
    intro C c
    rw [hT, hT]
    tauto
  have hsel' : ∀ C, Sel G w I O C → ∃ σ ∈ A, ∀ i j, p i j ∈ C ↔ σ i = j := hsel
  obtain ⟨F, hFmem⟩ : ∃ F : Finset (Finset (Fin N)),
      ∀ C, C ∈ F ↔ (Sel G w I O C ∧ C ∩ D = Z) :=
    ⟨Finset.univ.filter (fun C => Sel G w I O C ∧ C ∩ D = Z), fun C => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]⟩
  obtain ⟨f, fspec⟩ : ∃ f : Finset (Fin N) → Fin n → Fin n, ∀ C, Sel G w I O C →
      ∃ σ ∈ A, f (T C) = (fun i => σ i) ∧ ∀ i j, p i j ∈ C ↔ σ i = j := by
    refine ⟨fun X => if hx : ∃ σ ∈ A, ∀ i j, p i j ∈ T X ↔ σ i = j
      then (fun i => (Classical.choose hx) i) else id, ?_⟩
    intro C hC
    have hx : ∃ σ ∈ A, ∀ i j, p i j ∈ T (T C) ↔ σ i = j := by
      obtain ⟨σ, hσ, hr⟩ := hsel' C hC
      exact ⟨σ, hσ, fun i j => (hTmem C _).trans (hr i j)⟩
    refine ⟨Classical.choose hx, (Classical.choose_spec hx).1, ?_, ?_⟩
    · show (if hx : ∃ σ ∈ A, ∀ i j, p i j ∈ T (T C) ↔ σ i = j
        then (fun i => (Classical.choose hx) i) else id) = _
      rw [dite_eq_left hx]
    · intro i j
      exact (hTmem C _).symm.trans ((Classical.choose_spec hx).2 i j)
  by_cases hF : F = ∅
  · refine ⟨∅, by simp, ?_⟩
    rintro σ hσ ⟨C, hC, hZ, hr⟩
    have hm : C ∈ F := (hFmem C).2 ⟨hC, hZ⟩
    rw [hF] at hm
    exact absurd hm (Finset.notMem_empty _)
  · have hLne : (F.image T).Nonempty :=
      (Finset.nonempty_iff_ne_empty.2 hF).image T
    have hclos : ∀ X ∈ F.image T, ∀ Y ∈ F.image T, X ∪ Y ∈ F.image T ∧ X ∩ Y ∈ F.image T := by
      intro X hX Y hY
      obtain ⟨C1, hC1, rfl⟩ := Finset.mem_image.1 hX
      obtain ⟨C2, hC2, rfl⟩ := Finset.mem_image.1 hY
      obtain ⟨⟨hc1, ho1, hi1, hd1⟩, hz1⟩ := (hFmem C1).1 hC1
      obtain ⟨⟨hc2, ho2, hi2, hd2⟩, hz2⟩ := (hFmem C2).1 hC2
      obtain ⟨hcM, hcM', hsM, hsM'⟩ :=
        mix_opt G w D S C1 C2 hbip hc1 hc2 ho1 ho2 (hz1.trans hz2.symm)
      have mk : ∀ M : Finset (Fin N), (∀ e ∈ G, e.1 ∈ M ∨ e.2 ∈ M) → M.sum w = C1.sum w →
          (∀ c, c ∈ M → c ∈ C1 ∨ c ∈ C2) → (∀ c, c ∈ C1 → c ∈ C2 → c ∈ M) → M ∈ F := by
        intro M hcov hsum hup hlo
        refine (hFmem M).2 ⟨⟨hcov, ?_, ?_, ?_⟩, ?_⟩
        · intro B hB
          rw [hsum]
          exact ho1 B hB
        · intro c hc
          exact hlo c (hi1 hc) (hi2 hc)
        · rw [Finset.disjoint_left]
          intro c hcO hcM
          rcases hup c hcM with h1 | h1
          · exact (Finset.disjoint_left.1 hd1 hcO) h1
          · exact (Finset.disjoint_left.1 hd2 hcO) h1
        · ext c
          have e1 := Finset.ext_iff.1 hz1 c
          have e2 := Finset.ext_iff.1 hz2 c
          rw [Finset.mem_inter] at e1 e2 ⊢
          constructor
          · rintro ⟨hm, hd⟩
            rcases hup c hm with q | q
            · exact e1.1 ⟨q, hd⟩
            · exact e2.1 ⟨q, hd⟩
          · intro hz
            exact ⟨hlo c (e1.2 hz).1 (e2.2 hz).1, (e1.2 hz).2⟩
      constructor
      · refine Finset.mem_image.2 ⟨(C1 ∩ C2) ∪ ((C1 ∪ C2) \ S), mk _ hcM hsM ?_ ?_, ?_⟩
        · intro c
          by_cases a : c ∈ C1 <;> by_cases b : c ∈ C2 <;> by_cases s : c ∈ S <;>
            simp [a, b, s]
        · intro c
          by_cases a : c ∈ C1 <;> by_cases b : c ∈ C2 <;> by_cases s : c ∈ S <;>
            simp [a, b, s]
        · ext c
          rw [Finset.mem_union, hT, hT, hT]
          by_cases a : c ∈ C1 <;> by_cases b : c ∈ C2 <;> by_cases s : c ∈ S <;>
            simp [a, b, s]
      · refine Finset.mem_image.2 ⟨(C1 ∩ C2) ∪ ((C1 ∪ C2) ∩ S), mk _ hcM' hsM' ?_ ?_, ?_⟩
        · intro c
          by_cases a : c ∈ C1 <;> by_cases b : c ∈ C2 <;> by_cases s : c ∈ S <;>
            simp [a, b, s]
        · intro c
          by_cases a : c ∈ C1 <;> by_cases b : c ∈ C2 <;> by_cases s : c ∈ S <;>
            simp [a, b, s]
        · ext c
          rw [Finset.mem_inter, hT, hT, hT]
          by_cases a : c ∈ C1 <;> by_cases b : c ∈ C2 <;> by_cases s : c ∈ S <;>
            simp [a, b, s]
    have hread : ∀ X ∈ F.image T, ∀ i j, (p i j ∈ X ↔ p i j ∉ S) ↔ f X i = j := by
      intro X hX i j
      obtain ⟨C, hC, rfl⟩ := Finset.mem_image.1 hX
      obtain ⟨σ, -, hf, hr⟩ := fspec C ((hFmem C).1 hC).1
      rw [hf, hT]
      have := hr i j
      tauto
    have hsepL : ∀ X ∈ F.image T, ∀ Y ∈ F.image T, f X ≠ f Y →
        h ≤ (Finset.univ.filter (fun i => f X i ≠ f Y i)).card := by
      intro X hX Y hY hne
      obtain ⟨C1, hC1, rfl⟩ := Finset.mem_image.1 hX
      obtain ⟨C2, hC2, rfl⟩ := Finset.mem_image.1 hY
      obtain ⟨σ1, hσ1, hf1, -⟩ := fspec C1 ((hFmem C1).1 hC1).1
      obtain ⟨σ2, hσ2, hf2, -⟩ := fspec C2 ((hFmem C2).1 hC2).1
      rw [hf1, hf2] at hne ⊢
      exact hsep σ1 hσ1 σ2 hσ2 (fun e => hne (by rw [e]))
    obtain ⟨B, hB, hBmin⟩ := Finset.exists_min_image (F.image T) Finset.card hLne
    obtain ⟨Tp, hTp, hTmax⟩ := Finset.exists_max_image (F.image T) Finset.card hLne
    have hBT : ∀ X ∈ F.image T, B ⊆ X ∧ X ⊆ Tp := by
      intro X hX
      constructor
      · have he : B ∩ X = B := Finset.eq_of_subset_of_card_le Finset.inter_subset_left
          (hBmin _ (hclos B hB X hX).2)
        rw [← he]
        exact Finset.inter_subset_right
      · have he : Tp = X ∪ Tp := Finset.eq_of_subset_of_card_le Finset.subset_union_right
          (hTmax _ (hclos X hX Tp hTp).1)
        rw [he]
        exact Finset.subset_union_left
    have hcore := core hh S p f (F.image T).card (F.image T) le_rfl
      (fun X hX Y hY => (hclos X hX Y hY).1) (fun X hX Y hY => (hclos X hX Y hY).2)
      hread hsepL B hB Tp hTp hBT
    refine ⟨(F.image T).image f, ?_, ?_⟩
    · have hd : (Finset.univ.filter (fun i => f B i ≠ f Tp i)).card ≤ n := by
        have := Finset.card_filter_le (Finset.univ : Finset (Fin n)) (fun i => f B i ≠ f Tp i)
        rw [Finset.card_univ, Fintype.card_fin] at this
        exact this
      exact hcore.trans (Nat.pow_le_pow_right (by norm_num) (Nat.div_le_div_right hd))
    · rintro σ hσ ⟨C, hC, hZ, hr⟩
      obtain ⟨σ', -, hf, hr'⟩ := fspec C hC
      refine Finset.mem_image.2 ⟨T C, Finset.mem_image_of_mem T
        ((hFmem C).2 ⟨hC, hZ⟩), ?_⟩
      rw [hf]
      funext i
      exact (hr' i (σ i)).1 ((hr i (σ i)).2 rfl)

end PEqualNP.Outside.L_pcx_473

theorem PEqualNP.Outside.L_pcx_473 : letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
∀ (n h N : Nat) (A : Finset (Equiv.Perm (Fin n)))
  (G : Finset (Fin N × Fin N)) (w : Fin N → Nat)
  (p : Fin n → Fin n → Fin N) (D S I O : Finset (Fin N)),
  0 < h →
  (∀ σ ∈ A, ∀ τ ∈ A, σ ≠ τ →
    h ≤ (Finset.univ.filter (fun i : Fin n => σ i ≠ τ i)).card) →
  (∀ e ∈ G, e.1 ∉ D → e.2 ∉ D → (e.1 ∈ S ↔ e.2 ∉ S)) →
  let cover := fun (C : Finset (Fin N)) => ∀ e ∈ G, e.1 ∈ C ∨ e.2 ∈ C
  let selected := fun (C : Finset (Fin N)) =>
    cover C ∧ (∀ B, cover B → C.sum w ≤ B.sum w) ∧ I ⊆ C ∧ Disjoint O C
  let reads := fun (C : Finset (Fin N)) (σ : Equiv.Perm (Fin n)) =>
    ∀ i j, p i j ∈ C ↔ σ i = j
  (∀ C, selected C → ∃ σ ∈ A, reads C σ) →
  (∀ σ ∈ A, ∃ C, selected C ∧ reads C σ) →
  (∀ Z ∈ D.powerset,
    (A.filter (fun σ => ∃ C, selected C ∧ C ∩ D = Z ∧ reads C σ)).card ≤
      2 ^ (n / h)) ∧
  A.card ≤ 2 ^ (D.card + n / h) := by
  classical
  intro n h N A G w p D S I O hh hsep hbip cover selected reads hsel hA
  have key : ∀ Z : Finset (Fin N),
      (A.filter (fun σ => ∃ C, selected C ∧ C ∩ D = Z ∧ reads C σ)).card ≤ 2 ^ (n / h) := by
    intro Z
    obtain ⟨R, hR, hmem⟩ := PEqualNP.Outside.L_pcx_473.zbound n h N A G w p D S I O Z hh
      (by intro σ hσ τ hτ hne; convert hsep σ hσ τ hτ hne) hbip hsel
    refine le_trans (Finset.card_le_card_of_injOn (fun σ => (fun i => σ i))
      (fun σ hσ => hmem σ (Finset.mem_filter.1 hσ).1 (Finset.mem_filter.1 hσ).2)
      (fun a _ b _ hab => Equiv.ext (fun i => congrFun hab i))) hR
  refine ⟨fun Z _ => by convert key Z, ?_⟩
  have hsub : A ⊆ D.powerset.biUnion
      (fun Z => A.filter (fun σ => ∃ C, selected C ∧ C ∩ D = Z ∧ reads C σ)) := by
    intro σ hσ
    obtain ⟨C, hC, hr⟩ := hA σ hσ
    exact Finset.mem_biUnion.2 ⟨C ∩ D, Finset.mem_powerset.2 Finset.inter_subset_right,
      Finset.mem_filter.2 ⟨hσ, C, hC, rfl, hr⟩⟩
  calc A.card ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ Z ∈ D.powerset,
        (A.filter (fun σ => ∃ C, selected C ∧ C ∩ D = Z ∧ reads C σ)).card :=
      Finset.card_biUnion_le
    _ ≤ D.powerset.card • 2 ^ (n / h) := Finset.sum_le_card_nsmul _ _ _ (fun Z _ => key Z)
    _ = 2 ^ (D.card + n / h) := by rw [Finset.card_powerset, smul_eq_mul, pow_add]
