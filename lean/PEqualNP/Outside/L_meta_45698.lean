import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_45698_aux

variable {R : ℕ → ℕ}
def op (d : Bool) (a b : ℕ) : ℕ := bif d then a ||| b else a &&& b
lemma op_comm (d : Bool) (a b : ℕ) : op d a b = op d b a := by
  cases d <;> simp [op, Nat.and_comm, Nat.or_comm]
lemma op_bit (d : Bool) (a b i : ℕ) : (op d a b).testBit i =
    bif d then a.testBit i || b.testBit i else a.testBit i && b.testBit i := by
  cases d <;> simp [op]
lemma op_self (d : Bool) (a : ℕ) : op d a a = a := by cases d <;> simp [op]
def Al (R : ℕ → ℕ) (d : Bool) (a b : ℕ) : Prop := (R a &&& R b) ≤ (bif d then 1 else 0)
lemma Al.symm {d : Bool} {a b : ℕ} (h : Al R d a b) : Al R d b a := by unfold Al at *; rwa [Nat.and_comm]
def Z0 : ℕ → ℕ := fun _ => 0
lemma al0 (d : Bool) (a b : ℕ) : Al Z0 d a b := by simp [Al, Z0]
inductive Sol (R : ℕ → ℕ) (m T : ℕ) : ℕ → Set ℕ → Prop
  | done {q : ℕ} {S : Set ℕ} : T ∈ S → Sol R m T q S
  | un {q : ℕ} {S : Set ℕ} {a : ℕ} : a ∈ S → Sol R m T q (insert (a ^^^ m) S) → Sol R m T (q + 1) S
  | bi {q : ℕ} {S : Set ℕ} {d : Bool} {a b : ℕ} : a ∈ S → b ∈ S → Al R d a b →
      Sol R m T q (insert (op d a b) S) → Sol R m T (q + 1) S
lemma Sol.mono {m T q : ℕ} {S : Set ℕ} (h : Sol R m T q S) :
    ∀ {q' : ℕ} {S' : Set ℕ}, q ≤ q' → S ⊆ S' → Sol R m T q' S' := by
  induction h with
  | done h => intro q' S' _ hs; exact .done (hs h)
  | un h _ ih =>
    intro q' S' hq hs
    obtain ⟨r, rfl⟩ : ∃ r, q' = r + 1 := ⟨q' - 1, by omega⟩
    exact .un (hs h) (ih (by omega) (Set.insert_subset_insert hs))
  | bi h1 h2 ha _ ih =>
    intro q' S' hq hs
    obtain ⟨r, rfl⟩ : ∃ r, q' = r + 1 := ⟨q' - 1, by omega⟩
    exact .bi (hs h1) (hs h2) ha (ih (by omega) (Set.insert_subset_insert hs))
lemma Sol.rel {R' : ℕ → ℕ} {m T q : ℕ} {S : Set ℕ} (h : Sol R m T q S) (hR : ∀ d a b, Al R d a b → Al R' d a b) : Sol R' m T q S := by
  induction h with
  | done h => exact .done h
  | un h _ ih => exact .un h ih
  | bi h1 h2 ha _ ih => exact .bi h1 h2 (hR _ _ _ ha) ih
lemma Sol.to0 {m T q : ℕ} {S : Set ℕ} (h : Sol R m T q S) : Sol Z0 m T q S := h.rel fun d a b _ => al0 d a b
inductive Live (R : ℕ → ℕ) (m T : ℕ) : ℕ → ℕ → Finset ℕ → Prop
  | stop : Live R m T 0 0 {T}
  | un {k t : ℕ} {a : ℕ} {U : Finset ℕ} : Live R m T k t (insert (a ^^^ m) U) →
      Live R m T (k + 1) (t + 1) (insert a U)
  | bi {k t : ℕ} {d : Bool} {a b : ℕ} {U : Finset ℕ} : a ≠ b → Al R d a b → Live R m T k t (insert (op d a b) U) →
      Live R m T (k + 1) t (insert a (insert b U))
lemma Live.sol {m T k t : ℕ} {S : Finset ℕ} (h : Live R m T k t S) : Sol Z0 m T k (S : Set ℕ) := by
  induction h with
  | stop => exact .done (by simp)
  | @un k t a U _ ih =>
    refine .un (a := a) (by simp) (ih.mono le_rfl ?_)
    intro x hx; simp at hx ⊢; tauto
  | @bi k t d a b U _ _ _ ih =>
    refine .bi (d := d) (a := a) (b := b) (by simp) (by simp) (al0 _ _ _) (ih.mono le_rfl ?_)
    intro x hx; simp at hx ⊢; tauto
lemma Sol.live {m T q : ℕ} {S : Set ℕ} (h : Sol R m T q S) :
    ∃ k ≤ q, ∃ t, ∃ S0 : Finset ℕ, (S0 : Set ℕ) ⊆ S ∧ Live R m T k t S0 := by
  induction h with
  | @done q S h => exact ⟨0, by omega, 0, {T}, by simpa using h, .stop⟩
  | @un q S a ha _ ih =>
    obtain ⟨k, hk, t, S1, hs, hl⟩ := ih
    by_cases hg : a ^^^ m ∈ S1
    · refine ⟨k + 1, by omega, t + 1, insert a (S1.erase (a ^^^ m)), ?_, .un (by rwa [Finset.insert_erase hg])⟩
      intro x hx
      simp at hx
      rcases hx with rfl | ⟨h1, h2⟩
      · exact ha
      · exact (hs h1).resolve_left h2
    · exact ⟨k, by omega, t, S1, fun x hx => (hs hx).resolve_left (fun e => hg (e ▸ hx)), hl⟩
  | @bi q S d a b ha hb hal _ ih =>
    obtain ⟨k, hk, t, S1, hs, hl⟩ := ih
    by_cases hg : op d a b ∈ S1
    · by_cases hab : a = b
      · subst hab; rw [op_self] at hs
        exact ⟨k, by omega, t, S1, fun x hx => (hs hx).elim (fun e => e ▸ ha) id, hl⟩
      refine ⟨k + 1, by omega, t, insert a (insert b (S1.erase (op d a b))), ?_, .bi hab hal (by rwa [Finset.insert_erase hg])⟩
      intro x hx
      simp at hx
      rcases hx with rfl | rfl | ⟨h1, h2⟩
      · exact ha
      · exact hb
      · exact (hs h1).resolve_left h2
    · exact ⟨k, by omega, t, S1, fun x hx => (hs hx).resolve_left (fun e => hg (e ▸ hx)), hl⟩
def C (m : ℕ) (S : Set ℕ) : Set ℕ := S ∪ {0, m}
lemma C_mono {m : ℕ} {S S' : Set ℕ} (h : S ⊆ S') : C m S ⊆ C m S' := Set.union_subset_union_left _ h
lemma sub_C (m : ℕ) (S : Set ℕ) : S ⊆ C m S := Set.subset_union_left
def Un (m a : ℕ) (S S' : Finset ℕ) : Prop := ∃ U, S = insert a U ∧ S' = insert (a ^^^ m) U
def Bi (R : ℕ → ℕ) (d : Bool) (a b : ℕ) (S S' : Finset ℕ) : Prop :=
  a ≠ b ∧ ∃ U, S = insert a (insert b U) ∧ S' = insert (op d a b) U ∧ Al R d a b
lemma Un.live {m T a k t : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hl : Live R m T k t S') :
    Live R m T (k + 1) (t + 1) S := by obtain ⟨U, rfl, rfl⟩ := h; exact .un hl
lemma Bi.live {m T a b k t : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') (hl : Live R m T k t S') :
    Live R m T (k + 1) t S := by obtain ⟨hab, U, rfl, rfl, hal⟩ := h; exact .bi hab hal hl
lemma Bi.symm {a b : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') : Bi R d b a S S' := by
  obtain ⟨hab, U, rfl, rfl, hal⟩ := h
  exact ⟨hab.symm, U, Finset.insert_comm _ _ _, by rw [op_comm], hal.symm⟩
lemma Un.sub {m a : ℕ} {S S' : Finset ℕ} (h : Un m a S S') : a ∈ S ∧ S' ⊆ insert (a ^^^ m) S := by
  obtain ⟨U, rfl, rfl⟩ := h
  exact ⟨by simp, Finset.insert_subset_insert _ (Finset.subset_insert _ _)⟩
lemma Bi.sub {a b : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') :
    a ∈ S ∧ b ∈ S ∧ S' ⊆ insert (op d a b) S := by
  obtain ⟨_, U, rfl, rfl, _⟩ := h
  refine ⟨by simp, by simp, Finset.insert_subset_insert _ ?_⟩
  intro x hx; simp [hx]
def Min (R : ℕ → ℕ) (m T k t : ℕ) (S : Finset ℕ) : Prop := Live R m T k t S ∧ ∀ q < k, ¬ Sol Z0 m T q (C m S)
lemma Un.sol {m T a q : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hs : Sol Z0 m T q (C m S')) :
    Sol Z0 m T (q + 1) (C m S) := by
  obtain ⟨ha, hsub⟩ := h.sub
  refine .un (a := a) (sub_C _ _ (by simpa using ha)) (hs.mono le_rfl ?_)
  intro x hx
  rcases hx with hx | hx
  · have := hsub hx; simp at this
    rcases this with rfl | h'
    · exact Or.inl rfl
    · exact Or.inr (Or.inl h')
  · exact Or.inr (Or.inr hx)
lemma Bi.sol {m T a b q : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') (hs : Sol Z0 m T q (C m S')) :
    Sol Z0 m T (q + 1) (C m S) := by
  obtain ⟨ha, hb, hsub⟩ := h.sub
  refine .bi (d := d) (a := a) (b := b) (sub_C _ _ (by simpa using ha)) (sub_C _ _ (by simpa using hb)) (al0 _ _ _) (hs.mono le_rfl ?_)
  intro x hx
  rcases hx with hx | hx
  · have := hsub hx; simp at this
    rcases this with rfl | h'
    · exact Or.inl rfl
    · exact Or.inr (Or.inl h')
  · exact Or.inr (Or.inr hx)
lemma Un.min {m T a k t : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hl : Live R m T k t S')
    (hm : ∀ q < k + 1, ¬ Sol Z0 m T q (C m S)) : Min R m T k t S' :=
  ⟨hl, fun q hq hs => hm (q + 1) (by omega) (h.sol hs)⟩
lemma Bi.min {m T a b k t : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') (hl : Live R m T k t S')
    (hm : ∀ q < k + 1, ¬ Sol Z0 m T q (C m S)) : Min R m T k t S' :=
  ⟨hl, fun q hq hs => hm (q + 1) (by omega) (h.sol hs)⟩
lemma Un.fresh {m T a k t : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hl : Live R m T k t S')
    (hm : ∀ q < k + 1, ¬ Sol Z0 m T q (C m S)) : a ^^^ m ∉ C m S := by
  intro hg
  apply hm k (by omega)
  refine hl.sol.mono le_rfl fun x hx => ?_
  have := h.sub.2 hx; simp at this
  rcases this with rfl | h'
  · exact hg
  · exact Or.inl h'
lemma Bi.fresh {m T a b k t : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') (hl : Live R m T k t S')
    (hm : ∀ q < k + 1, ¬ Sol Z0 m T q (C m S)) : op d a b ∉ C m S := by
  intro hg
  apply hm k (by omega)
  refine hl.sol.mono le_rfl fun x hx => ?_
  have := h.sub.2.2 hx; simp at this
  rcases this with rfl | h'
  · exact hg
  · exact Or.inl h'
lemma Min.size {m T : ℕ} : ∀ {k t : ℕ} {S : Finset ℕ}, Min R m T k t S → S.card + t ≤ k + 1 ∧ t ≤ k := by
  intro k t S ⟨hl, hm⟩
  induction hl with
  | stop => simp
  | @un k t a U hl ih =>
    have hu : Un m a (insert a U) (insert (a ^^^ m) U) := ⟨U, rfl, rfl⟩
    have ih := ih (hu.min hl hm).2
    have hf : a ^^^ m ∉ U := fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
    have h1 := Finset.card_insert_le a U
    rw [Finset.card_insert_of_notMem hf] at ih; omega
  | @bi k t d a b U hab hal hl ih =>
    have hu : Bi R d a b (insert a (insert b U)) (insert (op d a b) U) := ⟨hab, U, rfl, rfl, hal⟩
    have ih := ih (hu.min hl hm).2
    have hf : op d a b ∉ U := fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
    have h1 := Finset.card_insert_le a (insert b U)
    have h2 := Finset.card_insert_le b U
    rw [Finset.card_insert_of_notMem hf] at ih; omega
def phi (a n : ℕ) (X : Finset ℕ) : Finset ℕ := insert a (X.erase n)
lemma phi_un {m a n c : ℕ} {X X' : Finset ℕ} (h : Un m c X X') (h1 : c ≠ n) (h2 : c ^^^ m ≠ n) :
    Un m c (phi a n X) (phi a n X') := by
  obtain ⟨U, rfl, rfl⟩ := h
  refine ⟨insert a (U.erase n), ?_, ?_⟩ <;> ext x <;> simp [phi] <;> grind
lemma phi_bi {a n b c : ℕ} {d : Bool} {X X' : Finset ℕ} (h : Bi R d b c X X') (h1 : b ≠ n) (h2 : c ≠ n)
    (h3 : op d b c ≠ n) : Bi R d b c (phi a n X) (phi a n X') := by
  obtain ⟨hab, U, rfl, rfl, hal⟩ := h
  refine ⟨hab, insert a (U.erase n), ?_, ?_, hal⟩ <;> ext x <;> simp [phi] <;> grind
lemma phi_back {m a : ℕ} {X : Finset ℕ} (h : a ^^^ m ∈ X) : Un m a (phi a (a ^^^ m) X) X :=
  ⟨X.erase (a ^^^ m), rfl, by rw [Finset.insert_erase h]⟩
lemma phi_start {m a : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hn : a ^^^ m ∉ S) : phi a (a ^^^ m) S' = S := by
  obtain ⟨U, rfl, rfl⟩ := h
  simp at hn
  simp [phi, hn.2]
lemma un_keep {m c n : ℕ} {X X' : Finset ℕ} (h : Un m c X X') (hn : n ∈ X) (h1 : c ≠ n) : n ∈ X' := by
  obtain ⟨U, rfl, rfl⟩ := h
  simp at hn ⊢; exact Or.inr (hn.resolve_left (Ne.symm h1))
lemma bi_keep {b c n : ℕ} {d : Bool} {X X' : Finset ℕ} (h : Bi R d b c X X') (hn : n ∈ X) (h1 : b ≠ n)
    (h2 : c ≠ n) : n ∈ X' := by
  obtain ⟨_, U, rfl, rfl, _⟩ := h
  simp at hn ⊢; rcases hn with h | h | h
  · exact absurd h.symm h1
  · exact absurd h.symm h2
  · exact Or.inr h
lemma first_move {m T : ℕ} : ∀ (k t : ℕ) (S : Finset ℕ), Min R m T k t S → 2 ≤ S.card →
    (∃ k0 d a b S1, k = k0 + 1 ∧ Bi R d a b S S1 ∧ Live R m T k0 t S1) ∨
    (∃ k0 t0 a d c S1 S2, k = k0 + 2 ∧ t = t0 + 1 ∧ Un m a S S1 ∧ Bi R d (a ^^^ m) c S1 S2 ∧ Live R m T k0 t0 S2) ∨
    (∃ k0 t0 a a' d S1 S2 S3, k = k0 + 3 ∧ t = t0 + 2 ∧ Un m a S S1 ∧ a' ≠ a ^^^ m ∧ Un m a' S1 S2 ∧
      Bi R d (a ^^^ m) (a' ^^^ m) S2 S3 ∧ Live R m T k0 t0 S3) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro t S hS hc
  obtain ⟨hl, hm⟩ := hS
  cases hl with
  | stop => simp at hc
  | @bi k t d a b U hab hal hl => exact Or.inl ⟨k, d, a, b, _, rfl, ⟨hab, U, rfl, rfl, hal⟩, hl⟩
  | @un k t a U hl =>
    have hu : Un m a (insert a U) (insert (a ^^^ m) U) := ⟨U, rfl, rfl⟩
    have hf := hu.fresh hl hm
    have hn : a ^^^ m ∉ insert a U := fun h => hf (sub_C _ _ (by simpa using h))
    have hmin := hu.min hl hm
    have hxx : ∀ c : ℕ, c ^^^ m ^^^ m = c := fun c => by simp
    have hc' : 2 ≤ (insert (a ^^^ m) U).card := by
      have h1 := Finset.card_insert_le a U
      rw [Finset.card_insert_of_notMem (fun h => hn (by simp [h]))]; omega
    generalize hS1 : insert (a ^^^ m) U = S1 at *
    have hnS1 : a ^^^ m ∈ S1 := by rw [← hS1]; simp
    have hst := phi_start hu hn
    have dbl : ∀ {c k2 t2 S2}, Un m c S1 S2 → Live R m T k2 t2 S2 → k = k2 + 1 → c ≠ a ^^^ m ∧ c ^^^ m ≠ a ^^^ m := by
      intro c k2 t2 S2 h2 hl2 hk
      constructor
      · rintro rfl
        have hsub := h2.sub.2
        rw [hxx] at hsub
        apply hm (k2 + 1) (by omega)
        refine .un (a := a) (sub_C _ _ (by simp)) (hl2.sol.mono le_rfl fun x hx => ?_)
        have h3 := hsub hx
        have h4 : x ∈ insert a (insert (a ^^^ m) U) := by rw [hS1]; exact h3
        simp at h4
        rcases h4 with rfl | rfl | h4
        · exact Or.inr (sub_C _ _ (by simp))
        · exact Or.inl rfl
        · exact Or.inr (sub_C _ _ (by simp [h4]))
      · intro e
        exact h2.fresh hl2 (by rw [← hk]; exact hmin.2) (sub_C _ _ (by rw [e]; simpa using hnS1))
    rcases ih k (by omega) t S1 hmin hc' with
      ⟨k0, d, x, y, S2, rfl, hb, hl2⟩ | ⟨k0, t0, c, d, y, S2, S3, rfl, rfl, h1, hb, hl2⟩ |
      ⟨k0, t0, c, c', d, S2, S3, S4, rfl, rfl, h1, hne, h2, hb, hl2⟩
    · by_cases hx : x = a ^^^ m
      · subst hx; exact Or.inr (Or.inl ⟨k0, t, a, d, y, S1, S2, rfl, rfl, hu, hb, hl2⟩)
      by_cases hy : y = a ^^^ m
      · subst hy; exact Or.inr (Or.inl ⟨k0, t, a, d, x, S1, S2, rfl, rfl, hu, hb.symm, hl2⟩)
      have hg : op d x y ≠ a ^^^ m := fun e => hb.fresh hl2 hmin.2 (sub_C _ _ (by rw [e]; simpa using hnS1))
      refine Or.inl ⟨k0 + 1, d, x, y, phi a (a ^^^ m) S2, rfl, ?_, ?_⟩
      · rw [← hst]; exact phi_bi hb hx hy hg
      · exact (phi_back (bi_keep hb hnS1 hx hy)).live hl2
    · have hb1 := hb.live hl2
      obtain ⟨n1, n2⟩ := dbl h1 hb1 rfl
      have hm2 := h1.min hb1 hmin.2
      by_cases hy : y = a ^^^ m
      · subst hy
        exact Or.inr (Or.inr ⟨k0, t0, a, c, d, S1, S2, S3, rfl, rfl, hu, n1, h1, hb.symm, hl2⟩)
      have hk2 := un_keep h1 hnS1 n1
      have hg : op d (c ^^^ m) y ≠ a ^^^ m := fun e => hb.fresh hl2 hm2.2 (sub_C _ _ (by rw [e]; simpa using hk2))
      refine Or.inr (Or.inl ⟨k0 + 1, t0 + 1, c, d, y, phi a (a ^^^ m) S2, phi a (a ^^^ m) S3, rfl, rfl, ?_, phi_bi hb n2 hy hg, ?_⟩)
      · rw [← hst]; exact phi_un h1 n1 n2
      · exact (phi_back (bi_keep hb hk2 n2 hy)).live hl2
    · have hb1 := hb.live hl2
      have hb2 := h2.live hb1
      obtain ⟨n1, n2⟩ := dbl h1 hb2 rfl
      have hm2 := h1.min hb2 hmin.2
      have hk2 := un_keep h1 hnS1 n1
      have hm3 := h2.min hb1 hm2.2
      have n3 : c' ≠ a ^^^ m := by
        rintro rfl
        have hsub := h2.sub.2
        rw [hxx] at hsub
        obtain ⟨hcS, hsub1⟩ := h1.sub
        have hcS' : c ∈ insert a U := by
          have : c ∈ insert (a ^^^ m) U := by rw [hS1]; exact hcS
          simp at this ⊢; exact Or.inr (this.resolve_left n1)
        apply hm (k0 + 1 + 1 + 1) (by omega)
        refine .un (a := a) (sub_C _ _ (by simp)) (.un (a := c) (Or.inr (sub_C _ _ (by simpa using hcS'))) (hb1.sol.mono le_rfl fun x hx => ?_))
        have h3 : x = a ∨ x = c ^^^ m ∨ x ∈ S1 := by
          have := hsub hx; simp at this
          rcases this with h | h
          · exact Or.inl h
          · have := hsub1 h; simp at this; exact Or.inr this
        rcases h3 with rfl | rfl | h3
        · exact Or.inr (Or.inr (sub_C _ _ (by simp)))
        · exact Or.inl rfl
        · rw [← hS1] at h3; simp at h3
          rcases h3 with rfl | h3
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (sub_C _ _ (by simp [h3])))
      have n4 : c' ^^^ m ≠ a ^^^ m := fun e => h2.fresh hb1 hm2.2 (sub_C _ _ (by rw [e]; simpa using hk2))
      have hk3 := un_keep h2 hk2 n3
      have hg : op d (c ^^^ m) (c' ^^^ m) ≠ a ^^^ m := fun e => hb.fresh hl2 hm3.2 (sub_C _ _ (by rw [e]; simpa using hk3))
      refine Or.inr (Or.inr ⟨k0 + 1, t0 + 1, c, c', d, phi a (a ^^^ m) S2, phi a (a ^^^ m) S3, phi a (a ^^^ m) S4, rfl, rfl, ?_, hne,
        phi_un h2 n3 n4, phi_bi hb n2 n4 hg, ?_⟩)
      · rw [← hst]; exact phi_un h1 n1 n2
      · exact (phi_back (bi_keep hb hk3 n2 n4)).live hl2
lemma and_op (d : Bool) (a b n : ℕ) : op d a b &&& n = op d (a &&& n) (b &&& n) := by
  apply Nat.eq_of_testBit_eq; intro i
  cases d <;> simp [op_bit] <;> grind
lemma and_neg {m n : ℕ} (hn : n &&& m = n) (a : ℕ) : (a ^^^ m) &&& n = (a &&& n) ^^^ n := by
  apply Nat.eq_of_testBit_eq; intro i
  have := congrArg (fun x => x.testBit i) hn
  simp at this ⊢
  grind
abbrev Cst (n x : ℕ) : Prop := x &&& n = 0 ∨ x &&& n = n
def Im (n : ℕ) (S : Finset ℕ) : Set ℕ := (fun x => x &&& n) '' (S : Set ℕ)
lemma Im_mem {n x : ℕ} {S : Finset ℕ} (h : x ∈ S) : x &&& n ∈ C n (Im n S) := Or.inl ⟨x, by simpa using h, rfl⟩
lemma Cst_mem {n x : ℕ} {S : Set ℕ} (h : Cst n x) : x &&& n ∈ C n S := by
  rcases h with h | h <;> simp [C, h]
lemma Cst_neg {m n a : ℕ} (hn : n &&& m = n) : Cst n (a ^^^ m) ↔ Cst n a := by
  unfold Cst; rw [and_neg hn]
  constructor
  · rintro (h | h)
    · right; have := congrArg (· ^^^ n) h; simpa using this
    · left; have := congrArg (· ^^^ n) h; simpa using this
  · rintro (h | h) <;> simp [h]
lemma op_cst {n a b : ℕ} (d : Bool) (ha : Cst n a) :
    op d a b &&& n = 0 ∨ op d a b &&& n = n ∨ op d a b &&& n = b &&& n := by
  rw [and_op]
  rcases ha with h | h <;> rw [h] <;> cases d
  · left; simp [op]
  · right; right; simp [op]
  · right; right; apply Nat.eq_of_testBit_eq; intro i; simp [op]
  · right; left; apply Nat.eq_of_testBit_eq; intro i; simp [op]
lemma op_cst2 {n a b : ℕ} (d : Bool) (ha : Cst n a) (hb : Cst n b) : Cst n (op d a b) := by
  rcases op_cst (b := b) d ha with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · unfold Cst at hb ⊢; rw [h]; exact hb
lemma op_cst_mem {n a b : ℕ} {S : Finset ℕ} (d : Bool) (h : Cst n a ∨ Cst n b) (ha : a ∈ S) (hb : b ∈ S) :
    op d a b &&& n ∈ C n (Im n S) := by
  rcases h with h | h
  · rcases op_cst (b := b) d h with e | e | e <;> rw [e]
    · simp [C]
    · simp [C]
    · exact Im_mem hb
  · rw [op_comm]
    rcases op_cst (b := a) d h with e | e | e <;> rw [e]
    · simp [C]
    · simp [C]
    · exact Im_mem ha
lemma C_Im_sub {n g : ℕ} {S S' : Finset ℕ} {Q : Set ℕ} (h : S' ⊆ insert g S) (hg : g &&& n ∈ Q)
    (hQ : C n (Im n S) ⊆ Q) : C n (Im n S') ⊆ Q := by
  rintro x (⟨y, hy, rfl⟩ | hx)
  · have := h hy; simp at this
    rcases this with rfl | h'
    · exact hg
    · exact hQ (Im_mem h')
  · exact hQ (Or.inr hx)
section proj
variable {m T n : ℕ} (hn : n &&& m = n)
include hn
lemma Un.im {a q : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hs : Sol Z0 n (T &&& n) q (C n (Im n S'))) :
    Sol Z0 n (T &&& n) (q + 1) (C n (Im n S)) := by
  obtain ⟨ha, hsub⟩ := h.sub
  refine .un (Im_mem ha) (hs.mono le_rfl (C_Im_sub hsub ?_ (Set.subset_insert _ _)))
  rw [and_neg hn]; exact Or.inl rfl
omit hn in
lemma Bi.im {a b q : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') (hs : Sol Z0 n (T &&& n) q (C n (Im n S'))) :
    Sol Z0 n (T &&& n) (q + 1) (C n (Im n S)) := by
  obtain ⟨ha, hb, hsub⟩ := h.sub
  refine .bi (d := d) (Im_mem ha) (Im_mem hb) (al0 _ _ _) (hs.mono le_rfl (C_Im_sub hsub ?_ (Set.subset_insert _ _)))
  rw [and_op]; exact Or.inl rfl
lemma Un.kill {a q : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hc : Cst n a) (hs : Sol Z0 n (T &&& n) q (C n (Im n S'))) :
    Sol Z0 n (T &&& n) q (C n (Im n S)) :=
  hs.mono le_rfl (C_Im_sub h.sub.2 (Cst_mem ((Cst_neg hn).2 hc)) subset_rfl)
omit hn in
lemma Bi.kill {a b q : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') (hc : Cst n a ∨ Cst n b)
    (hs : Sol Z0 n (T &&& n) q (C n (Im n S'))) : Sol Z0 n (T &&& n) q (C n (Im n S)) :=
  hs.mono le_rfl (C_Im_sub h.sub.2.2 (op_cst_mem d hc h.sub.1 h.sub.2.1) subset_rfl)
lemma Min.const (hT0 : T &&& n ≠ 0) (hT1 : T &&& n ≠ n) {k t : ℕ} {S : Finset ℕ} (h : Min R m T k t S) :
    ∃ q, q + (S.filter (Cst n)).card ≤ k ∧ Sol Z0 n (T &&& n) q (C n (Im n S)) := by
  obtain ⟨hl, hm⟩ := h
  induction hl with
  | stop =>
    refine ⟨0, ?_, .done (Im_mem (by simp))⟩
    rw [Finset.filter_eq_empty_iff.2]; · simp
    intro x hx; simp at hx; subst hx
    rintro (h | h); exacts [hT0 h, hT1 h]
  | @un k t a U hl ih =>
    have hu : Un m a (insert a U) (insert (a ^^^ m) U) := ⟨U, rfl, rfl⟩
    obtain ⟨q, hq, hs⟩ := ih (hu.min hl hm).2
    have h1 : (U.filter (Cst n)).card ≤ ((insert (a ^^^ m) U).filter (Cst n)).card :=
      Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_insert _ _))
    by_cases hc : Cst n a
    · refine ⟨q, ?_, hu.kill hn hc hs⟩
      rw [Finset.filter_insert, ite_eq_left hc]
      have := Finset.card_insert_le a (U.filter (Cst n)); omega
    · refine ⟨q + 1, ?_, hu.im hn hs⟩
      rw [Finset.filter_insert, ite_eq_right hc]; omega
  | @bi k t d a b U hab hal hl ih =>
    have hu : Bi R d a b (insert a (insert b U)) (insert (op d a b) U) := ⟨hab, U, rfl, rfl, hal⟩
    obtain ⟨q, hq, hs⟩ := ih (hu.min hl hm).2
    have hf : op d a b ∉ U := fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
    have h1 : (U.filter (Cst n)).card ≤ ((insert (op d a b) U).filter (Cst n)).card :=
      Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_insert _ _))
    have ca := Finset.card_insert_le a (U.filter (Cst n))
    have cb := Finset.card_insert_le b (U.filter (Cst n))
    by_cases hca : Cst n a
    · refine ⟨q, ?_, hu.kill (Or.inl hca) hs⟩
      rw [Finset.filter_insert, ite_eq_left hca, Finset.filter_insert]
      by_cases hcb : Cst n b
      · rw [ite_eq_left hcb]
        rw [Finset.filter_insert, ite_eq_left (op_cst2 d hca hcb), Finset.card_insert_of_notMem (by simp [hf])] at hq
        have := Finset.card_insert_le a (insert b (U.filter (Cst n))); omega
      · rw [ite_eq_right hcb]; omega
    · rw [Finset.filter_insert, ite_eq_right hca, Finset.filter_insert]
      by_cases hcb : Cst n b
      · refine ⟨q, ?_, hu.kill (Or.inr hcb) hs⟩
        rw [ite_eq_left hcb]; omega
      · refine ⟨q + 1, ?_, hu.im hs⟩
        rw [ite_eq_right hcb]; omega
end proj
lemma Min.proper {m T k t : ℕ} (hT : T &&& m = T) (hT0 : T ≠ 0) (hT1 : T ≠ m) {S : Finset ℕ} (hS : ∀ x ∈ S, x &&& m = x)
    (h : Min R m T k t S) : 0 ∉ S ∧ m ∉ S := by
  obtain ⟨q, hq, hs⟩ := h.const (n := m) (by simp) (by rwa [hT]) (by rwa [hT])
  have hi : Im m S = (S : Set ℕ) := by
    ext x; constructor
    · rintro ⟨y, hy, rfl⟩; have := hS y hy; simp only; rw [this]; exact hy
    · intro hx; exact ⟨x, hx, hS x hx⟩
  rw [hi, hT] at hs
  have key : ∀ x ∈ S, ¬ Cst m x := by
    intro x hx hc
    have : 0 < (S.filter (Cst m)).card := Finset.card_pos.2 ⟨x, by simp [hx, hc]⟩
    exact h.2 q (by omega) hs
  exact ⟨fun h0 => key 0 h0 (Or.inl (by simp)), fun h1 => key m h1 (Or.inr (by simp))⟩
def sepb (N : ℕ) (d : Bool) (w i : ℕ) : Bool :=
  bif d then xor (w.testBit i) (w.testBit (N + i)) else w.testBit i && !w.testBit (N + i)
def pos' (t : ℕ) : Bool := decide (0 < t)
section cov
variable {N m T i : ℕ} (m1 : m.testBit i = true) (m2 : m.testBit (N + i) = true)
  (t1 : T.testBit i = true) (t2 : T.testBit (N + i) = false)
include t1 t2 m1 m2
lemma Live.cov {k t : ℕ} {S : Finset ℕ} (h : Live R m T k t S) : ∃ w ∈ S, sepb N (pos' t) w i = true := by
  induction h with
  | stop => exact ⟨T, by simp, by simp [sepb, pos', t1, t2]⟩
  | @un k t a U _ ih =>
    obtain ⟨w, hw, hs⟩ := ih
    have weak : sepb N true w i = true := by
      revert hs; cases pos' t <;> simp [sepb] <;> cases w.testBit i <;> cases w.testBit (N + i) <;> simp
    simp at hw
    rcases hw with rfl | hw
    · refine ⟨a, by simp, ?_⟩
      revert weak; simp [sepb, pos', m1, m2]
    · exact ⟨w, by simp [hw], by simpa [pos'] using weak⟩
  | @bi k t d a b U _ _ _ ih =>
    obtain ⟨w, hw, hs⟩ := ih
    simp at hw
    rcases hw with rfl | hw
    · by_cases ha : sepb N (pos' t) a i = true
      · exact ⟨a, by simp, ha⟩
      · refine ⟨b, by simp, ?_⟩
        revert hs ha
        unfold sepb; simp only [op_bit]
        cases pos' t <;> cases d <;> cases a.testBit i <;> cases a.testBit (N + i) <;> cases b.testBit i <;>
          cases b.testBit (N + i) <;> simp
    · exact ⟨w, by simp [hw], hs⟩
end cov
def Uq (N : ℕ) (e : Bool) (S : Finset ℕ) (a i : ℕ) : Prop :=
  sepb N e a i = true ∧ ∀ c ∈ S, c ≠ a → sepb N e c i = false
lemma sepb_weak {N w i : ℕ} (e : Bool) (h : sepb N e w i = true) : sepb N true w i = true := by
  revert h; cases e <;> simp [sepb] <;> cases w.testBit i <;> cases w.testBit (N + i) <;> simp
section rect
variable {N m T : ℕ}
def Lg (N m T i : ℕ) : Prop := m.testBit i = true ∧ m.testBit (N + i) = true ∧ T.testBit i = true ∧ T.testBit (N + i) = false
lemma bi_uq {a b k t c i : ℕ} {d e : Bool} {U : Finset ℕ} (he : e = true ∨ e = pos' t) (hl : Live R m T k t (insert (op d a b) U))
    (ha : a ∉ U) (hb : b ∉ U) (hi : Lg N m T i)
    (hc : c ∈ insert a (insert b U)) (h : Uq N e (insert a (insert b U)) c i) :
    Uq N e (insert (op d a b) U) (if c = a ∨ c = b then op d a b else c) i := by
  obtain ⟨w, hw, hs⟩ := hl.cov hi.1 hi.2.1 hi.2.2.1 hi.2.2.2
  have hs : sepb N e w i = true := by
    rcases he with rfl | rfl
    · exact sepb_weak _ hs
    · exact hs
  by_cases hcc : c = a ∨ c = b
  · rw [ite_eq_left hcc]
    have hU : ∀ x ∈ U, sepb N e x i = false := by
      intro x hx
      refine h.2 x (by simp [hx]) ?_
      rintro rfl
      rcases hcc with rfl | rfl; exacts [ha hx, hb hx]
    simp at hw
    rcases hw with rfl | hw
    · refine ⟨hs, fun x hx hne => ?_⟩
      simp at hx; exact hU x (hx.resolve_left hne)
    · rw [hU w hw] at hs; simp at hs
  · rw [ite_eq_right hcc]
    push Not at hcc
    refine ⟨h.1, fun x hx hne => ?_⟩
    simp at hx
    rcases hx with rfl | hx
    · have h1 := h.2 a (by simp) (Ne.symm hcc.1)
      have h2 := h.2 b (by simp) (Ne.symm hcc.2)
      revert h1 h2; unfold sepb; simp only [op_bit]
      cases e <;> cases d <;> cases a.testBit i <;> cases a.testBit (N + i) <;> cases b.testBit i <;>
          cases b.testBit (N + i) <;> simp
    · exact h.2 x (by simp [hx]) hne
lemma un_uq {a c i : ℕ} {U : Finset ℕ} (hi : Lg N m T i) (ha : a ∉ U)
    (hc : c ∈ insert a U) (h : Uq N true (insert a U) c i) :
    Uq N true (insert (a ^^^ m) U) (if c = a then a ^^^ m else c) i := by
  have hn : sepb N true (a ^^^ m) i = sepb N true a i := by simp [sepb, hi.1, hi.2.1]
  by_cases hcc : c = a
  · rw [ite_eq_left hcc]; subst hcc
    refine ⟨by rw [hn]; exact h.1, fun x hx hne => ?_⟩
    simp at hx
    exact h.2 x (by simp [hx.resolve_left hne]) (fun e => ha (e ▸ hx.resolve_left hne))
  · rw [ite_eq_right hcc]
    refine ⟨h.1, fun x hx hne => ?_⟩
    simp at hx
    rcases hx with rfl | hx
    · rw [hn]; exact h.2 a (by simp) (Ne.symm hcc)
    · exact h.2 x (by simp [hx]) hne
lemma phi_mem {x y g c : ℕ} {U : Finset ℕ} (hc : c ∈ insert x (insert y U)) :
    (if c = x ∨ c = y then g else c) ∈ insert g U := by
  split_ifs with h
  · simp
  · simp only [Finset.mem_insert] at hc ⊢; tauto
lemma phi_ne {x y g a b : ℕ} {U : Finset ℕ} (hg : g ∉ U) (ha : a ∈ insert x (insert y U)) (hb : b ∈ insert x (insert y U))
    (hab : a ≠ b) (h : ¬ ((a = x ∨ a = y) ∧ (b = x ∨ b = y))) :
    (if a = x ∨ a = y then g else a) ≠ (if b = x ∨ b = y then g else b) := by
  simp only [Finset.mem_insert] at ha hb
  split_ifs with p q q
  · exact absurd ⟨p, q⟩ h
  · rintro rfl; tauto
  · rintro rfl; tauto
  · exact hab
lemma bi_tight {a b k t : ℕ} {d : Bool} {U : Finset ℕ} (hab : a ≠ b) (hal : Al R d a b) (hl : Live R m T k t (insert (op d a b) U))
    (hm : ∀ q < k + 1, ¬ Sol Z0 m T q (C m ((insert a (insert b U) : Finset ℕ) : Set ℕ)))
    (hc : (insert a (insert b U)).card + t = k + 2) :
    a ∉ U ∧ b ∉ U ∧ op d a b ∉ U ∧ (insert (op d a b) U).card + t = k + 1 ∧ Min R m T k t (insert (op d a b) U) := by
  have hu : Bi R d a b (insert a (insert b U)) (insert (op d a b) U) := ⟨hab, U, rfl, rfl, hal⟩
  have hf : op d a b ∉ U := fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
  have hmin := hu.min hl hm
  have hs := hmin.size.1
  rw [Finset.card_insert_of_notMem hf] at hs ⊢
  have h1 := Finset.card_insert_le a (insert b U)
  have h2 := Finset.card_insert_le b U
  have ha : a ∉ insert b U := fun h => by rw [Finset.insert_eq_of_mem h] at hc; omega
  have hb : b ∉ U := fun h => by rw [Finset.insert_eq_of_mem h] at hc h1; omega
  exact ⟨fun h => ha (by simp [h]), hb, hf, by omega, hmin⟩
lemma un_tight {a k t : ℕ} {U : Finset ℕ} (hl : Live R m T k t (insert (a ^^^ m) U))
    (hm : ∀ q < k + 1, ¬ Sol Z0 m T q (C m ((insert a U : Finset ℕ) : Set ℕ)))
    (hc : (insert a U).card + (t + 1) = k + 2) :
    a ∉ U ∧ a ^^^ m ∉ U ∧ (insert (a ^^^ m) U).card + t = k + 1 ∧ Min R m T k t (insert (a ^^^ m) U) := by
  have hu : Un m a (insert a U) (insert (a ^^^ m) U) := ⟨U, rfl, rfl⟩
  have hf : a ^^^ m ∉ U := fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
  have hmin := hu.min hl hm
  have hs := hmin.size.1
  rw [Finset.card_insert_of_notMem hf] at hs ⊢
  have h1 := Finset.card_insert_le a U
  have ha : a ∉ U := fun h => by rw [Finset.insert_eq_of_mem h] at hc; omega
  exact ⟨ha, hf, by omega, hmin⟩
lemma rect0 {k : ℕ} {S : Finset ℕ} (hl : Live R m T k 0 S) (hm : ∀ q < k, ¬ Sol Z0 m T q (C m (S : Set ℕ)))
    (hc : S.card = k + 1) {i1 i2 j1 j2 : ℕ} (h1 : Lg N m T i1) (h2 : Lg N m T i2) (h3 : Lg N m T j1) (h4 : Lg N m T j2) :
    ∀ {a b : ℕ}, a ∈ S → b ∈ S → a ≠ b →
    (∀ w ∈ S, w.testBit i1 = w.testBit i2) → (∀ w ∈ S, w.testBit (N + j1) = w.testBit (N + j2)) →
    Uq N false S a i1 → Uq N false S b i2 → Uq N false S a j1 → Uq N false S b j2 → False := by
  generalize ht : 0 = t at hl
  induction hl with
  | stop => intro a b ha hb hab; simp at ha hb; exact absurd (ha.trans hb.symm) hab
  | un => omega
  | @bi k t d x y U hxy hal hl ih =>
    subst ht
    intro a b ha hb hab r1 r2 u1 u2 u3 u4
    obtain ⟨hx, hy, hg, hc', hmin⟩ := bi_tight hxy hal hl hm (by simpa using hc)
    have tr : ∀ {c i}, Lg N m T i → c ∈ insert x (insert y U) → Uq N false (insert x (insert y U)) c i →
        Uq N false (insert (op d x y) U) (if c = x ∨ c = y then op d x y else c) i :=
      fun hi hc h => bi_uq (Or.inr (by simp [pos'])) hl hx hy hi hc h
    by_cases hab' : (a = x ∨ a = y) ∧ (b = x ∨ b = y)
    · have v1 := tr h1 ha u1; have v2 := tr h2 hb u2; have v3 := tr h3 ha u3; have v4 := tr h4 hb u4
      rw [ite_eq_left hab'.1] at v1 v3; rw [ite_eq_left hab'.2] at v2 v4
      have hop : op d x y = op d a b := by
        rcases hab' with ⟨rfl | rfl, rfl | rfl⟩
        · exact absurd rfl hab
        · rfl
        · exact op_comm _ _ _
        · exact absurd rfl hab
      rw [hop] at v1 v2 v3 v4
      have e1 := r1 b hb; have e2 := r2 b hb
      have n1 := u1.2 b hb (Ne.symm hab); have n3 := u3.2 b hb (Ne.symm hab)
      have s1 := v1.1; have s3 := v3.1; have s2 := u2.1; have s4 := u4.1
      revert e1 e2 n1 n3 s1 s3 s2 s4
      unfold sepb; simp only [op_bit]
      cases d <;> simp <;> grind
    · refine ih hmin.2 (by simpa using hc') rfl ?_ ?_ ?_ ?_ ?_ (tr h1 ha u1) (tr h2 hb u2) (tr h3 ha u3) (tr h4 hb u4)
      · exact phi_mem ha
      · exact phi_mem hb
      · exact phi_ne hg ha hb hab hab'
      · intro w hw; simp at hw
        rcases hw with rfl | hw
        · simp only [op_bit, r1 x (by simp), r1 y (by simp)]
        · exact r1 w (by simp [hw])
      · intro w hw; simp at hw
        rcases hw with rfl | hw
        · simp only [op_bit, r2 x (by simp), r2 y (by simp)]
        · exact r2 w (by simp [hw])
lemma polar {k t : ℕ} {S : Finset ℕ} (hl : Live R m T k t S) (hm : ∀ q < k, ¬ Sol Z0 m T q (C m (S : Set ℕ)))
    (hc : S.card + t = k + 1) {i j : ℕ} (h1 : Lg N m T i) (h2 : Lg N m T j) :
    ∀ {a : ℕ}, a ∈ S → Uq N true S a i → Uq N true S a j → a.testBit i = a.testBit j := by
  induction hl with
  | stop => intro a ha _ _; simp at ha; subst ha; rw [h1.2.2.1, h2.2.2.1]
  | @un k t x U hl ih =>
    intro a ha u1 u2
    obtain ⟨hx, hg, hc', hmin⟩ := un_tight hl hm (by omega)
    have := ih hmin.2 hc' (a := if a = x then x ^^^ m else a) (by split_ifs with h <;> simp at ha ⊢; tauto)
      (un_uq h1 hx ha u1) (un_uq h2 hx ha u2)
    split_ifs at this with h
    · subst h; simpa [h1.1, h2.1] using this
    · exact this
  | @bi k t d x y U hxy hal hl ih =>
    intro a ha u1 u2
    obtain ⟨hx, hy, hg, hc', hmin⟩ := bi_tight hxy hal hl hm (by omega)
    have v1 := bi_uq (Or.inl rfl) hl hx hy h1 ha u1
    have v2 := bi_uq (Or.inl rfl) hl hx hy h2 ha u2
    have := ih hmin.2 hc' (phi_mem ha) v1 v2
    split_ifs at this v1 v2 with h
    · obtain ⟨b, hb, hab, hop⟩ : ∃ b ∈ insert x (insert y U), b ≠ a ∧ op d x y = op d a b := by
        rcases h with rfl | rfl
        · exact ⟨y, by simp, Ne.symm hxy, rfl⟩
        · exact ⟨x, by simp, hxy, op_comm _ _ _⟩
      rw [hop] at this v1 v2
      have n1 := u1.2 b hb hab; have n2 := u2.2 b hb hab
      have s1 := v1.1; have s2 := v2.1; have p1 := u1.1; have p2 := u2.1
      revert this n1 n2 s1 s2 p1 p2
      unfold sepb; simp only [op_bit]
      cases d <;> simp <;> grind
    · exact this
lemma rect1 {k t : ℕ} {S : Finset ℕ} (hl : Live R m T k t S) (hm : ∀ q < k, ¬ Sol Z0 m T q (C m (S : Set ℕ)))
    (hc : S.card + t = k + 1) {i1 i2 j1 j2 : ℕ} (h1 : Lg N m T i1) (h2 : Lg N m T i2) (h3 : Lg N m T j1) (h4 : Lg N m T j2) :
    ∀ {a b : ℕ}, a ∈ S → b ∈ S → a ≠ b →
    (∀ w ∈ S, w.testBit i1 = w.testBit i2) → (∀ w ∈ S, w.testBit (N + j1) = w.testBit (N + j2)) →
    Uq N true S a i1 → Uq N true S b i2 → Uq N true S a j1 → Uq N true S b j2 → False := by
  induction hl with
  | stop => intro a b ha hb hab; simp at ha hb; exact absurd (ha.trans hb.symm) hab
  | @un k t x U hl ih =>
    intro a b ha hb hab r1 r2 u1 u2 u3 u4
    obtain ⟨hx, hg, hc', hmin⟩ := un_tight hl hm (by omega)
    refine ih hmin.2 hc' ?_ ?_ ?_ ?_ ?_ (un_uq h1 hx ha u1) (un_uq h2 hx hb u2) (un_uq h3 hx ha u3) (un_uq h4 hx hb u4)
    · split_ifs with h <;> simp at ha ⊢; tauto
    · split_ifs with h <;> simp at hb ⊢; tauto
    · split_ifs with p q q
      · exact absurd (p.trans q.symm) hab
      · intro e; simp at hb; rw [← e] at hb; rcases hb with h | h
        · exact q (by rw [← e, h])
        · exact hg h
      · intro e; simp at ha; rw [e] at ha; rcases ha with h | h
        · exact p (by rw [e, h])
        · exact hg h
      · exact hab
    · intro w hw; simp at hw
      rcases hw with rfl | hw
      · simp [r1 x (by simp), h1.1, h2.1]
      · exact r1 w (by simp [hw])
    · intro w hw; simp at hw
      rcases hw with rfl | hw
      · simp [r2 x (by simp), h3.2.1, h4.2.1]
      · exact r2 w (by simp [hw])
  | @bi k t d x y U hxy hal hl ih =>
    intro a b ha hb hab r1 r2 u1 u2 u3 u4
    obtain ⟨hx, hy, hg, hc', hmin⟩ := bi_tight hxy hal hl hm (by omega)
    have tr : ∀ {c i}, Lg N m T i → c ∈ insert x (insert y U) → Uq N true (insert x (insert y U)) c i →
        Uq N true (insert (op d x y) U) (if c = x ∨ c = y then op d x y else c) i :=
      fun hi hc h => bi_uq (Or.inl rfl) hl hx hy hi hc h
    by_cases hab' : (a = x ∨ a = y) ∧ (b = x ∨ b = y)
    · have v1 := tr h1 ha u1; have v2 := tr h2 hb u2; have v3 := tr h3 ha u3; have v4 := tr h4 hb u4
      rw [ite_eq_left hab'.1] at v1 v3; rw [ite_eq_left hab'.2] at v2 v4
      have hpol := polar hl hmin.2 hc' h1 h3 (by simp) v1 v3
      have hop : op d x y = op d a b := by
        rcases hab' with ⟨rfl | rfl, rfl | rfl⟩
        · exact absurd rfl hab
        · rfl
        · exact op_comm _ _ _
        · exact absurd rfl hab
      rw [hop] at v1 v2 v3 v4 hpol
      have e1 := r1 a ha; have e2 := r2 a ha; have e1b := r1 b hb; have e2b := r2 b hb
      have n1 := u1.2 b hb (Ne.symm hab); have n3 := u3.2 b hb (Ne.symm hab)
      have n2 := u2.2 a ha hab; have n4 := u4.2 a ha hab
      have s1 := v1.1; have s3 := v3.1; have s2 := v2.1; have s4 := v4.1
      have p1 := u1.1; have p2 := u2.1; have p3 := u3.1; have p4 := u4.1
      revert e1 e2 e1b e2b n1 n2 n3 n4 s1 s2 s3 s4 p1 p2 p3 p4 hpol
      unfold sepb; simp only [op_bit]
      cases d <;> simp <;> grind
    · refine ih hmin.2 hc' ?_ ?_ ?_ ?_ ?_ (tr h1 ha u1) (tr h2 hb u2) (tr h3 ha u3) (tr h4 hb u4)
      · exact phi_mem ha
      · exact phi_mem hb
      · exact phi_ne hg ha hb hab hab'
      · intro w hw; simp at hw
        rcases hw with rfl | hw
        · simp only [op_bit, r1 x (by simp), r1 y (by simp)]
        · exact r1 w (by simp [hw])
      · intro w hw; simp at hw
        rcases hw with rfl | hw
        · simp only [op_bit, r2 x (by simp), r2 y (by simp)]
        · exact r2 w (by simp [hw])
end rect
section chrom
variable {N m T : ℕ}
def Ht (N m T : ℕ) (e : Bool) (S : Finset ℕ) (a b : ℕ) : Prop := ∃ i1 i2 j1 j2, Lg N m T i1 ∧ Lg N m T i2 ∧ Lg N m T j1 ∧ Lg N m T j2 ∧
  (∀ w ∈ S, w.testBit i1 = w.testBit i2) ∧ (∀ w ∈ S, w.testBit (N + j1) = w.testBit (N + j2)) ∧
  Uq N e S a i1 ∧ Uq N e S b i2 ∧ Uq N e S a j1 ∧ Uq N e S b j2 ∧ a.testBit i1 = a.testBit j1 ∧ b.testBit i2 = b.testBit j2
lemma Ht.symm {e : Bool} {S : Finset ℕ} {a b : ℕ} (h : Ht N m T e S a b) : Ht N m T e S b a := by
  obtain ⟨i1, i2, j1, j2, l1, l2, l3, l4, r1, r2, u1, u2, u3, u4, p1, p2⟩ := h
  exact ⟨i2, i1, j2, j1, l2, l1, l4, l3, fun w hw => (r1 w hw).symm, fun w hw => (r2 w hw).symm, u2, u1, u4, u3, p2, p1⟩
lemma bi_uq2 {a b k t c i : ℕ} {d e : Bool} {U : Finset ℕ} (he : e = true ∨ e = pos' t) (hl : Live R m T k t (insert (op d a b) U))
    (hi : Lg N m T i) (hc : c ∈ insert a (insert b U)) (h1 : c = a → a ∉ U) (h2 : c = b → b ∉ U)
    (h : Uq N e (insert a (insert b U)) c i) :
    Uq N e (insert (op d a b) U) (if c = a ∨ c = b then op d a b else c) i := by
  obtain ⟨w, hw, hs⟩ := hl.cov hi.1 hi.2.1 hi.2.2.1 hi.2.2.2
  have hs : sepb N e w i = true := by
    rcases he with rfl | rfl
    · exact sepb_weak _ hs
    · exact hs
  by_cases hcc : c = a ∨ c = b
  · rw [ite_eq_left hcc]
    have hcU : c ∉ U := by
      rcases hcc with rfl | rfl; exacts [h1 rfl, h2 rfl]
    have hU : ∀ x ∈ U, sepb N e x i = false := by
      intro x hx
      refine h.2 x (by simp [hx]) ?_
      rintro rfl; exact hcU hx
    simp at hw
    rcases hw with rfl | hw
    · refine ⟨hs, fun x hx hne => ?_⟩
      simp at hx; exact hU x (hx.resolve_left hne)
    · rw [hU w hw] at hs; simp at hs
  · rw [ite_eq_right hcc]
    push Not at hcc
    refine ⟨h.1, fun x hx hne => ?_⟩
    simp at hx
    rcases hx with rfl | hx
    · have h1 := h.2 a (by simp) (Ne.symm hcc.1)
      have h2 := h.2 b (by simp) (Ne.symm hcc.2)
      revert h1 h2; unfold sepb; simp only [op_bit]
      cases e <;> cases d <;> cases a.testBit i <;> cases a.testBit (N + i) <;> cases b.testBit i <;>
          cases b.testBit (N + i) <;> simp
    · exact h.2 x (by simp [hx]) hne
lemma pol_op {a b i : ℕ} {d e : Bool} (ha : sepb N e a i = true) (hb : sepb N e b i = false) (ho : sepb N e (op d a b) i = true) :
    (op d a b).testBit i = a.testBit i := by
  revert ha hb ho; unfold sepb; simp only [op_bit]
  cases e <;> cases d <;> cases a.testBit i <;> cases a.testBit (N + i) <;> cases b.testBit i <;>
    cases b.testBit (N + i) <;> simp
lemma pol_phi {a b c i : ℕ} {d e : Bool} {U : Finset ℕ} (hab : a ≠ b) (h : Uq N e (insert a (insert b U)) c i)
    (hu : Uq N e (insert (op d a b) U) (if c = a ∨ c = b then op d a b else c) i) :
    (if c = a ∨ c = b then op d a b else c).testBit i = c.testBit i := by
  by_cases hcc : c = a ∨ c = b
  · rw [ite_eq_left hcc] at hu ⊢
    rcases hcc with rfl | rfl
    · exact pol_op h.1 (h.2 b (by simp) (Ne.symm hab)) hu.1
    · rw [op_comm] at hu ⊢
      exact pol_op h.1 (h.2 a (by simp) hab) hu.1
  · rw [ite_eq_right hcc]
lemma ht_bi {a b k t c1 c2 : ℕ} {d e : Bool} {U : Finset ℕ} (hab : a ≠ b) (he : e = true ∨ e = pos' t) (hl : Live R m T k t (insert (op d a b) U))
    (hc1 : c1 ∈ insert a (insert b U)) (hc2 : c2 ∈ insert a (insert b U))
    (h1 : c1 = a → a ∉ U) (h1' : c1 = b → b ∉ U) (h2 : c2 = a → a ∉ U) (h2' : c2 = b → b ∉ U)
    (h : Ht N m T e (insert a (insert b U)) c1 c2) :
    Ht N m T e (insert (op d a b) U) (if c1 = a ∨ c1 = b then op d a b else c1) (if c2 = a ∨ c2 = b then op d a b else c2) := by
  obtain ⟨i1, i2, j1, j2, l1, l2, l3, l4, r1, r2, u1, u2, u3, u4, p1, p2⟩ := h
  have v1 := bi_uq2 he hl l1 hc1 h1 h1' u1
  have v2 := bi_uq2 he hl l2 hc2 h2 h2' u2
  have v3 := bi_uq2 he hl l3 hc1 h1 h1' u3
  have v4 := bi_uq2 he hl l4 hc2 h2 h2' u4
  refine ⟨i1, i2, j1, j2, l1, l2, l3, l4, ?_, ?_, v1, v2, v3, v4, ?_, ?_⟩
  · intro w hw; simp at hw
    rcases hw with rfl | hw
    · simp only [op_bit, r1 a (by simp), r1 b (by simp)]
    · exact r1 w (by simp [hw])
  · intro w hw; simp at hw
    rcases hw with rfl | hw
    · simp only [op_bit, r2 a (by simp), r2 b (by simp)]
    · exact r2 w (by simp [hw])
  · rw [pol_phi hab u1 v1, pol_phi hab u3 v3, p1]
  · rw [pol_phi hab u2 v2, pol_phi hab u4 v4, p2]
lemma ht_merge {a b k t : ℕ} {d e : Bool} {U : Finset ℕ} (hab : a ≠ b) (he : e = true ∨ e = pos' t) (hl : Live R m T k t (insert (op d a b) U))
    (ha : a ∉ U) (hb : b ∉ U) (h : Ht N m T e (insert a (insert b U)) a b) : False := by
  obtain ⟨i1, i2, j1, j2, l1, l2, l3, l4, r1, r2, u1, u2, u3, u4, p1, p2⟩ := h
  have v1 := (bi_uq2 he hl l1 (by simp) (fun _ => ha) (fun _ => hb) u1).1
  have v2 := (bi_uq2 he hl l2 (by simp) (fun _ => ha) (fun _ => hb) u2).1
  have v3 := (bi_uq2 he hl l3 (by simp) (fun _ => ha) (fun _ => hb) u3).1
  have v4 := (bi_uq2 he hl l4 (by simp) (fun _ => ha) (fun _ => hb) u4).1
  simp only [true_or, or_true, if_true] at v1 v2 v3 v4
  have e1 := r1 a (by simp); have e2 := r2 a (by simp); have e1b := r1 b (by simp); have e2b := r2 b (by simp)
  have n1 := u1.2 b (by simp) (Ne.symm hab); have n3 := u3.2 b (by simp) (Ne.symm hab)
  have n2 := u2.2 a (by simp) hab; have n4 := u4.2 a (by simp) hab
  have s1 := u1.1; have s2 := u2.1; have s3 := u3.1; have s4 := u4.1
  revert e1 e2 e1b e2b n1 n2 n3 n4 s1 s2 s3 s4 v1 v2 v3 v4 p1 p2
  unfold sepb; simp only [op_bit]
  cases e <;> cases d <;> simp <;> grind
lemma un_uq2 {a c i : ℕ} {U : Finset ℕ} (hi : Lg N m T i) (h1 : c = a → a ∉ U) (hc : c ∈ insert a U) (h : Uq N true (insert a U) c i) :
    Uq N true (insert (a ^^^ m) U) (if c = a then a ^^^ m else c) i := by
  by_cases hca : c = a
  · exact un_uq hi (h1 hca) hc h
  · rw [ite_eq_right hca]
    have hn : sepb N true (a ^^^ m) i = sepb N true a i := by simp [sepb, hi.1, hi.2.1]
    refine ⟨h.1, fun x hx hne => ?_⟩
    simp at hx
    rcases hx with rfl | hx
    · rw [hn]; exact h.2 a (by simp) (Ne.symm hca)
    · exact h.2 x (by simp [hx]) hne
lemma ht_un {a c1 c2 : ℕ} {U : Finset ℕ} (hc1 : c1 ∈ insert a U) (hc2 : c2 ∈ insert a U) (h1 : c1 = a → a ∉ U) (h2 : c2 = a → a ∉ U)
    (h : Ht N m T true (insert a U) c1 c2) :
    Ht N m T true (insert (a ^^^ m) U) (if c1 = a then a ^^^ m else c1) (if c2 = a then a ^^^ m else c2) := by
  obtain ⟨i1, i2, j1, j2, l1, l2, l3, l4, r1, r2, u1, u2, u3, u4, p1, p2⟩ := h
  have pp : ∀ {c i j : ℕ}, m.testBit i = true → m.testBit j = true → c.testBit i = c.testBit j →
      (if c = a then a ^^^ m else c).testBit i = (if c = a then a ^^^ m else c).testBit j := by
    intro c i j m1 m2 p
    split_ifs with h
    · subst h; simp [m1, m2, p]
    · exact p
  refine ⟨i1, i2, j1, j2, l1, l2, l3, l4, ?_, ?_, un_uq2 l1 h1 hc1 u1, un_uq2 l2 h2 hc2 u2, un_uq2 l3 h1 hc1 u3, un_uq2 l4 h2 hc2 u4,
    pp l1.1 l3.1 p1, pp l2.1 l4.1 p2⟩
  · intro w hw; simp at hw
    rcases hw with rfl | hw
    · simp [r1 a (by simp), l1.1, l2.1]
    · exact r1 w (by simp [hw])
  · intro w hw; simp at hw
    rcases hw with rfl | hw
    · simp [r2 a (by simp), l3.2.1, l4.2.1]
    · exact r2 w (by simp [hw])
lemma chrom {e : Bool} {k t : ℕ} {S : Finset ℕ} (hl : Live R m T k t S) (hm : ∀ q < k, ¬ Sol Z0 m T q (C m (S : Set ℕ)))
    (he : e = true ∨ t = 0) :
    ∃ (x : ℕ) (f : ℕ → ℕ), S.card + t + x = k + 1 ∧ (∀ a ∈ S, f a ≤ x) ∧ ∀ a ∈ S, ∀ b ∈ S, a ≠ b → Ht N m T e S a b → f a ≠ f b := by
  induction hl with
  | stop =>
    refine ⟨0, fun _ => 0, by simp, by simp, ?_⟩
    intro a ha b hb hab; simp at ha hb; exact absurd (ha.trans hb.symm) hab
  | @un k t a U hl ih =>
    have he1 : e = true := he.resolve_right (by omega)
    subst he1
    have hu : Un m a (insert a U) (insert (a ^^^ m) U) := ⟨U, rfl, rfl⟩
    have hf : a ^^^ m ∉ U := fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
    have hmin := hu.min hl hm
    obtain ⟨x, f, hx, hfx, hc⟩ := ih hmin.2 (Or.inl rfl)
    rw [Finset.card_insert_of_notMem hf] at hx
    have sm : ∀ {i1 i2 : ℕ}, m.testBit i1 = true → m.testBit i2 = true → (∀ w ∈ insert a U, w.testBit i1 = w.testBit i2) →
        ∀ w ∈ insert (a ^^^ m) U, w.testBit i1 = w.testBit i2 := by
      intro i1 i2 m1 m2 r w hw
      simp at hw
      rcases hw with rfl | hw
      · simp [r a (by simp), m1, m2]
      · exact r w (by simp [hw])
    by_cases ha : a ∈ U
    · have eS : insert a U = U := Finset.insert_eq_of_mem ha
      refine ⟨x + 1, fun c => if c = a then x + 1 else f c, by rw [eS]; omega, ?_, ?_⟩
      · intro c hcS
        rw [eS] at hcS
        by_cases hca : c = a
        · simp [hca]
        · simp only [hca, if_false]
          have := hfx c (by simp [hcS]); omega
      · intro c1 h1 c2 h2 h12 hh
        rw [eS] at h1 h2
        by_cases q1 : c1 = a
        · have q2 : c2 ≠ a := fun e => h12 (q1.trans e.symm)
          have := hfx c2 (by simp [h2])
          simp only [q1, q2, if_true, if_false]; omega
        · by_cases q2 : c2 = a
          · have := hfx c1 (by simp [h1])
            simp only [q1, q2, if_true, if_false]; omega
          · simp only [q1, q2, if_false]
            refine hc c1 (by simp [h1]) c2 (by simp [h2]) h12 ?_
            obtain ⟨i1, i2, j1, j2, l1, l2, l3, l4, r1, r2, u1, u2, u3, u4, p1, p2⟩ := hh
            have tr : ∀ {c i : ℕ}, c ≠ a → Lg N m T i → Uq N true (insert a U) c i → Uq N true (insert (a ^^^ m) U) c i := by
              intro c i hca hi h
              refine ⟨h.1, fun y hy hne => ?_⟩
              simp at hy
              rcases hy with rfl | hy
              · have hn : sepb N true (a ^^^ m) i = sepb N true a i := by simp [sepb, hi.1, hi.2.1]
                rw [hn]; exact h.2 a (by simp) (Ne.symm hca)
              · exact h.2 y (by simp [hy]) hne
            exact ⟨i1, i2, j1, j2, l1, l2, l3, l4, sm l1.1 l2.1 r1, sm l3.2.1 l4.2.1 r2, tr q1 l1 u1, tr q2 l2 u2, tr q1 l3 u3, tr q2 l4 u4, p1, p2⟩
    · rw [Finset.card_insert_of_notMem ha]
      have mem : ∀ {c : ℕ}, c ∈ insert a U → (if c = a then a ^^^ m else c) ∈ insert (a ^^^ m) U := by
        intro c hcS; split_ifs with h <;> simp at hcS ⊢; tauto
      refine ⟨x, fun c => f (if c = a then a ^^^ m else c), by omega, fun c hcS => hfx _ (mem hcS), ?_⟩
      intro c1 h1 c2 h2 h12 hh
      refine hc _ (mem h1) _ (mem h2) ?_ ?_
      · split_ifs with p q q
        · exact absurd (p.trans q.symm) h12
        · intro e; simp at h2; rw [← e] at h2; rcases h2 with h | h
          · exact q (by rw [← e, h])
          · exact hf h
        · intro e; simp at h1; rw [e] at h1; rcases h1 with h | h
          · exact p (by rw [e, h])
          · exact hf h
        · exact h12
      · obtain ⟨i1, i2, j1, j2, l1, l2, l3, l4, r1, r2, u1, u2, u3, u4, p1, p2⟩ := hh
        have pp : ∀ {c i j : ℕ}, m.testBit i = true → m.testBit j = true → c.testBit i = c.testBit j →
            (if c = a then a ^^^ m else c).testBit i = (if c = a then a ^^^ m else c).testBit j := by
          intro c i j m1 m2 p
          split_ifs with h
          · subst h; simp [m1, m2, p]
          · exact p
        exact ⟨i1, i2, j1, j2, l1, l2, l3, l4, sm l1.1 l2.1 r1, sm l3.2.1 l4.2.1 r2, un_uq l1 ha h1 u1, un_uq l2 ha h2 u2, un_uq l3 ha h1 u3, un_uq l4 ha h2 u4,
          pp l1.1 l3.1 p1, pp l2.1 l4.1 p2⟩
  | @bi k t d a b U hab hal hl ih =>
    have hu : Bi R d a b (insert a (insert b U)) (insert (op d a b) U) := ⟨hab, U, rfl, rfl, hal⟩
    have hfS : op d a b ∉ insert a (insert b U) := fun h => hu.fresh hl hm (sub_C _ _ (by simpa using h))
    have hf : op d a b ∉ U := fun h => hfS (by simp [h])
    have hmin := hu.min hl hm
    have he2 : e = true ∨ e = pos' t := by
      rcases he with h | h
      · exact Or.inl h
      · subst h; cases e <;> simp [pos']
    obtain ⟨x, f, hx, hfx, hc⟩ := ih hmin.2 he
    rw [Finset.card_insert_of_notMem hf] at hx
    have mem : ∀ {c : ℕ}, c ∈ insert a (insert b U) → (if c = a ∨ c = b then op d a b else c) ∈ insert (op d a b) U := fun h => phi_mem h
    by_cases ha : a ∈ U
    · by_cases hb : b ∈ U
      · have eS : insert a (insert b U) = U := by rw [Finset.insert_eq_of_mem hb, Finset.insert_eq_of_mem ha]
        refine ⟨x + 2, fun c => if c = a then x + 2 else if c = b then x + 1 else f c, by rw [eS]; omega, ?_, ?_⟩
        · intro c hcS
          rw [eS] at hcS
          have := hfx c (by simp [hcS])
          dsimp only; split_ifs <;> omega
        · intro c1 h1 c2 h2 h12 hh
          have k1 := h1; have k2 := h2
          rw [eS] at h1 h2
          have f1 := hfx c1 (by simp [h1]); have f2 := hfx c2 (by simp [h2])
          by_cases q1 : c1 = a
          · have q2 : c2 ≠ a := fun e => h12 (q1.trans e.symm)
            simp only [q1, q2, if_true, if_false]; split_ifs <;> omega
          · by_cases q2 : c2 = a
            · simp only [q1, q2, if_true, if_false]; split_ifs <;> omega
            · by_cases q3 : c1 = b
              · have q4 : c2 ≠ b := fun e => h12 (q3.trans e.symm)
                simp only [q1, q2, q3, q4, if_true, if_false]; rw [if_neg (Ne.symm hab)]; omega
              · by_cases q4 : c2 = b
                · simp only [q1, q2, q3, q4, if_true, if_false]; rw [if_neg (Ne.symm hab)]; omega
                · simp only [q1, q2, q3, q4, if_false]
                  have := ht_bi hab he2 hl k1 k2 (fun e => absurd e q1) (fun e => absurd e q3) (fun e => absurd e q2) (fun e => absurd e q4) hh
                  simp only [q1, q2, q3, q4, or_self, if_false] at this
                  exact hc c1 (by simp [h1]) c2 (by simp [h2]) h12 this
      · have eS : insert a (insert b U) = insert b U := Finset.insert_eq_of_mem (by simp [ha])
        refine ⟨x + 1, fun c => if c = a then x + 1 else f (if c = a ∨ c = b then op d a b else c), ?_, ?_, ?_⟩
        · rw [eS, Finset.card_insert_of_notMem hb]; omega
        · intro c hcS
          have := hfx _ (mem hcS)
          dsimp only; by_cases hca : c = a
          · simp [hca]
          · simp only [hca, if_false, false_or] at this ⊢; omega
        · intro c1 h1 c2 h2 h12 hh
          have f1 := hfx _ (mem h1); have f2 := hfx _ (mem h2)
          by_cases q1 : c1 = a
          · have q2 : c2 ≠ a := fun e => h12 (q1.trans e.symm)
            simp only [q1, q2, if_true, if_false, false_or] at f2 ⊢; omega
          · by_cases q2 : c2 = a
            · simp only [q1, q2, if_true, if_false, false_or] at f1 ⊢; omega
            · have := ht_bi hab he2 hl h1 h2 (fun e => absurd e q1) (fun _ => hb) (fun e => absurd e q2) (fun _ => hb) hh
              simp only [q1, q2, if_false, false_or] at this f1 f2 ⊢
              refine hc _ (by simpa [q1] using mem h1) _ (by simpa [q2] using mem h2) ?_ this
              have h1' : c1 = b ∨ c1 ∈ U := by simp at h1; tauto
              have h2' : c2 = b ∨ c2 ∈ U := by simp at h2; tauto
              split_ifs with p q q
              · exact absurd (p.trans q.symm) h12
              · intro e; exact hf (e ▸ h2'.resolve_left q)
              · intro e; exact hf (e ▸ h1'.resolve_left p)
              · exact h12
    · by_cases hb : b ∈ U
      · have eS : insert a (insert b U) = insert a U := by rw [Finset.insert_eq_of_mem hb]
        refine ⟨x + 1, fun c => if c = b then x + 1 else f (if c = a ∨ c = b then op d a b else c), ?_, ?_, ?_⟩
        · rw [eS, Finset.card_insert_of_notMem ha]; omega
        · intro c hcS
          have := hfx _ (mem hcS)
          dsimp only; by_cases hca : c = b
          · simp [hca]
          · simp only [hca, if_false, or_false] at this ⊢; omega
        · intro c1 h1 c2 h2 h12 hh
          have f1 := hfx _ (mem h1); have f2 := hfx _ (mem h2)
          by_cases q1 : c1 = b
          · have q2 : c2 ≠ b := fun e => h12 (q1.trans e.symm)
            simp only [q1, q2, if_true, if_false, or_false] at f2 ⊢; omega
          · by_cases q2 : c2 = b
            · simp only [q1, q2, if_true, if_false, or_false] at f1 ⊢; omega
            · have := ht_bi hab he2 hl h1 h2 (fun _ => ha) (fun e => absurd e q1) (fun _ => ha) (fun e => absurd e q2) hh
              simp only [q1, q2, if_false, or_false] at this f1 f2 ⊢
              refine hc _ (by simpa [q1] using mem h1) _ (by simpa [q2] using mem h2) ?_ this
              have h1' : c1 = a ∨ c1 ∈ U := by simp at h1; tauto
              have h2' : c2 = a ∨ c2 ∈ U := by simp at h2; tauto
              split_ifs with p q q
              · exact absurd (p.trans q.symm) h12
              · intro e; exact hf (e ▸ h2'.resolve_left q)
              · intro e; exact hf (e ▸ h1'.resolve_left p)
              · exact h12
      · refine ⟨x, fun c => f (if c = a ∨ c = b then op d a b else c), ?_, fun c hcS => hfx _ (mem hcS), ?_⟩
        · rw [Finset.card_insert_of_notMem (by simp [hab, ha]), Finset.card_insert_of_notMem hb]; omega
        · intro c1 h1 c2 h2 h12 hh
          by_cases hab' : (c1 = a ∨ c1 = b) ∧ (c2 = a ∨ c2 = b)
          · exfalso
            have : Ht N m T e (insert a (insert b U)) a b := by
              rcases hab' with ⟨rfl | rfl, rfl | rfl⟩
              · exact absurd rfl h12
              · exact hh
              · exact hh.symm
              · exact absurd rfl h12
            exact ht_merge hab he2 hl ha hb this
          · exact hc _ (mem h1) _ (mem h2) (phi_ne hf h1 h2 h12 hab')
              (ht_bi hab he2 hl h1 h2 (fun _ => ha) (fun _ => hb) (fun _ => ha) (fun _ => hb) hh)
end chrom
structure W where
  s : Nat
  a : Nat
  b : Nat
  c : Nat
  r : Nat
structure XW where
  w : W
  s : Nat
  q : Nat
  u : Nat
structure Cm where
  a : List Nat
  b : List Nat

structure Inst where
  NN : Nat
  AA : Nat
  HX : Nat
  HY : Nat
  segsX : List (ℕ × ℕ)
  segsY : List (ℕ × ℕ)
  rawP : List ℕ
  TG : ℕ

def segOk (AA : ℕ) (s : ℕ × ℕ) : Bool := decide (s.1 < s.2) && decide (AA % 2 ^ s.2 + 2 ^ (s.1 + 1) = 2 ^ s.2 + AA % 2 ^ s.1) &&
  !AA.testBit s.1 && !AA.testBit s.2
def bitsOf (L : List (ℕ × ℕ)) : ℕ := L.foldr (fun s x => 2 ^ s.2 ||| x) 0
def segGood (w o : ℕ) (s : ℕ × ℕ) : Bool :=
  Nat.beq ((w >>> (o + s.1 + 1)) % 2 ^ (s.2 - s.1 - 1)) 0 || Nat.beq ((w >>> (o + s.1 + 1)) % 2 ^ (s.2 - s.1 - 1)) (2 ^ (s.2 - s.1 - 1) - 1)

structure InstOk (I : Inst) : Prop where
  segX_ok : I.segsX.all (segOk I.AA) = true
  segY_ok : I.segsY.all (segOk I.AA) = true
  HX_eq : I.HX = bitsOf I.segsX
  HY_eq : I.HY = bitsOf I.segsY
  AA_TG : I.AA &&& I.TG = I.AA
  TG_lt : I.TG < 2 ^ I.NN
  AA_lt : I.AA < 2 ^ I.NN
  raw_good : I.rawP.all (fun w => I.segsX.all (segGood w 0) && I.segsY.all (segGood w I.NN)) = true
  rawP_len : I.rawP.length = 6


noncomputable section coreC
def st (n : Nat) (f : Nat → Bool) : Bool := Nat.rec (motive := fun _ => Bool) (f 0) (fun m _ => f m) (Nat.succ n)
def spC (NN : Nat) (d : Bool) (l s : Nat) : Nat :=
  Nat.land (Nat.xor s (Nat.land (Nat.shiftRight s NN) l)) (Bool.rec (motive := fun _ => Nat) (Nat.land s l) l d)
def covC (NN : Nat) (d : Bool) (l : Nat) (v : List W) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun w _ ih => Nat.lor (spC NN d l w.s) ih) v
def twiceC (NN : Nat) (d : Bool) (l : Nat) (v : List W) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun w t ih => Nat.lor (Nat.land (spC NN d l w.s) (covC NN d l t)) ih) v
def hitC (HX HY : Nat) (f e : Nat) : Bool := (Bool.rec (motive := fun _ => Bool) ((Bool.rec (motive := fun _ => Bool) (true) (false) (Nat.beq (Nat.land (Nat.land f e) HY) 0))) (false) (Nat.beq (Nat.land (Nat.land f e) HX) 0))
def hitsC (HX HY : Nat) (f : Nat) (m : List Nat) : Bool := (List.rec (motive := fun _ => Bool) (false) (fun e _ ih => (Bool.rec (motive := fun _ => Bool) (ih) (true) (hitC HX HY f e))) (m))
def flagC (NN AA : Nat) (d : Bool) (l o : Nat) (w : W) : Nat := Nat.add (Nat.land (spC NN d l w.s) o) AA
def rectC (NN AA HX HY : Nat) (d : Bool) (l o : Nat) (v : List W) : List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun _ => false)
    (fun w _ ih m => (Bool.rec (motive := fun _ => Bool) (ih (flagC NN AA d l o w :: m)) (true) (hitsC HX HY (flagC NN AA d l o w) m))) v
def app (x y : List Nat) : List Nat := List.rec (motive := fun _ => List Nat) y (fun e _ ih => e :: ih) x
def joinC (HX HY : Nat) (k : List Cm → Bool) (f : Nat) (cs : List Cm) : List Nat → List Nat → List Cm → Bool :=
  List.rec (motive := fun _ => List Nat → List Nat → List Cm → Bool) (fun S O R => k (⟨S, O⟩ :: R))
    (fun c _ ih S O R => Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) (ih S O (c :: R)) (ih (app c.a S) (app c.b O) R) (hitsC HX HY f c.b))
      (Bool.rec (motive := fun _ => Bool) (ih (app c.b S) (app c.a O) R) true (hitsC HX HY f c.b)) (hitsC HX HY f c.a)) cs
def bipC (NN AA HX HY : Nat) (l o : Nat) (v : List W) : List Cm → Bool :=
  List.rec (motive := fun _ => List Cm → Bool) (fun _ => false)
    (fun w _ ih cs => (fun f => joinC HX HY ih f cs [f] [] []) (flagC NN AA false l o w)) v
def anyEC (HX HY : Nat) (m : List Nat) : Bool := List.rec (motive := fun _ => Bool) false (fun f t ih => Bool.rec (motive := fun _ => Bool) ih true (hitsC HX HY f t)) m
def rmFC (HX HY : Nat) (f : Nat) (m : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun e t ih => Bool.rec (motive := fun _ => List Nat) (e :: ih) t (hitC HX HY f e)) m
def starC (HX HY : Nat) (m : List Nat) : Bool := List.rec (motive := fun _ => Bool) true (fun f t ih => Bool.rec (motive := fun _ => Bool) ih
  (Bool.rec (motive := fun _ => Bool) true (Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) true false (anyEC HX HY (rmFC HX HY f t))) false (hitsC HX HY f (rmFC HX HY f t))) (anyEC HX HY t)) (hitsC HX HY f t)) m
def flkC (NN AA : Nat) (l o : Nat) (v : List W) : (List Nat → Bool) → Bool :=
  List.rec (motive := fun _ => (List Nat → Bool) → Bool) (fun k => k []) (fun w _ ih k => (fun f => ih (fun r => k (f :: r))) (flagC NN AA false l o w)) v
def mkXC (NN : Nat) (d : Bool) (l o : Nat) (v : List W) : List XW :=
  List.rec (motive := fun _ => List XW) [] (fun w _ ih => ⟨w, w.s, Nat.shiftRight w.s NN, Nat.land (spC NN d l w.s) o⟩ :: ih) v
def rm (x y : Nat) (v : List W) : (List W → Bool) → Bool :=
  List.rec (motive := fun _ => (List W → Bool) → Bool) (fun h => h []) (fun w _ ih h => Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) (ih (fun r => h (w :: r))) (ih h) (Nat.beq w.s y)) (ih h) (Nat.beq w.s x)) v
def ins (o : W) (v : List W) : (List W → Bool) → Bool :=
  List.rec (motive := fun _ => (List W → Bool) → Bool) (fun h => h [o]) (fun w t ih h => Bool.rec (motive := fun _ => Bool) (ih (fun r => h (w :: r))) (Bool.rec (motive := fun _ => Bool) (h (o :: w :: t)) false (Nat.beq o.s w.s)) (Nat.ble w.s o.s)) v
def child (f : Nat → List W → Bool) (g : Nat) (mk : (List W → Bool) → Bool) (z : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (st z (fun z => mk (f z))) (Nat.beq (Nat.land z g) g)
def put (m s x y : Nat) (v : List W) (h : List W → Bool) : Bool :=
  (st (s) (fun s => (Bool.rec (motive := fun _ => Bool) ((Bool.rec (motive := fun _ => Bool) ((st (x) (fun x1 => (st (y) (fun y1 => (st (Nat.lor x y) (fun w => ins ⟨s, x1, y1, w, 0⟩ v h))))))) (false) (Nat.beq s m))) (false) (Nat.beq s 0))))
def kids (c : ((List W → Bool) → Bool) → Nat → Bool) (e n z x y a c' : Nat) (oa oc : Bool) (mk : (List W → Bool) → Bool) : Bool :=
  (Bool.rec (motive := fun _ => Bool) ((Bool.rec (motive := fun _ => Bool) ((Bool.rec (motive := fun _ => Bool) (false) (c mk (Nat.sub (Nat.sub z x) y)) (Nat.ble (Nat.succ (Nat.succ n)) e))) (true) ((Bool.rec (motive := fun _ => Bool) (false) ((Bool.rec (motive := fun _ => Bool) ((Bool.rec (motive := fun _ => Bool) (false) (c (fun h => mk (fun r => rm a a r h)) (Nat.sub z y)) (oa))) (true) ((Bool.rec (motive := fun _ => Bool) (false) (c (fun h => mk (fun r => rm c' c' r h)) (Nat.sub z x)) (oc))))) (Nat.ble (Nat.succ n) e))))) (true) ((Bool.rec (motive := fun _ => Bool) (false) ((Bool.rec (motive := fun _ => Bool) (false) (c (fun h => mk (fun r => rm a c' r h)) z) (oc))) (oa))))
def mid (f : Nat → List W → Bool) (m g e n z : Nat) (v : List W) (a c : W) (da dc s x y : Nat) : Bool :=
  (Bool.rec (motive := fun _ => Bool) (false) ((st (Nat.sub (Nat.add z (Nat.land a.c c.c)) (Nat.lor x y)) (fun z => kids (child f g) e n z a.c c.c a.s c.s (Nat.beq da 0) (Nat.beq dc 0) (put m s x y v)))) (Nat.beq (Nat.land (Nat.sub (Nat.add z (Nat.land a.c c.c)) (Nat.lor x y)) g) g))
def f0 (h : W → W → Nat → Nat → Nat → Nat → Nat → Bool) (a c : W) (da dc s x y : Nat) : Bool :=
  (Bool.rec (motive := fun _ => Bool) (false) (h a c da dc s x y) (Nat.beq (Nat.lor da dc) 0))
def f1 (h : W → W → Nat → Nat → Nat → Nat → Nat → Bool) (a c : W) (da dc s x y : Nat) : Bool :=
  (Bool.rec (motive := fun _ => Bool) (false) (h a c da dc s x y) (Nat.beq (Nat.mul da dc) 0))
def f2 (h : W → W → Nat → Nat → Nat → Nat → Nat → Bool) (a c : W) (da dc s x y : Nat) : Bool := h a c da dc s x y
def pair (h : W → W → Nat → Nat → Nat → Nat → Nat → Bool) (a c : XW) : Bool :=
  XW.rec (motive := fun _ => Bool) (fun a s q u => XW.rec (motive := fun _ => Bool) (fun c s' q' u' => (Bool.rec (motive := fun _ => Bool) (h a c (Nat.land u q') (Nat.land u' q) (Nat.lor s s') (Nat.land a.a c.a) (Nat.lor a.b c.b)) (true) (h a c (Nat.xor (Nat.land u s') u) (Nat.xor (Nat.land u' s) u') (Nat.land s s') (Nat.lor a.a c.a) (Nat.land a.b c.b)))) c) a
def scan (p : XW → Bool) (xs : List XW) : Bool := (List.rec (motive := fun _ => Bool) (false) (fun c _ jh => (Bool.rec (motive := fun _ => Bool) (jh) (true) (p c))) (xs))
def pairs (h : XW → XW → Bool) (xs : List XW) : Bool :=
  (List.rec (motive := fun _ => Bool) (false) (fun a r ih => (Bool.rec (motive := fun _ => Bool) (ih) (true) (scan (h a) r))) (xs))
def pairsP (q : Nat) (h : XW → XW → Bool) (xs : List XW) : Bool :=
  scan (fun a => (Bool.rec (motive := fun _ => Bool) (false) (scan (fun c => (Bool.rec (motive := fun _ => Bool) (h a c) (false) (Nat.beq c.s q))) xs) (Nat.beq a.s q))) xs
def pairsQ (q q' : Nat) (h : XW → XW → Bool) (xs : List XW) : Bool :=
  scan (fun a => (Bool.rec (motive := fun _ => Bool) (false) (scan (fun c => (Bool.rec (motive := fun _ => Bool) (false) (h a c) (Nat.beq c.s q'))) xs) (Nat.beq a.s q))) xs
def fr (xs : List XW) : List XW := List.rec (motive := fun _ => List XW) [] (fun a _ ih => Bool.rec (motive := fun _ => List XW) ih (a :: ih) (Nat.beq a.w.r 0)) xs
def fs (xs : List XW) : List XW := List.rec (motive := fun _ => List XW) [] (fun a _ ih => Bool.rec (motive := fun _ => List XW) (a :: ih) ih (Nat.beq a.w.r 0)) xs
def pairsN (h : XW → XW → Bool) (xs : List XW) : Bool :=
  Bool.rec (motive := fun _ => Bool) (scan (fun a => scan (h a) (fs xs)) (fr xs)) true (pairs h (fr xs))
def pairsS (h : XW → XW → Bool) (xs : List XW) : Bool := pairs h (fs xs)
def nots (f : Nat → Nat → List W → Bool) (m g e n z q : Nat) (v r : List W) : Bool :=
  (List.rec (motive := fun _ => Bool) (false) (fun a _ ih => (Bool.rec (motive := fun _ => Bool) (ih) (true) ((Bool.rec (motive := fun _ => Bool) ((st (Nat.xor a.s m) (fun s => (st (Nat.sub z a.c) (fun z => ins ⟨s, a.b, a.a, a.c, 0⟩ v (fun v => (Bool.rec (motive := fun _ => Bool) ((Bool.rec (motive := fun _ => Bool) (false) (child (f s) g (fun h => h v) (Nat.sub z a.c)) (Nat.ble (Nat.succ n) e))) (true) ((Bool.rec (motive := fun _ => Bool) (false) (child (f s) g (rm a.s a.s v) z) (Nat.ble n e)))))))))) (false) (Nat.beq (Nat.succ a.s) q))))) (r))
def pos (t : Nat) : Bool := Nat.rec (motive := fun _ => Bool) false (fun _ _ => true) t
def wstC (NN : Nat) (d : Bool) (l : Nat) (v : List W) : Nat := Nat.xor l (twiceC NN d l v)
def nodeC (NN : Nat) (f : Nat → List W → Bool) (d : Bool) (l m g e n z : Nat) (v : List W) (go : (XW → XW → Bool) → List XW → Bool) : Bool :=
  (fun h => (fun xs => Bool.rec (motive := fun _ => Bool) (go (pair (f0 h)) xs)
    (Bool.rec (motive := fun _ => Bool) (go (pair (f1 h)) xs) (go (pair (f2 h)) xs) (Nat.ble (Nat.succ n) e)) (Nat.ble n e))
    (mkXC NN d l (wstC NN d l v) v))
  (mid f m g e (Nat.pred n) z v)
def prd (t : Nat) (h : Nat → Bool) : Bool := Nat.rec (motive := fun _ => Bool) false (fun s _ => h s) t
def cvC (NN : Nat) (d : Bool) (l : Nat) (v : List W) (b : Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false b (Nat.beq (covC NN d l v) l)) b d
def tstC (NN AA HX HY : Nat) (d : Bool) (l e : Nat) (v : List W) (F : Nat → Bool) : Bool :=
  (fun n => Bool.rec (motive := fun _ => Bool)
    (Bool.rec (motive := fun _ => Bool) (F 0) (Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) (F 1) (F 0) (flkC NN AA l (wstC NN d l v) v (starC HX HY))) false (bipC NN AA HX HY l (wstC NN d l v) v []))
      (Nat.beq (Nat.succ n) e))
    (Bool.rec (motive := fun _ => Bool) (F 0) false (rectC NN AA HX HY d l (wstC NN d l v) v [])) (Nat.beq n e)) v.length
def mvC (NN AA HX HY : Nat) (F : Nat → Nat → Nat → List W → Bool) (l m g k t z : Nat) (v : List W) (y : Nat) : Bool :=
  (fun n => Bool.rec (motive := fun _ => Bool) (prd t (fun s => nots (fun q z v => cvC NN (pos s) l v (tstC NN AA HX HY (pos s) l (Nat.sub k s) v (fun y =>
      Bool.rec (motive := fun _ => Bool) (prd s (fun s => nots (fun q' z v => cvC NN (pos s) l v (tstC NN AA HX HY (pos s) l (Nat.sub (Nat.sub k 1) s) v (fun y =>
          nodeC NN (F (Nat.sub k 3) s) (pos s) l m g (Nat.sub (Nat.sub (Nat.sub k 2) s) y) v.length z v (pairsQ q q'))))
          m g (Nat.sub (Nat.sub (Nat.sub k 1) s) y) v.length z (Nat.succ q) v v)) true
        (nodeC NN (F (Nat.sub k 2) s) (pos s) l m g (Nat.sub (Nat.sub (Nat.sub k 1) s) y) v.length z v (pairsP q)))))
      m g (Nat.sub (Nat.sub k s) y) n z 0 v v)) true
    (nodeC NN (F (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) n z v pairsN)) v.length
def lookC (NN AA HX HY : Nat) (l m g : Nat) (fuel : Nat) : Nat → Nat → Nat → List W → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → List W → Bool) (fun _ _ _ _ => true)
    (fun _ ih k t z v => Bool.rec (motive := fun _ => Bool) (tstC NN AA HX HY (pos t) l (Nat.sub (Nat.succ k) t) v (fun y => mvC NN AA HX HY ih l m g k t z v y)) true (Nat.ble v.length 1)) fuel
def look1C (NN AA HX HY : Nat) (l m g K : Nat) (fuel : Nat) : Nat → Nat → Nat → List W → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → List W → Bool) (fun _ _ _ _ => true)
    (fun _ ih k t z v => Bool.rec (motive := fun _ => Bool) (tstC NN AA HX HY (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
      Bool.rec (motive := fun _ => Bool) (mvC NN AA HX HY (lookC NN AA HX HY l m g K) l m g k t z v y) true
        (nodeC NN (ih (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) v.length z v pairsS))) true (Nat.ble v.length 1)) fuel
end coreC

def bigNat_0 : Nat := ([0, 18441114494449971199, 13546735319465851821, 18068421321073622749, 12681395204788320991, 2250545674843903] : List Nat).foldr (fun x a => x + 18446744073709551616 * a) 0
def bigNat_1 : Nat := ([0, 5629579259580416, 4900008754243699794, 22020386] : List Nat).foldr (fun x a => x + 18446744073709551616 * a) 0
def bigNat_2 : Nat := ([0, 0, 0, 378322752613908480, 5765348868921230624, 2253053952526592] : List Nat).foldr (fun x a => x + 18446744073709551616 * a) 0
def bigNat_3 : Nat := ([12297829382473034410, 18439988731982082047, 13258645680802494509, 13442934226108285121, 11668083973276817606, 693004704395837, 2494994193563254784, 19198058348814946, 4902599546693493291, 10088067554888122385, 7516193791, 2047] : List Nat).foldr (fun x a => x + 18446744073709551616 * a) 0
def bigNat_4 : Nat := ([14757395258967641292, 3377566844936192, 4323323701165554572, 8121481554142690844, 1069681015657296411, 1597125839119595, 6845471433603153920, 1786707045623291814, 9278140775125812701, 11673198296087658543, 1150950922138878975, 4190208] : List Nat).foldr (fun x a => x + 18446744073709551616 * a) 0
def bigNat_5 : Nat := ([17361641481138401520, 3377619726790655, 9511496860259320736, 7643080346361135133, 9697667896650000969, 1840690998040130, 9889904781705609216, 3031212968811727108, 9317988457543452804, 144009638449252996, 6917810296862021632, 549244108800] : List Nat).foldr (fun x a => x + 18446744073709551616 * a) 0
def bigNat_6 : Nat := ([18374966859414961920, 18437736880628760576, 288138016101237677, 12878817335954112192, 3109755040310333597, 2204256310830837, 10772610308670226432, 4220660260489565632, 14411561356322408726, 144022820509190858, 8068761682857377792, 549420269568] : List Nat).foldr (fun x a => x + 18446744073709551616 * a) 0
def bigNat_7 : Nat := ([18446462603027742720, 18441114488275992576, 13258597302978741165, 13844918480269213405, 878203730245313233, 1997656070602886, 16573246628723425280, 3665068877903095296, 980580479602265624, 12393906174523607795, 469720063, 549449627647] : List Nat).foldr (fun x a => x + 18446744073709551616 * a) 0
def bigNat_8 : Nat := ([18446744069414584320, 0, 13546735319465850880, 16888781545144029, 3441133003059626014, 2217560074290936, 17870283321406128128, 8725990566066176, 998461023428112352, 2812, 8069042975902007296, 549449627647] : List Nat).foldr (fun x a => x + 18446744073709551616 * a) 0
def bigNat_9 : Nat := ([] : List Nat).foldr (fun x a => x + 18446744073709551616 * a) 0
def bigNat_10 : Nat := ([] : List Nat).foldr (fun x a => x + 18446744073709551616 * a) 0
def bigNat_11 : Nat := ([17215267586839718048, 18441114494449971199, 13546735319465851821, 18068421321073622749, 12681395204788320991, 2250545674843903] : List Nat).foldr (fun x a => x + 18446744073709551616 * a) 0
def NN0 : Nat := 372
def AA0 : Nat := bigNat_0
def HX0 : Nat := bigNat_1
def HY0 : Nat := bigNat_2
def segsX0 : List (ℕ × ℕ) := [(63, 76), (76, 79), (79, 92), (92, 95), (95, 97), (97, 100), (100, 114), (114, 116), (116, 129), (129, 132), (132, 134), (134, 138), (138, 152), (152, 155), (155, 157), (157, 170), (170, 172), (172, 174), (174, 186), (186, 190), (190, 193), (193, 197), (197, 200), (200, 212), (212, 214), (214, 216)]
def segsY0 : List (ℕ × ℕ) := [(216, 225), (225, 227), (227, 231), (231, 233), (233, 236), (236, 246), (246, 248), (248, 250), (250, 261), (261, 264), (264, 266), (266, 278), (278, 281), (281, 283), (283, 294), (294, 297), (297, 301), (301, 303), (303, 305), (305, 316), (316, 318), (318, 328), (328, 331), (331, 343), (343, 354), (354, 357), (357, 360), (360, 371)]
def rawP0 : List ℕ := [bigNat_3, bigNat_4, bigNat_5, bigNat_6, bigNat_7, bigNat_8]
def TG0 : ℕ := bigNat_11
def I : Inst := ⟨NN0, AA0, HX0, HY0, segsX0, segsY0, rawP0, TG0⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma segX_ok0 : segsX0.all (segOk AA0) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma segY_ok0 : segsY0.all (segOk AA0) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma HX_eq0 : HX0 = bitsOf segsX0 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma HY_eq0 : HY0 = bitsOf segsY0 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma AA_TG0 : AA0 &&& TG0 = AA0 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma TG_lt0 : TG0 < 2 ^ NN0 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma AA_lt0 : AA0 < 2 ^ NN0 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma raw_good0 : rawP0.all (fun w => segsX0.all (segGood w 0) && segsY0.all (segGood w NN0)) = true := by decide +kernel
lemma IOk : InstOk I := ⟨segX_ok0, segY_ok0, HX_eq0, HY_eq0, AA_TG0, TG_lt0, AA_lt0, raw_good0, rfl⟩

section engine

noncomputable section core
abbrev sp := spC I.NN
abbrev cov := covC I.NN
abbrev twice := twiceC I.NN
abbrev hit := hitC I.HX I.HY
abbrev hits := hitsC I.HX I.HY
abbrev flag := flagC I.NN I.AA
abbrev rect := rectC I.NN I.AA I.HX I.HY
abbrev join := joinC I.HX I.HY
abbrev bip := bipC I.NN I.AA I.HX I.HY
abbrev anyE := anyEC I.HX I.HY
abbrev rmF := rmFC I.HX I.HY
abbrev star := starC I.HX I.HY
abbrev flk := flkC I.NN I.AA
abbrev mkX := mkXC I.NN
abbrev wst := wstC I.NN
abbrev node := nodeC I.NN
abbrev cv := cvC I.NN
abbrev tst := tstC I.NN I.AA I.HX I.HY
abbrev mv := mvC I.NN I.AA I.HX I.HY
abbrev look := lookC I.NN I.AA I.HX I.HY
abbrev look1 := look1C I.NN I.AA I.HX I.HY
end core

lemma bR (c e t : Bool) : (Bool.rec (motive := fun _ => Bool) e t c : Bool) = bif c then t else e := by cases c <;> rfl
lemma st_eq (n : ℕ) (f : ℕ → Bool) : st n f = f n := by cases n <;> rfl
lemma nl (a b : ℕ) : Nat.land a b = a &&& b := rfl
lemma no (a b : ℕ) : Nat.lor a b = a ||| b := rfl
lemma nx (a b : ℕ) : Nat.xor a b = a ^^^ b := rfl
lemma nsr (a b : ℕ) : Nat.shiftRight a b = a >>> b := rfl
lemma sp_bit (d : Bool) (l s i : ℕ) : (sp d l s).testBit i = (l.testBit i && sepb I.NN d s i) := by
  cases d <;> simp [sp, spC, sepb, nl, nx, nsr, Nat.testBit_shiftRight] <;>
    cases l.testBit i <;> cases s.testBit i <;> cases s.testBit (I.NN + i) <;> rfl
lemma cov_bit (d : Bool) (l i : ℕ) (v : List W) : (cov d l v).testBit i = true ↔ ∃ w ∈ v, (sp d l w.s).testBit i = true := by
  induction v with
  | nil => simp [cov, covC]
  | cons w v ih =>
    change (Nat.lor (sp d l w.s) (cov d l v)).testBit i = true ↔ _
    simp [no, ih]
lemma twice_bit (d : Bool) (l i : ℕ) (v : List W) (h : (twice d l v).testBit i = false) :
    v.Pairwise (fun w w' => ¬ ((sp d l w.s).testBit i = true ∧ (sp d l w'.s).testBit i = true)) := by
  induction v with
  | nil => simp
  | cons w v ih =>
    change (Nat.lor (Nat.land (sp d l w.s) (cov d l v)) (twice d l v)).testBit i = false at h
    simp only [no, nl, Nat.testBit_or, Nat.testBit_and, Bool.or_eq_false_iff] at h
    refine List.pairwise_cons.2 ⟨fun w' hw' ⟨h1, h2⟩ => ?_, ih h.2⟩
    have := (cov_bit d l i v).2 ⟨w', hw', h2⟩
    simp [h1, this] at h
def Rep (v : List W) (S : Finset ℕ) : Prop := (v.map W.s).Nodup ∧ (v.map W.s).toFinset = S
lemma Rep.mem {v : List W} {S : Finset ℕ} (h : Rep v S) {x : ℕ} : x ∈ S ↔ ∃ w ∈ v, w.s = x := by
  rw [← h.2]; simp
lemma Rep.inj {v : List W} {S : Finset ℕ} (h : Rep v S) {w w' : W} (hw : w ∈ v) (hw' : w' ∈ v) (e : w.s = w'.s) : w = w' :=
  List.inj_on_of_nodup_map h.1 hw hw' e
lemma Rep.card {v : List W} {S : Finset ℕ} (h : Rep v S) : S.card = v.length := by
  rw [← h.2, List.toFinset_card_of_nodup h.1, List.length_map]
lemma uq_of {d : Bool} {l i : ℕ} {v : List W} {S : Finset ℕ} (h : Rep v S) {w : W} (hw : w ∈ v)
    (hu : (Nat.land (sp d l w.s) (wst d l v)).testBit i = true) : l.testBit i = true ∧ Uq I.NN d S w.s i := by
  simp only [nl, wst, wstC, nx, Nat.testBit_and, Nat.testBit_xor, Bool.and_eq_true, sp_bit] at hu
  obtain ⟨⟨hl, hs⟩, ht⟩ := hu
  have ht : (twice d l v).testBit i = false := by simpa [hl] using ht
  refine ⟨hl, hs, fun c hc hne => ?_⟩
  obtain ⟨w', hw', rfl⟩ := h.mem.1 hc
  have hp := twice_bit d l i v ht
  haveI : Std.Symm (fun w w' : W => ¬ ((sp d l w.s).testBit i = true ∧ (sp d l w'.s).testBit i = true)) :=
    ⟨fun a b h h' => h h'.symm⟩
  have := hp.forall hw hw' (fun e => hne (by rw [e]))
  simp only [sp_bit, hl, hs, Bool.true_and, true_and] at this
  simpa using this

section engine_ok
lemma bitsOf_bit {L : List (ℕ × ℕ)} {h : ℕ} (hh : (bitsOf L).testBit h = true) : ∃ s ∈ L, s.2 = h := by
  induction L with
  | nil => simp [bitsOf] at hh
  | cons s L ih =>
    change (2 ^ s.2 ||| bitsOf L).testBit h = true at hh
    rw [Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true] at hh
    rcases hh with hh | hh
    · exact ⟨s, by simp, by simpa using hh⟩
    · obtain ⟨s', hs', e⟩ := ih hh; exact ⟨s', by simp [hs'], e⟩
lemma carry {u A p h : ℕ} (hp : p < h) (hA : A % 2 ^ h + 2 ^ (p + 1) = 2 ^ h + A % 2 ^ p) (hAh : A.testBit h = false)
    (huh : u.testBit h = false) (hup : u.testBit p = false) (hs : (u + A).testBit h = true) :
    ∃ i, p < i ∧ i < h ∧ u.testBit i = true := by
  by_contra hno
  push Not at hno
  have e1 : u % 2 ^ h = u % 2 ^ p := by
    apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_mod_two_pow]
    by_cases h1 : i < p
    · simp [h1, show i < h by omega]
    · by_cases h2 : i < h
      · rcases Nat.lt_or_ge p i with h3 | h3
        · simp [h1, hno i h3 h2]
        · obtain rfl : i = p := by omega
          simp [hup]
      · simp [h1, h2]
  have l1 := Nat.mod_lt u (Nat.two_pow_pos p)
  have l2 := Nat.mod_lt A (Nat.two_pow_pos p)
  have hlt : u % 2 ^ h + A % 2 ^ h < 2 ^ h := by rw [e1]; have := Nat.pow_succ 2 p; omega
  have e2 : (u + A).testBit h = (u / 2 ^ h + A / 2 ^ h).testBit 0 := by
    have : u + A = 2 ^ h * (u / 2 ^ h + A / 2 ^ h) + (u % 2 ^ h + A % 2 ^ h) := by
      have a1 := Nat.div_add_mod u (2 ^ h); have a2 := Nat.div_add_mod A (2 ^ h)
      rw [Nat.mul_add]; omega
    rw [this, Nat.testBit_two_pow_mul_add _ hlt]; simp
  have b1 : (u / 2 ^ h).testBit 0 = false := by rw [← huh, Nat.testBit_div_two_pow]; simp
  have b2 : (A / 2 ^ h).testBit 0 = false := by rw [← hAh, Nat.testBit_div_two_pow]; simp
  rw [e2] at hs
  simp [Nat.testBit_zero] at hs b1 b2
  omega
def Same (L : List (ℕ × ℕ)) (i j : ℕ) : Prop := ∃ s ∈ L, s.1 < i ∧ i < s.2 ∧ s.1 < j ∧ j < s.2
def Good (l s : ℕ) : Prop := (∀ i j, Same I.segsX i j → l.testBit i = true → l.testBit j = true → s.testBit i = s.testBit j) ∧
  (∀ i j, Same I.segsY i j → l.testBit i = true → l.testBit j = true → s.testBit (I.NN + i) = s.testBit (I.NN + j))
lemma flag_seg {L : List (ℕ × ℕ)} (hL : L.all (segOk I.AA) = true) {u : ℕ} (hu : ∀ i, u.testBit i = true → I.AA.testBit i = true)
    {s : ℕ × ℕ} (hs : s ∈ L) (hb : (u + I.AA).testBit s.2 = true) : ∃ i, s.1 < i ∧ i < s.2 ∧ u.testBit i = true := by
  have h := List.all_eq_true.1 hL s hs
  simp only [segOk, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  refine carry h.1.1.1 h.1.1.2 h.2 ?_ ?_ hb
  · by_contra hc; have := hu _ (by simpa using hc); rw [h.2] at this; simp at this
  · by_contra hc; have := hu _ (by simpa using hc); rw [h.1.2] at this; simp at this
lemma hit_spec {f e : ℕ} (h : hit f e = true) :
    (∃ s ∈ I.segsX, f.testBit s.2 = true ∧ e.testBit s.2 = true) ∧ (∃ s ∈ I.segsY, f.testBit s.2 = true ∧ e.testBit s.2 = true) := by
  have aux : ∀ H, Nat.beq (Nat.land (Nat.land f e) H) 0 = false → ∃ i, f.testBit i = true ∧ e.testBit i = true ∧ H.testBit i = true := by
    intro H hH
    have hne : (f &&& e &&& H) ≠ 0 := fun h0 => by rw [nl, nl, h0] at hH; simp at hH
    obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero hne
    simp at hi; exact ⟨i, hi.1.1, hi.1.2, hi.2⟩
  simp only [hit, hitC, bR] at h
  cases h1 : Nat.beq (Nat.land (Nat.land f e) I.HX) 0 with
  | true => rw [h1] at h; simp only [cond_true, Bool.false_eq_true] at h
  | false =>
    cases h2 : Nat.beq (Nat.land (Nat.land f e) I.HY) 0 with
    | true => rw [h1, h2] at h; simp only [cond_true, cond_false, Bool.false_eq_true] at h
    | false =>
      obtain ⟨i, a1, a2, a3⟩ := aux _ h1
      obtain ⟨j, b1, b2, b3⟩ := aux _ h2
      rw [IOk.HX_eq] at a3; rw [IOk.HY_eq] at b3
      obtain ⟨s, hs, rfl⟩ := bitsOf_bit a3
      obtain ⟨s', hs', rfl⟩ := bitsOf_bit b3
      exact ⟨⟨s, hs, a1, a2⟩, ⟨s', hs', b1, b2⟩⟩
lemma hits_false {f : ℕ} {m : List ℕ} (h : ∀ e ∈ m, hit f e = false) : hits f m = false := by
  induction m with
  | nil => rfl
  | cons e m ih =>
    change (Bool.rec (motive := fun _ => Bool) (hits f m) true (hit f e) : Bool) = false
    rw [bR, h e (by simp), ih (fun x hx => h x (by simp [hx]))]; rfl
lemma rect_false {d : Bool} {l o : ℕ} {v : List W} : ∀ {m : List ℕ}, v.Pairwise (fun a b => hit (flag d l o b) (flag d l o a) = false) →
    (∀ w ∈ v, ∀ e ∈ m, hit (flag d l o w) e = false) → rect d l o v m = false := by
  induction v with
  | nil => intros; rfl
  | cons w v ih =>
    intro m hp hm
    change (Bool.rec (motive := fun _ => Bool) (rect d l o v (flag d l o w :: m)) true (hits (flag d l o w) m) : Bool) = false
    rw [List.pairwise_cons] at hp
    rw [bR, hits_false (hm w (by simp)), ih hp.2]; · rfl
    intro w' hw' e he
    simp at he
    rcases he with rfl | he
    · exact hp.1 w' hw'
    · exact hm w' (by simp [hw']) e he
lemma Live.pos {m T k t : ℕ} {S : Finset ℕ} (h : Live R m T k t S) : 0 < S.card := by
  cases h with
  | stop => simp
  | un => exact Finset.card_pos.2 (Finset.insert_nonempty _ _)
  | bi => exact Finset.card_pos.2 (Finset.insert_nonempty _ _)
def pk (n : ℕ) (f : ℕ → ℕ) : ℕ := ∑ j ∈ Finset.range n, f j * 2 ^ (5 * j)
lemma pk_succ (n : ℕ) (f : ℕ → ℕ) : pk (n + 1) f = 2 ^ (5 * n) * f n + pk n f := by
  rw [pk, Finset.sum_range_succ, ← pk]; ring
lemma pk_lt {n : ℕ} {f : ℕ → ℕ} (h : ∀ j < n, f j < 32) : pk n f < 2 ^ (5 * n) := by
  induction n with
  | zero => simp [pk]
  | succ n ih =>
    have := ih (fun j hj => h j (by omega))
    have h2 := h n (by omega)
    rw [pk_succ, show 5 * (n + 1) = 5 * n + 5 by ring, pow_add]
    have : 2 ^ (5 * n) * f n ≤ 2 ^ (5 * n) * 31 := Nat.mul_le_mul_left _ (by omega)
    omega
lemma pk_add (n : ℕ) (f g : ℕ → ℕ) : pk n f + pk n g = pk n (fun j => f j + g j) := by
  simp [pk, ← Finset.sum_add_distrib, add_mul]
lemma pk_congr {n : ℕ} {f g : ℕ → ℕ} (h : ∀ j < n, f j = g j) : pk n f = pk n g :=
  Finset.sum_congr rfl fun j hj => by rw [h j (by simpa using hj)]
lemma pk_sub {n : ℕ} {f g : ℕ → ℕ} (h : ∀ j < n, g j ≤ f j) : pk n f - pk n g = pk n (fun j => f j - g j) := by
  have : pk n (fun j => f j - g j) + pk n g = pk n f := by
    rw [pk_add]; exact pk_congr fun j hj => Nat.sub_add_cancel (h j hj)
  omega
lemma pk_guard {n : ℕ} {f : ℕ → ℕ} (h : ∀ j < n, 16 ≤ f j ∧ f j < 32) :
    pk n f &&& pk n (fun _ => 16) = pk n (fun _ => 16) := by
  induction n with
  | zero => simp [pk]
  | succ n ih =>
    have ih := ih (fun j hj => h j (by omega))
    have h1 : pk n f < 2 ^ (5 * n) := pk_lt fun j hj => (h j (by omega)).2
    have h2 : pk n (fun _ => 16) < 2 ^ (5 * n) := pk_lt fun _ _ => by omega
    have h3 : f n &&& 16 = 16 := by
      obtain ⟨a, b⟩ := h n (by omega)
      generalize f n = x at *
      interval_cases x <;> rfl
    rw [pk_succ, pk_succ]
    apply Nat.eq_of_testBit_eq; intro i
    rw [Nat.testBit_and, Nat.testBit_two_pow_mul_add _ h1, Nat.testBit_two_pow_mul_add _ h2]
    split_ifs with hi
    · rw [← Nat.testBit_and, ih]
    · rw [← Nat.testBit_and, h3]
def isPk (n x : ℕ) : Prop := ∀ i, x.testBit i = true → i % 5 = 0 ∧ i / 5 < n
lemma pk_of {n : ℕ} : ∀ {x : ℕ}, isPk n x → x = pk n (fun j => (x.testBit (5 * j)).toNat) := by
  induction n with
  | zero =>
    intro x h
    simp only [pk, Finset.range_zero, Finset.sum_empty]
    apply Nat.eq_of_testBit_eq; intro i
    by_contra hc
    have := h i (by simpa using hc); omega
  | succ n ih =>
    intro x h
    have hm : isPk n (x % 2 ^ (5 * n)) := by
      intro i hi
      simp only [Nat.testBit_mod_two_pow, Bool.and_eq_true, decide_eq_true_eq] at hi
      exact ⟨(h i hi.2).1, by omega⟩
    have e := ih hm
    have hd : x / 2 ^ (5 * n) = (x.testBit (5 * n)).toNat := by
      apply Nat.eq_of_testBit_eq; intro i
      rw [Nat.testBit_div_two_pow]
      cases i with
      | zero => cases hb : x.testBit (5 * n) <;> simp [hb]
      | succ i =>
        have e1 : x.testBit (i + 1 + 5 * n) = false := by
          by_contra hc
          have := h _ (by simpa using hc); omega
        rw [e1]
        cases x.testBit (5 * n) <;> simp [Nat.testBit_succ]
    rw [pk_succ, ← hd]
    have e2 : pk n (fun j => (x.testBit (5 * j)).toNat) = x % 2 ^ (5 * n) := by
      conv_rhs => rw [e]
      refine pk_congr fun j hj => ?_
      rw [Nat.testBit_mod_two_pow]; simp [show 5 * j < 5 * n by omega]
    rw [e2]; exact (Nat.div_add_mod x _).symm
lemma isPk_and {n x y : ℕ} (hx : isPk n x) : isPk n (x &&& y) := fun i hi => hx i (by simp at hi; exact hi.1)
lemma isPk_or {n x y : ℕ} (hx : isPk n x) (hy : isPk n y) : isPk n (x ||| y) := fun i hi => by
  simp at hi; exact hi.elim (hx i) (hy i)
def fl (w : W) (j : ℕ) : ℕ := (w.c.testBit (5 * j)).toNat
lemma fl_le (w : W) (j : ℕ) : fl w j ≤ 1 := by unfold fl; cases w.c.testBit (5 * j) <;> simp
def cnt (v : List W) (j : ℕ) : ℕ := (v.map (fun w => fl w j)).sum
lemma cnt_cons (w : W) (v : List W) (j : ℕ) : cnt (w :: v) j = fl w j + cnt v j := by simp [cnt]
lemma cnt_perm {v v' : List W} (h : v.Perm v') (j : ℕ) : cnt v j = cnt v' j := (h.map _).sum_eq
structure WOk (P : List ℕ) (w : W) : Prop where
  pa : isPk P.length w.a
  pb : isPk P.length w.b
  ec : w.c = w.a ||| w.b
  ca : ∀ j < P.length, w.a.testBit (5 * j) = true → w.s &&& P.getD j 0 = 0
  cb : ∀ j < P.length, w.b.testBit (5 * j) = true → w.s &&& P.getD j 0 = P.getD j 0
lemma WOk.pc {P : List ℕ} {w : W} (h : WOk P w) : isPk P.length w.c := by rw [h.ec]; exact isPk_or h.pa h.pb
lemma WOk.cst {P : List ℕ} {w : W} (h : WOk P w) {j : ℕ} (hj : j < P.length) (hf : w.c.testBit (5 * j) = true) :
    Cst (P.getD j 0) w.s := by
  rw [h.ec, Nat.testBit_or, Bool.or_eq_true] at hf
  exact hf.elim (fun h1 => Or.inl (h.ca j hj h1)) (fun h1 => Or.inr (h.cb j hj h1))
def Cl (P : List ℕ) (T k : ℕ) (b : ℕ → ℕ) (S : Finset ℕ) : Prop := ∀ j < P.length, ∀ q, q + b j < k →
  ¬ Sol Z0 (P.getD j 0) (T &&& P.getD j 0) q (C (P.getD j 0) (Im (P.getD j 0) S))
structure StOk (P : List ℕ) (T l k z : ℕ) (v : List W) (S : Finset ℕ) : Prop where
  rep : Rep v S
  wok : ∀ w ∈ v, WOk P w
  good : ∀ w ∈ v, Good l w.s
  bud : ∃ b : ℕ → ℕ, (∀ j < P.length, b j ≤ 15) ∧ Cl P T k b S ∧ z = pk P.length (fun j => 16 + b j - cnt v j)
structure Ctx (P : List ℕ) (l m g T : ℕ) : Prop where
  lg : ∀ i, l.testBit i = true → Lg I.NN m T i ∧ I.AA.testBit i = true
  hP : ∀ j < P.length, P.getD j 0 &&& m = P.getD j 0 ∧ T &&& P.getD j 0 ≠ 0 ∧ T &&& P.getD j 0 ≠ P.getD j 0
  hg : g = pk P.length (fun _ => 16)
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma cnt_le {k k' t : ℕ} {v : List W} {S : Finset ℕ} {b : ℕ → ℕ} (hr : Rep v S) (hw : ∀ w ∈ v, WOk P w)
    (hc : Cl P T k b S) (hm : Min R m T k' t S) (hk : k' ≤ k) : ∀ j < P.length, cnt v j ≤ b j := by
  intro j hj
  obtain ⟨p1, p2, p3⟩ := X.hP j hj
  obtain ⟨q, hq, hs⟩ := hm.const p1 p2 p3
  have hqb : ¬ q + b j < k := fun h => hc j hj q h hs
  have : cnt v j ≤ (S.filter (Cst (P.getD j 0))).card := by
    have e : cnt v j = (v.filter (fun w => w.c.testBit (5 * j))).length := by
      clear hr hw
      induction v with
      | nil => rfl
      | cons w v ih =>
        rw [cnt_cons, ih, List.filter_cons, fl]
        cases w.c.testBit (5 * j) <;> simp; omega
    rw [e, ← List.length_map W.s, ← List.toFinset_card_of_nodup (hr.1.sublist (List.filter_sublist.map _))]
    apply Finset.card_le_card
    intro x hx
    simp only [List.mem_toFinset, List.mem_map, List.mem_filter] at hx
    obtain ⟨w, ⟨h1, h2⟩, rfl⟩ := hx
    rw [Finset.mem_filter]
    exact ⟨hr.mem.2 ⟨w, h1, rfl⟩, (hw w h1).cst hj h2⟩
  omega
lemma guard_ok {k k' t z : ℕ} {v : List W} {S : Finset ℕ} (hr : StOk P T l k z v S) (hm : Min R m T k' t S) (hk : k' ≤ k) :
    Nat.beq (Nat.land z g) g = true := by
  obtain ⟨b, hb, hc, hz⟩ := hr.bud
  have hle := cnt_le X hr.rep hr.wok hc hm hk
  rw [nl, hz, X.hg, pk_guard]; · simp
  intro j hj
  have := hb j hj; have := hle j hj; omega
lemma child_sound {f : ℕ → List W → Bool} {z t k k' : ℕ} {r : List W} {S : Finset ℕ}
    {mk : (List W → Bool) → Bool} (hmk : ∀ h, mk h = h r)
    (hr : StOk P T l k z r S) (hm : Min R m T k' t S) (hk : k' ≤ k) (h : child f g mk z = false) : f z r = false := by
  simp only [child, bR, st_eq, guard_ok X hr hm hk, cond_true, hmk] at h
  exact h
end sound
lemma rm_eq (x y : ℕ) (v : List W) : ∀ h, rm x y v h = h (v.filter (fun w => !(Nat.beq w.s x || Nat.beq w.s y))) := by
  induction v with
  | nil => intro h; rfl
  | cons w v ih =>
    intro h
    change (Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) (rm x y v (fun r => h (w :: r)))
      (rm x y v h) (Nat.beq w.s y)) (rm x y v h) (Nat.beq w.s x) : Bool) = _
    rw [bR, bR, ih, ih, List.filter_cons]
    cases Nat.beq w.s x <;> cases Nat.beq w.s y <;> simp
lemma ins_spec (o : W) (v : List W) (hv : ∀ w ∈ v, w.s ≠ o.s) : ∃ r : List W, r.Perm (o :: v) ∧ ∀ h, ins o v h = h r := by
  induction v with
  | nil => exact ⟨[o], List.Perm.refl _, fun h => rfl⟩
  | cons w v ih =>
    obtain ⟨r, hp, hr⟩ := ih fun w' hw' => hv w' (by simp [hw'])
    have e : ∀ h, ins o (w :: v) h = bif Nat.ble w.s o.s then (bif Nat.beq o.s w.s then false else h (o :: w :: v)) else ins o v (fun r => h (w :: r)) := by
      intro h
      change (Bool.rec (motive := fun _ => Bool) (ins o v (fun r => h (w :: r)))
        (Bool.rec (motive := fun _ => Bool) (h (o :: w :: v)) false (Nat.beq o.s w.s)) (Nat.ble w.s o.s) : Bool) = _
      rw [bR, bR]
    cases hb : Nat.ble w.s o.s with
    | true =>
      refine ⟨o :: w :: v, List.Perm.refl _, fun h => ?_⟩
      have : Nat.beq o.s w.s = false := Bool.eq_false_iff.2 fun h => hv w (by simp) (Nat.eq_of_beq_eq_true h).symm
      rw [e, hb, this]; rfl
    | false =>
      refine ⟨w :: r, (List.Perm.cons w hp).trans (List.Perm.swap _ _ _), fun h => ?_⟩
      rw [e, hb, hr]; rfl
lemma filter_perm {v : List W} (hv : (v.map W.s).Nodup) {a : W} (ha : a ∈ v) :
    (a :: v.filter (fun w => !Nat.beq w.s a.s)).Perm v := by
  induction v with
  | nil => simp at ha
  | cons w v ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hv
    have hne : ∀ x y : ℕ, x ≠ y → Nat.beq x y = false := fun x y h => Bool.eq_false_iff.2 fun h' => h (Nat.eq_of_beq_eq_true h')
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · have : v.filter (fun w => !Nat.beq w.s a.s) = v := by
        rw [List.filter_eq_self]
        intro w' hw'
        rw [hne _ _ (hv.1 w' hw')]; rfl
      rw [List.filter_cons, this]; simp
    · rw [List.filter_cons, hne w.s a.s (fun e => hv.1 a ha e.symm)]
      simp only [Bool.not_false, if_true]
      exact (List.Perm.swap _ _ _).trans ((ih hv.2 ha).cons w)
lemma filter2 {v : List W} {x y : ℕ} : v.filter (fun w => !(Nat.beq w.s x || Nat.beq w.s y)) =
    (v.filter (fun w => !Nat.beq w.s x)).filter (fun w => !Nat.beq w.s y) := by
  rw [List.filter_filter]; congr 1; funext w; cases Nat.beq w.s x <;> cases Nat.beq w.s y <;> rfl
lemma filter1 {v : List W} {x : ℕ} : v.filter (fun w => !(Nat.beq w.s x || Nat.beq w.s x)) = v.filter (fun w => !Nat.beq w.s x) := by
  congr 1; funext w; cases Nat.beq w.s x <;> rfl
inductive Shape (o a c : W) (v : List W) : Bool → Bool → List W → Prop
  | ff {r} : (a :: c :: r).Perm (o :: v) → Shape o a c v false false r
  | tf {r} : (c :: r).Perm (o :: v) → Shape o a c v true false r
  | ft {r} : (a :: r).Perm (o :: v) → Shape o a c v false true r
  | tt {r} : r.Perm (o :: v) → Shape o a c v true true r
lemma Shape.cnt {o a c : W} {v r : List W} {ka kc : Bool} (h : Shape o a c v ka kc r) (j : ℕ) :
    cnt r j + (bif ka then 0 else fl a j) + (bif kc then 0 else fl c j) = fl o j + cnt v j := by
  cases h with
  | ff h => have := cnt_perm h j; simp only [cnt_cons] at this; simp; omega
  | tf h => have := cnt_perm h j; simp only [cnt_cons] at this; simp; omega
  | ft h => have := cnt_perm h j; simp only [cnt_cons] at this; simp; omega
  | tt h => have := cnt_perm h j; simp only [cnt_cons] at this; simp; omega
lemma Shape.mem {o a c : W} {v r : List W} {ka kc : Bool} (h : Shape o a c v ka kc r) {w : W} (hw : w ∈ r) : w = o ∨ w ∈ v := by
  have : w ∈ o :: v := by
    cases h with
    | ff h => exact h.subset (by simp [hw])
    | tf h => exact h.subset (by simp [hw])
    | ft h => exact h.subset (by simp [hw])
    | tt h => exact h.subset (by simp [hw])
  simpa using this
lemma Shape.len {o a c : W} {v r : List W} {ka kc : Bool} (h : Shape o a c v ka kc r) :
    r.length + (bif ka then 0 else 1) + (bif kc then 0 else 1) = v.length + 1 := by
  cases h with
  | ff h => have := h.length_eq; simp at this ⊢; omega
  | tf h => have := h.length_eq; simp at this ⊢; omega
  | ft h => have := h.length_eq; simp at this ⊢; omega
  | tt h => have := h.length_eq; simp at this ⊢; omega
lemma Shape.rep {o a c : W} {v r : List W} {ka kc : Bool} (h : Shape o a c v ka kc r) {S S' : Finset ℕ} (hr : Rep v S)
    (ha : a ∈ v) (hc : c ∈ v) (hac : a.s ≠ c.s) (ho : o.s ∉ S)
    (hS : ∀ x, x ∈ S' ↔ x = o.s ∨ (x ∈ S ∧ (x = a.s → ka = true) ∧ (x = c.s → kc = true))) : Rep r S' := by
  have hov : ((o :: v).map W.s).Nodup := by
    simp only [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ho ?_, hr.1⟩
    rw [← hr.2]; simpa using hm
  have hvS : ∀ x, x ∈ v.map W.s ↔ x ∈ S := fun x => by rw [← hr.2]; simp
  have hm : ∀ x, x ∈ (o :: v).map W.s ↔ x = o.s ∨ x ∈ S := fun x => by simp only [List.map_cons, List.mem_cons, hvS]
  have haS := (hvS a.s).1 (List.mem_map_of_mem ha)
  have hcS := (hvS c.s).1 (List.mem_map_of_mem hc)
  have hao : a.s ≠ o.s := fun e => ho (e ▸ haS)
  have hco : c.s ≠ o.s := fun e => ho (e ▸ hcS)
  cases h with
  | ff h =>
    have hn := (h.map W.s).nodup_iff.2 hov
    simp only [List.map_cons, List.nodup_cons, List.mem_cons, not_or] at hn
    refine ⟨hn.2.2, Finset.ext fun x => ?_⟩
    have hx := (h.map W.s).mem_iff (a := x)
    rw [hm] at hx; simp only [List.map_cons, List.mem_cons] at hx
    rw [List.mem_toFinset, hS]
    constructor
    · intro h1
      have n1 : x ≠ a.s := fun e => hn.1.2 (e ▸ h1)
      have n2 : x ≠ c.s := fun e => hn.2.1 (e ▸ h1)
      rcases hx.1 (Or.inr (Or.inr h1)) with e | e
      · exact Or.inl e
      · exact Or.inr ⟨e, fun e => absurd e n1, fun e => absurd e n2⟩
    · rintro (e | ⟨e, f1, f2⟩)
      · rcases hx.2 (Or.inl e) with e' | e' | e'
        · exact absurd (e'.symm.trans e) hao
        · exact absurd (e'.symm.trans e) hco
        · exact e'
      · rcases hx.2 (Or.inr e) with e' | e' | e'
        · exact absurd (f1 e') (by simp)
        · exact absurd (f2 e') (by simp)
        · exact e'
  | tf h =>
    have hn := (h.map W.s).nodup_iff.2 hov
    simp only [List.map_cons, List.nodup_cons] at hn
    refine ⟨hn.2, Finset.ext fun x => ?_⟩
    have hx := (h.map W.s).mem_iff (a := x)
    rw [hm] at hx; simp only [List.map_cons, List.mem_cons] at hx
    rw [List.mem_toFinset, hS]
    constructor
    · intro h1
      have n2 : x ≠ c.s := fun e => hn.1 (e ▸ h1)
      rcases hx.1 (Or.inr h1) with e | e
      · exact Or.inl e
      · exact Or.inr ⟨e, fun _ => rfl, fun e => absurd e n2⟩
    · rintro (e | ⟨e, f1, f2⟩)
      · exact (hx.2 (Or.inl e)).resolve_left fun e' => hco (e'.symm.trans e)
      · exact (hx.2 (Or.inr e)).resolve_left fun e' => by simpa using f2 e'
  | ft h =>
    have hn := (h.map W.s).nodup_iff.2 hov
    simp only [List.map_cons, List.nodup_cons] at hn
    refine ⟨hn.2, Finset.ext fun x => ?_⟩
    have hx := (h.map W.s).mem_iff (a := x)
    rw [hm] at hx; simp only [List.map_cons, List.mem_cons] at hx
    rw [List.mem_toFinset, hS]
    constructor
    · intro h1
      have n2 : x ≠ a.s := fun e => hn.1 (e ▸ h1)
      rcases hx.1 (Or.inr h1) with e | e
      · exact Or.inl e
      · exact Or.inr ⟨e, fun e => absurd e n2, fun _ => rfl⟩
    · rintro (e | ⟨e, f1, f2⟩)
      · exact (hx.2 (Or.inl e)).resolve_left fun e' => hao (e'.symm.trans e)
      · exact (hx.2 (Or.inr e)).resolve_left fun e' => by simpa using f1 e'
  | tt h =>
    have hn := (h.map W.s).nodup_iff.2 hov
    refine ⟨hn, Finset.ext fun x => ?_⟩
    have hx := (h.map W.s).mem_iff (a := x)
    rw [hm] at hx
    rw [List.mem_toFinset, hS, hx]; simp
lemma shape_all {o a c : W} {v r : List W} (ho : ∀ w ∈ v, w.s ≠ o.s) (hp : r.Perm (o :: v)) (hv : (v.map W.s).Nodup)
    (ha : a ∈ v) (hc : c ∈ v) (hac : a.s ≠ c.s) :
    Shape o a c v false false (r.filter (fun w => !(Nat.beq w.s a.s || Nat.beq w.s c.s))) ∧
    Shape o a c v true false (r.filter (fun w => !(Nat.beq w.s c.s || Nat.beq w.s c.s))) ∧
    Shape o a c v false true (r.filter (fun w => !(Nat.beq w.s a.s || Nat.beq w.s a.s))) ∧ Shape o a c v true true r := by
  have hnd : (r.map W.s).Nodup := by
    refine (hp.map W.s).nodup_iff.2 ?_
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and]
    exact ⟨fun w hw => ho w hw, hv⟩
  have har : a ∈ r := hp.symm.subset (by simp [ha])
  have hcr : c ∈ r := hp.symm.subset (by simp [hc])
  refine ⟨.ff ?_, .tf ?_, .ft ?_, .tt hp⟩
  · rw [filter2]
    have h1 := filter_perm hnd har
    have h2 : c ∈ r.filter (fun w => !Nat.beq w.s a.s) := by
      rw [List.mem_filter]; refine ⟨hcr, ?_⟩
      rw [Bool.eq_false_iff.2 fun h => hac (Nat.eq_of_beq_eq_true h).symm]; rfl
    exact ((filter_perm (hnd.sublist (List.filter_sublist.map _)) h2).cons a).trans (h1.trans hp)
  · rw [filter1]; exact (filter_perm hnd hcr).trans hp
  · rw [filter1]; exact (filter_perm hnd har).trans hp
lemma cnt_two {v : List W} {a c : W} (ha : a ∈ v) (hc : c ∈ v) (hv : (v.map W.s).Nodup) (hac : a.s ≠ c.s) (j : ℕ) :
    fl a j + fl c j ≤ cnt v j := by
  have h1 := cnt_perm (filter_perm hv ha) j
  have h2 : c ∈ v.filter (fun w => !Nat.beq w.s a.s) := by
    rw [List.mem_filter]; refine ⟨hc, ?_⟩
    rw [Bool.eq_false_iff.2 fun h => hac (Nat.eq_of_beq_eq_true h).symm]; rfl
  have h3 := cnt_perm (filter_perm (hv.sublist (List.filter_sublist.map _)) h2) j
  simp only [cnt_cons] at h1 h3; omega
lemma cnt_one {v : List W} {a : W} (ha : a ∈ v) (hv : (v.map W.s).Nodup) (j : ℕ) : fl a j ≤ cnt v j := by
  have h1 := cnt_perm (filter_perm hv ha) j
  simp only [cnt_cons] at h1; omega
def opW (d : Bool) (a c : W) : W := bif d then ⟨a.s ||| c.s, a.a &&& c.a, a.b ||| c.b, (a.a &&& c.a) ||| (a.b ||| c.b), 0⟩
  else ⟨a.s &&& c.s, a.a ||| c.a, a.b &&& c.b, (a.a ||| c.a) ||| (a.b &&& c.b), 0⟩
lemma opW_s (d : Bool) (a c : W) : (opW d a c).s = op d a.s c.s := by cases d <;> rfl
lemma opW_ok {P : List ℕ} {a c : W} (d : Bool) (ha : WOk P a) (hc : WOk P c) : WOk P (opW d a c) := by
  cases d
  · refine ⟨isPk_or ha.pa hc.pa, isPk_and ha.pb, rfl, fun j hj h => ?_, fun j hj h => ?_⟩
    · have h : (a.a ||| c.a).testBit (5 * j) = true := h
      rw [Nat.testBit_or, Bool.or_eq_true] at h
      rw [opW_s, and_op]
      rcases h with h | h
      · rw [ha.ca j hj h]; simp [op]
      · rw [hc.ca j hj h]; simp [op]
    · have h : (a.b &&& c.b).testBit (5 * j) = true := h
      rw [Nat.testBit_and, Bool.and_eq_true] at h
      rw [opW_s, and_op, ha.cb j hj h.1, hc.cb j hj h.2, op_self]
  · refine ⟨isPk_and ha.pa, isPk_or ha.pb hc.pb, rfl, fun j hj h => ?_, fun j hj h => ?_⟩
    · have h : (a.a &&& c.a).testBit (5 * j) = true := h
      rw [Nat.testBit_and, Bool.and_eq_true] at h
      rw [opW_s, and_op, ha.ca j hj h.1, hc.ca j hj h.2, op_self]
    · have h : (a.b ||| c.b).testBit (5 * j) = true := h
      rw [Nat.testBit_or, Bool.or_eq_true] at h
      rw [opW_s, and_op]
      rcases h with h | h
      · rw [ha.cb j hj h]; apply Nat.eq_of_testBit_eq; intro i; simp [op]
      · rw [hc.cb j hj h]; apply Nat.eq_of_testBit_eq; intro i; simp [op]
lemma op_good {l x y : ℕ} (d : Bool) (hx : Good l x) (hy : Good l y) : Good l (op d x y) := by
  refine ⟨fun i j h h1 h2 => ?_, fun i j h h1 h2 => ?_⟩
  · rw [op_bit, op_bit, hx.1 i j h h1 h2, hy.1 i j h h1 h2]
  · rw [op_bit, op_bit, hx.2 i j h h1 h2, hy.2 i j h h1 h2]
lemma fl_and {P : List ℕ} {a c : W} (ha : WOk P a) : a.c &&& c.c = pk P.length (fun j => fl a j * fl c j) := by
  rw [pk_of (isPk_and (y := c.c) ha.pc)]
  refine pk_congr fun j _ => ?_
  rw [Nat.testBit_and]; unfold fl; cases a.c.testBit (5 * j) <;> cases c.c.testBit (5 * j) <;> rfl
lemma fl_pk {P : List ℕ} {a : W} (ha : WOk P a) : a.c = pk P.length (fl a) := pk_of ha.pc
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma bi_st {k k' t z : ℕ} {v r : List W} {S S' : Finset ℕ} {d' : Bool} {a c : W} {ka kc : Bool}
    (hs : StOk P T l (k + 1) z v S) (hm : Min R m T (k' + 1) t S) (hk : k' ≤ k) (hb : Bi R d' a.s c.s S S')
    (hl : Live R m T k' t S') (ha : a ∈ v) (hc : c ∈ v) (hka : ka = decide (a.s ∈ S')) (hkc : kc = decide (c.s ∈ S'))
    (hsh : Shape (opW d' a c) a c v ka kc r) :
    StOk P T l k (z + (a.c &&& c.c) - (opW d' a c).c - (bif ka then a.c else 0) - (bif kc then c.c else 0)) r S' ∧
    Nat.beq (Nat.land (z + (a.c &&& c.c) - (opW d' a c).c) g) g = true := by
  obtain ⟨b, hb15, hcl, hz⟩ := hs.bud
  have hle := cnt_le X hs.rep hs.wok hcl hm (by omega)
  have hab : a.s ≠ c.s := hb.1
  have hfr := hb.fresh hl hm.2
  have hfS : (opW d' a c).s ∉ S := by rw [opW_s]; exact fun h => hfr (sub_C _ _ (by simpa using h))
  have wa := hs.wok a ha; have wc := hs.wok c hc
  have wo := opW_ok d' wa wc
  have hrep : Rep r S' := by
    refine hsh.rep hs.rep ha hc hab hfS fun x => ?_
    obtain ⟨_, U, e1, e2, _⟩ := hb
    rw [opW_s] at hfS ⊢
    rw [e2, Finset.mem_insert]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · refine Or.inr ⟨by rw [e1]; simp [h], ?_, ?_⟩
        · rintro rfl; rw [hka, e2]; simp [h]
        · rintro rfl; rw [hkc, e2]; simp [h]
    · rintro (h | ⟨h, f1, f2⟩)
      · exact Or.inl h
      · rw [e1] at h; simp only [Finset.mem_insert] at h
        rcases h with h | h | h
        · have := f1 h; rw [hka, decide_eq_true_eq, e2, Finset.mem_insert] at this; rw [h]; exact this
        · have := f2 h; rw [hkc, decide_eq_true_eq, e2, Finset.mem_insert] at this; rw [h]; exact this
        · exact Or.inr h
  have hwok : ∀ w ∈ r, WOk P w := fun w hw => (hsh.mem hw).elim (fun e => e ▸ wo) (hs.wok w)
  have hgood : ∀ w ∈ r, Good l w.s := fun w hw => by
    rcases hsh.mem hw with rfl | h
    · rw [opW_s]; exact op_good _ (hs.good a ha) (hs.good c hc)
    · exact hs.good w h
  let b' : ℕ → ℕ := fun j => b j - max (fl a j) (fl c j)
  have hcl' : Cl P T k b' S' := by
    intro j hj q hq hsol
    have hl1 := hle j hj
    have h2 := cnt_two ha hc hs.rep.1 hab j
    simp only [b'] at hq
    by_cases hkill : a.c.testBit (5 * j) = true ∨ c.c.testBit (5 * j) = true
    · refine hcl j hj q ?_ (hb.kill (hkill.imp (wa.cst hj) (wc.cst hj)) hsol)
      have : 1 ≤ max (fl a j) (fl c j) := by
        rcases hkill with h | h <;> simp [fl, h]
      have := fl_le a j; have := fl_le c j; omega
    · push Not at hkill
      refine hcl j hj (q + 1) ?_ (hb.im hsol)
      have e1 : fl a j = 0 := by simp [fl, hkill.1]
      have e2 : fl c j = 0 := by simp [fl, hkill.2]
      rw [e1, e2] at hq; simp at hq; omega
  have hmin := hb.min hl hm.2
  have hle' := cnt_le X hrep hwok hcl' hmin hk
  have num : ∀ j < P.length, 1 ≤ 16 + b j - cnt v j + fl a j * fl c j ∧ fl (opW d' a c) j ≤ 1 ∧
      16 ≤ 16 + b j - cnt v j + fl a j * fl c j - fl (opW d' a c) j ∧ 16 + b j - cnt v j + fl a j * fl c j - fl (opW d' a c) j < 32 ∧
      16 + b j - cnt v j + fl a j * fl c j - fl (opW d' a c) j - (bif ka then fl a j else 0) - (bif kc then fl c j else 0) = 16 + b' j - cnt r j := by
    intro j hj
    have q1 := hle j hj; have q2 := hle' j hj; have q3 := cnt_two ha hc hs.rep.1 hab j; have q4 := hb15 j hj
    have q5 := hsh.cnt j; have q6 := fl_le a j; have q7 := fl_le c j; have q8 := fl_le (opW d' a c) j
    simp only [b'] at q2 ⊢
    generalize fl a j = fa at *; generalize fl c j = fc at *; generalize fl (opW d' a c) j = fo at *
    interval_cases fa <;> interval_cases fc <;> cases ka <;> cases kc <;> simp at q2 q3 q5 ⊢ <;> omega
  have e1 : z + (a.c &&& c.c) - (opW d' a c).c = pk P.length (fun j => 16 + b j - cnt v j + fl a j * fl c j - fl (opW d' a c) j) := by
    rw [hz, fl_and wa, fl_pk wo, pk_add, pk_sub]
    intro j hj; have := num j hj; omega
  refine ⟨⟨hrep, hwok, hgood, b', fun j hj => ?_, hcl', ?_⟩, ?_⟩
  · have := hb15 j hj; simp only [b']; omega
  · rw [e1]
    have ea : (bif ka then a.c else 0) = pk P.length (fun j => bif ka then fl a j else 0) := by
      cases ka
      · simp [pk]
      · exact fl_pk wa
    have ec : (bif kc then c.c else 0) = pk P.length (fun j => bif kc then fl c j else 0) := by
      cases kc
      · simp [pk]
      · exact fl_pk wc
    have le1 : ∀ j, (bif ka then fl a j else 0) ≤ 1 := fun j => by cases ka <;> simp [fl_le]
    have le2 : ∀ j, (bif kc then fl c j else 0) ≤ 1 := fun j => by cases kc <;> simp [fl_le]
    rw [ea, ec, pk_sub, pk_sub]
    · exact pk_congr fun j hj => (num j hj).2.2.2.2
    · intro j hj; have := num j hj; have := le1 j; have := le2 j; omega
    · intro j hj; have := num j hj; have := le1 j; omega
  · rw [e1, nl, X.hg, pk_guard]; · simp
    intro j hj; have := num j hj; omega
lemma drop_ok {k' t : ℕ} {v : List W} {S S' : Finset ℕ} {d' : Bool} {a c : W} {i : ℕ} (hr : Rep v S)
    (hb : Bi R d' a.s c.s S S') (hl : Live R m T k' t S')
    (ha : a ∈ v) (hk : a.s ∉ S')
    (hu : (Nat.land (sp (pos' t) l a.s) (wst (pos' t) l v)).testBit i = true) :
    bif d' then c.s.testBit (I.NN + i) = false else c.s.testBit i = true := by
  obtain ⟨hli, u1, u2⟩ := uq_of hr ha hu
  obtain ⟨⟨m1, m2, t1, t2⟩, _⟩ := X.lg i hli
  obtain ⟨w, hw, hs⟩ := hl.cov m1 m2 t1 t2
  have hac : c.s ≠ a.s := hb.1.symm
  have hsub := hb.sub.2.2 hw
  rw [Finset.mem_insert] at hsub
  have hg : sepb I.NN (pos' t) (op d' a.s c.s) i = true := by
    rcases hsub with rfl | h
    · exact hs
    · have := u2 w h (fun e => hk (e ▸ hw))
      rw [this] at hs; simp at hs
  have hcn := u2 c.s hb.sub.2.1 hac
  revert hg hcn u1
  unfold sepb; simp only [op_bit]
  cases pos' t <;> cases d' <;> cases a.s.testBit i <;> cases a.s.testBit (I.NN + i) <;> cases c.s.testBit i <;>
    cases c.s.testBit (I.NN + i) <;> simp
end sound
def mkx (d : Bool) (l o : ℕ) (w : W) : XW := ⟨w, w.s, Nat.shiftRight w.s I.NN, Nat.land (sp d l w.s) o⟩
lemma mkX_eq (d : Bool) (l o : ℕ) (v : List W) : mkX d l o v = v.map (mkx d l o) := by
  induction v with
  | nil => rfl
  | cons w v ih => change _ :: mkX d l o v = _; rw [ih]; rfl
def modeF (n e : ℕ) : (W → W → ℕ → ℕ → ℕ → ℕ → ℕ → Bool) → W → W → ℕ → ℕ → ℕ → ℕ → ℕ → Bool :=
  bif Nat.ble n e then (bif Nat.ble (Nat.succ n) e then f2 else f1) else f0
lemma node_eq (f : ℕ → List W → Bool) (d : Bool) (l m g e n z : ℕ) (v : List W) (go : (XW → XW → Bool) → List XW → Bool) :
    node f d l m g e n z v go = go (pair (modeF n e (mid f m g e (Nat.pred n) z v))) (v.map (mkx d l (wst d l v))) := by
  rw [← mkX_eq]; unfold node nodeC modeF
  cases Nat.ble n e <;> cases Nat.ble (Nat.succ n) e <;> rfl
lemma modeF_false {n e : ℕ} {h : W → W → ℕ → ℕ → ℕ → ℕ → ℕ → Bool} {a c : W} {da dc : ℕ} {s x y : ℕ}
    (hf : modeF n e h a c da dc s x y = false) (h0 : ¬ n ≤ e → da = 0 ∧ dc = 0) (h1 : ¬ n + 1 ≤ e → da = 0 ∨ dc = 0) :
    h a c da dc s x y = false := by
  unfold modeF at hf
  cases b1 : Nat.ble n e with
  | false =>
    have := h0 (fun h => by rw [Nat.ble_eq_true_of_le h] at b1; simp at b1)
    rw [b1, this.1, this.2] at hf; rw [this.1, this.2]; exact hf
  | true =>
    cases b2 : Nat.ble (Nat.succ n) e with
    | false =>
      have := h1 (fun h => by rw [Nat.ble_eq_true_of_le h] at b2; simp at b2)
      have h3 : Nat.beq (Nat.mul da dc) 0 = true := by
        change Nat.beq (da * dc) 0 = true
        rcases this with h | h <;> simp [h]
      rw [b1, b2] at hf
      simp only [Bool.cond_true, Bool.cond_false, f1, h3] at hf
      exact hf
    | true => rw [b1, b2] at hf; exact hf
def dfc (d d' : Bool) (l o : ℕ) (a c : W) : ℕ := bif d' then Nat.land (Nat.land (sp d l a.s) o) (Nat.shiftRight c.s I.NN)
  else Nat.xor (Nat.land (Nat.land (sp d l a.s) o) c.s) (Nat.land (sp d l a.s) o)
lemma pair_false {h : W → W → ℕ → ℕ → ℕ → ℕ → ℕ → Bool} {d : Bool} {l o : ℕ} {a c : W}
    (hp : pair h (mkx d l o a) (mkx d l o c) = false) (d' : Bool) :
    h a c (dfc d d' l o a c) (dfc d d' l o c a) (opW d' a c).s (opW d' a c).a (opW d' a c).b = false := by
  simp only [pair, mkx, bR] at hp
  rw [Bool.cond_eq_ite] at hp
  split_ifs at hp with h1
  · cases d'
    · rw [Bool.not_eq_true] at h1; exact h1
    · exact hp
lemma put_eq {m : ℕ} {o : W} {v : List W} (ho : Nat.lor o.a o.b = o.c) (hr : o.r = 0) (h0 : o.s ≠ 0) (h1 : o.s ≠ m) (h : List W → Bool) :
    put m o.s o.a o.b v h = ins o v h := by
  have hb0 : Nat.beq o.s 0 = false := Bool.eq_false_iff.2 fun h => h0 (Nat.eq_of_beq_eq_true h)
  have hb1 : Nat.beq o.s m = false := Bool.eq_false_iff.2 fun h => h1 (Nat.eq_of_beq_eq_true h)
  simp only [put, st_eq, hb0, hb1, ho]
  rw [← hr]
lemma mid_false {f : ℕ → List W → Bool} {m g e n z : ℕ} {v : List W} {a c : W} {da dc : ℕ} {d' : Bool}
    (h : mid f m g e n z v a c da dc (opW d' a c).s (opW d' a c).a (opW d' a c).b = false)
    (hg : Nat.beq (Nat.land (z + (a.c &&& c.c) - (opW d' a c).c) g) g = true) :
    kids (child f g) e n (z + (a.c &&& c.c) - (opW d' a c).c) a.c c.c a.s c.s (Nat.beq da 0) (Nat.beq dc 0)
      (put m (opW d' a c).s (opW d' a c).a (opW d' a c).b v) = false := by
  have ec : Nat.lor (opW d' a c).a (opW d' a c).b = (opW d' a c).c := by cases d' <;> rfl
  simp only [mid, st_eq, ec] at h
  have hg' : Nat.beq (Nat.land (Nat.sub (Nat.add z (Nat.land a.c c.c)) (opW d' a c).c) g) g = true := hg
  rw [hg'] at h
  exact h
lemma kids_false {ch : ((List W → Bool) → Bool) → ℕ → Bool} {e n z x y a c : ℕ} {oa oc : Bool} {mk : (List W → Bool) → Bool}
    (h : kids ch e n z x y a c oa oc mk = false) :
    (oa = true → oc = true → ch (fun h => mk (fun r => rm a c r h)) z = false) ∧
    (oc = true → n + 1 ≤ e → ch (fun h => mk (fun r => rm c c r h)) (z - x) = false) ∧
    (oa = true → n + 1 ≤ e → ch (fun h => mk (fun r => rm a a r h)) (z - y) = false) ∧
    (n + 2 ≤ e → ch mk (z - x - y) = false) := by
  simp only [kids, bR] at h
  have b1 : n + 1 ≤ e → Nat.ble (Nat.succ n) e = true := fun h => Nat.ble_eq_true_of_le h
  have b2 : n + 2 ≤ e → Nat.ble (Nat.succ (Nat.succ n)) e = true := fun h => Nat.ble_eq_true_of_le h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h1 h2; subst h1 h2
    revert h; simp only [Bool.cond_true]; cases ch (fun h => mk (fun r => rm a c r h)) z <;> simp
  · intro h1 h2; subst h1; rw [b1 h2] at h
    revert h; simp only [Bool.cond_true]
    change _ → ch (fun h => mk (fun r => rm c c r h)) (Nat.sub z x) = false
    cases ch (fun h => mk (fun r => rm c c r h)) (Nat.sub z x) <;> simp
  · intro h1 h2; subst h1; rw [b1 h2] at h
    revert h; simp only [Bool.cond_true]
    change _ → ch (fun h => mk (fun r => rm a a r h)) (Nat.sub z y) = false
    cases ch (fun h => mk (fun r => rm a a r h)) (Nat.sub z y) <;> simp
  · intro h2; rw [b2 h2] at h
    revert h; simp only [Bool.cond_true]
    change _ → ch mk (Nat.sub (Nat.sub z x) y) = false
    cases ch mk (Nat.sub (Nat.sub z x) y) <;> simp
lemma Live.rel {R' : ℕ → ℕ} {m T k t : ℕ} {S : Finset ℕ} (h : Live R m T k t S) (hR : ∀ d a b, Al R d a b → Al R' d a b) : Live R' m T k t S := by
  induction h with
  | stop => exact .stop
  | un _ ih => exact .un ih
  | bi hab hal _ ih => exact .bi hab (hR _ _ _ hal) ih
lemma Bi.rel {R' : ℕ → ℕ} {a b : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') (hR : ∀ d a b, Al R d a b → Al R' d a b) : Bi R' d a b S S' := by
  obtain ⟨hab, U, e1, e2, hal⟩ := h; exact ⟨hab, U, e1, e2, hR _ _ _ hal⟩
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma rect_ok {t k k' z : ℕ} {r : List W} {S : Finset ℕ} (hr : StOk P T l k z r S) (hm : Min R m T k' t S) (hk : k' ≤ k)
    (hn : r.length + t = k + 1) : rect (pos' t) l (wst (pos' t) l r) r [] = false := by
  cases hrect : rect (pos' t) l (wst (pos' t) l r) r [] with
  | false => rfl
  | true =>
      exfalso
      have hs := hm.size
      have hcard := hr.rep.card
      have hpos : 0 < S.card := hm.1.pos
      have htight : S.card + t = k' + 1 := by omega
      rw [rect_false (o := wst (pos' t) l r)] at hrect; · simp at hrect
      · have hnd : r.Pairwise (fun a b => a.s ≠ b.s) := List.pairwise_map.1 hr.rep.1
        refine hnd.imp_of_mem fun {a b} ha hb' hab => ?_
        by_contra hhit
        rw [Bool.not_eq_false] at hhit
        obtain ⟨⟨s, hs1, x1, x2⟩, ⟨s', hs2, y1, y2⟩⟩ := hit_spec hhit
        have hu : ∀ w, ∀ i, (Nat.land (sp (pos' t) l w) (wst (pos' t) l r)).testBit i = true → I.AA.testBit i = true := by
          intro w i hi
          simp only [nl, Nat.testBit_and, sp_bit, Bool.and_eq_true] at hi
          exact (X.lg i hi.1.1).2
        obtain ⟨i2, b1, b2, b3⟩ := flag_seg IOk.segX_ok (hu b.s) hs1 x1
        obtain ⟨i1, a1, a2, a3⟩ := flag_seg IOk.segX_ok (hu a.s) hs1 x2
        obtain ⟨j2, d1, d2, d3⟩ := flag_seg IOk.segY_ok (hu b.s) hs2 y1
        obtain ⟨j1, c1, c2, c3⟩ := flag_seg IOk.segY_ok (hu a.s) hs2 y2
        obtain ⟨l1, u1⟩ := uq_of hr.rep ha a3
        obtain ⟨l2, u2⟩ := uq_of hr.rep hb' b3
        obtain ⟨l3, u3⟩ := uq_of hr.rep ha c3
        obtain ⟨l4, u4⟩ := uq_of hr.rep hb' d3
        have g1 : ∀ w ∈ S, w.testBit i1 = w.testBit i2 := by
          intro w hw; obtain ⟨w', hw', rfl⟩ := hr.rep.mem.1 hw
          exact (hr.good w' hw').1 _ _ ⟨s, hs1, a1, a2, b1, b2⟩ l1 l2
        have g2 : ∀ w ∈ S, w.testBit (I.NN + j1) = w.testBit (I.NN + j2) := by
          intro w hw; obtain ⟨w', hw', rfl⟩ := hr.rep.mem.1 hw
          exact (hr.good w' hw').2 _ _ ⟨s', hs2, c1, c2, d1, d2⟩ l3 l4
        have ma := hr.rep.mem.2 ⟨a, ha, rfl⟩
        have mb := hr.rep.mem.2 ⟨b, hb', rfl⟩
        rcases Nat.eq_zero_or_pos t with rfl | htp
        · have hd' : pos' 0 = false := by simp [pos']
          rw [hd'] at u1 u2 u3 u4
          exact rect0 hm.1 hm.2 (by simpa using htight) (X.lg _ l1).1 (X.lg _ l2).1 (X.lg _ l3).1 (X.lg _ l4).1
            ma mb hab g1 g2 u1 u2 u3 u4
        · have hd' : pos' t = true := by simp [pos', htp]
          rw [hd'] at u1 u2 u3 u4
          exact rect1 hm.1 hm.2 htight (X.lg _ l1).1 (X.lg _ l2).1 (X.lg _ l3).1 (X.lg _ l4).1
            ma mb hab g1 g2 u1 u2 u3 u4
      · simp
lemma hit_ht {k z : ℕ} {r : List W} {S : Finset ℕ} {d : Bool} (hr : StOk P T l k z r S) {a b : W} (ha : a ∈ r) (hb : b ∈ r)
    (h : hit (flag false l (wst d l r) a) (flag false l (wst d l r) b) = true) : Ht I.NN m T d S a.s b.s := by
  obtain ⟨⟨s, hs1, x1, x2⟩, ⟨s', hs2, y1, y2⟩⟩ := hit_spec h
  have hu : ∀ w, ∀ i, (Nat.land (sp false l w) (wst d l r)).testBit i = true → I.AA.testBit i = true := by
    intro w i hi
    simp only [nl, Nat.testBit_and, sp_bit, Bool.and_eq_true] at hi
    exact (X.lg i hi.1.1).2
  have uq : ∀ {w : W} {i : ℕ}, w ∈ r → (Nat.land (sp false l w.s) (wst d l r)).testBit i = true →
      l.testBit i = true ∧ Uq I.NN d S w.s i ∧ w.s.testBit i = true := by
    intro w i hw hi
    have hi2 := hi
    simp only [nl, Nat.testBit_and, sp_bit, Bool.and_eq_true] at hi2
    obtain ⟨⟨hl, hs⟩, ho⟩ := hi2
    have hsd : sepb I.NN d w.s i = true := by
      cases d
      · exact hs
      · exact sepb_weak _ hs
    obtain ⟨q1, q2⟩ := uq_of hr.rep hw (d := d) (l := l) (i := i) (by
      simp only [nl, Nat.testBit_and, sp_bit, Bool.and_eq_true]; exact ⟨⟨hl, hsd⟩, ho⟩)
    refine ⟨q1, q2, ?_⟩
    revert hs; simp only [sepb, cond_false]; cases w.s.testBit i <;> simp
  obtain ⟨i1, a1, a2, a3⟩ := flag_seg IOk.segX_ok (hu a.s) hs1 x1
  obtain ⟨i2, b1, b2, b3⟩ := flag_seg IOk.segX_ok (hu b.s) hs1 x2
  obtain ⟨j1, c1, c2, c3⟩ := flag_seg IOk.segY_ok (hu a.s) hs2 y1
  obtain ⟨j2, d1, d2, d3⟩ := flag_seg IOk.segY_ok (hu b.s) hs2 y2
  obtain ⟨l1, u1, p1⟩ := uq ha a3
  obtain ⟨l2, u2, p2⟩ := uq hb b3
  obtain ⟨l3, u3, p3⟩ := uq ha c3
  obtain ⟨l4, u4, p4⟩ := uq hb d3
  refine ⟨i1, i2, j1, j2, (X.lg _ l1).1, (X.lg _ l2).1, (X.lg _ l3).1, (X.lg _ l4).1, ?_, ?_, u1, u2, u3, u4, by rw [p1, p3], by rw [p2, p4]⟩
  · intro w hw; obtain ⟨w', hw', rfl⟩ := hr.rep.mem.1 hw
    exact (hr.good w' hw').1 _ _ ⟨s, hs1, a1, a2, b1, b2⟩ l1 l2
  · intro w hw; obtain ⟨w', hw', rfl⟩ := hr.rep.mem.1 hw
    exact (hr.good w' hw').2 _ _ ⟨s', hs2, c1, c2, d1, d2⟩ l3 l4
end sound
lemma hits_true {f : ℕ} {m : List ℕ} (h : hits f m = true) : ∃ e ∈ m, hit f e = true := by
  by_contra hc
  push Not at hc
  rw [hits_false fun e he => by simpa using hc e he] at h; simp at h
lemma app_mem {x y : List ℕ} {e : ℕ} : e ∈ app x y ↔ e ∈ x ∨ e ∈ y := by
  induction x with
  | nil => simp [app]
  | cons a x ih =>
    change e ∈ a :: app x y ↔ _
    simp only [List.mem_cons, ih, or_assoc]
def CmOk (F : W → ℕ) (r : List W) (col : ℕ → ℕ) (c : Cm) : Prop := ∃ κ ≤ 1, (∀ e ∈ c.a, ∃ w ∈ r, F w = e ∧ col w.s = κ) ∧
  ∀ e ∈ c.b, ∃ w ∈ r, F w = e ∧ col w.s = 1 - κ
lemma join_false {F : W → ℕ} {r : List W} {col : ℕ → ℕ} {k : List Cm → Bool} {w : W} (hw1 : col w.s ≤ 1)
    (hh : ∀ w' ∈ r, hit (F w) (F w') = true → col w.s ≠ col w'.s)
    (hk : ∀ cs, (∀ c ∈ cs, CmOk F (w :: r) col c) → k cs = false) : ∀ (cs : List Cm) (S O : List ℕ) (Q : List Cm),
    (∀ c ∈ cs, CmOk F r col c) → (∀ c ∈ Q, CmOk F (w :: r) col c) → (∀ e ∈ S, ∃ w' ∈ w :: r, F w' = e ∧ col w'.s = col w.s) →
    (∀ e ∈ O, ∃ w' ∈ w :: r, F w' = e ∧ col w'.s = 1 - col w.s) → join k (F w) cs S O Q = false := by
  intro cs
  induction cs with
  | nil =>
    intro S O Q _ hQ hS hO
    refine hk _ fun c hc => ?_
    simp only [List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact ⟨col w.s, hw1, hS, hO⟩
    · exact hQ c hc
  | cons c cs ih =>
    intro S O Q hcs hQ hS hO
    have hc := hcs c (by simp)
    have hcs' : ∀ c ∈ cs, CmOk F r col c := fun c' h => hcs c' (by simp [h])
    obtain ⟨κ, hκ, ha, hb⟩ := hc
    have e : join k (F w) (c :: cs) S O Q = bif hits (F w) c.a then (bif hits (F w) c.b then true else join k (F w) cs (app c.b S) (app c.a O) Q)
        else (bif hits (F w) c.b then join k (F w) cs (app c.a S) (app c.b O) Q else join k (F w) cs S O (c :: Q)) := by
      change (Bool.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool) (join k (F w) cs S O (c :: Q)) (join k (F w) cs (app c.a S) (app c.b O) Q) (hits (F w) c.b))
        (Bool.rec (motive := fun _ => Bool) (join k (F w) cs (app c.b S) (app c.a O) Q) true (hits (F w) c.b)) (hits (F w) c.a) : Bool) = _
      rw [bR, bR, bR]
    rw [e]
    have hA : hits (F w) c.a = true → κ = 1 - col w.s := by
      intro h
      obtain ⟨x, hx, hhx⟩ := hits_true h
      obtain ⟨w', hw', e1, e2⟩ := ha x hx
      have := hh w' hw' (by rw [e1]; exact hhx)
      omega
    have hB : hits (F w) c.b = true → κ = col w.s := by
      intro h
      obtain ⟨x, hx, hhx⟩ := hits_true h
      obtain ⟨w', hw', e1, e2⟩ := hb x hx
      have := hh w' hw' (by rw [e1]; exact hhx)
      omega
    have up : ∀ {κ' : ℕ} {L : List ℕ}, (∀ e ∈ L, ∃ w' ∈ r, F w' = e ∧ col w'.s = κ') → ∀ e ∈ L, ∃ w' ∈ w :: r, F w' = e ∧ col w'.s = κ' := by
      intro κ' L h e he
      obtain ⟨w', h1, h2⟩ := h e he
      exact ⟨w', by simp [h1], h2⟩
    cases h1 : hits (F w) c.a with
    | true =>
      have k1 := hA h1
      cases h2 : hits (F w) c.b with
      | true => have k2 := hB h2; omega
      | false =>
        simp only [cond_true, cond_false]
        refine ih _ _ _ hcs' hQ ?_ ?_
        · intro e he
          rcases app_mem.1 he with h | h
          · obtain ⟨w', q1, q2, q3⟩ := up hb e h; exact ⟨w', q1, q2, by omega⟩
          · exact hS e h
        · intro e he
          rcases app_mem.1 he with h | h
          · obtain ⟨w', q1, q2, q3⟩ := up ha e h; exact ⟨w', q1, q2, by omega⟩
          · exact hO e h
    | false =>
      cases h2 : hits (F w) c.b with
      | true =>
        have k2 := hB h2
        simp only [cond_true, cond_false]
        refine ih _ _ _ hcs' hQ ?_ ?_
        · intro e he
          rcases app_mem.1 he with h | h
          · obtain ⟨w', q1, q2, q3⟩ := up ha e h; exact ⟨w', q1, q2, by omega⟩
          · exact hS e h
        · intro e he
          rcases app_mem.1 he with h | h
          · obtain ⟨w', q1, q2, q3⟩ := up hb e h; exact ⟨w', q1, q2, by omega⟩
          · exact hO e h
      | false =>
        simp only [cond_false]
        refine ih _ _ _ hcs' ?_ hS hO
        intro c' hc'
        simp only [List.mem_cons] at hc'
        rcases hc' with rfl | hc'
        · exact ⟨κ, hκ, up ha, up hb⟩
        · exact hQ c' hc'
lemma bip_aux {l o : ℕ} {col : ℕ → ℕ} : ∀ (v r : List W) (cs : List Cm), (∀ w ∈ v, col w.s ≤ 1) → (∀ c ∈ cs, CmOk (flag false l o) r col c) →
    (∀ w ∈ v, ∀ w' ∈ r, hit (flag false l o w) (flag false l o w') = true → col w.s ≠ col w'.s) →
    v.Pairwise (fun a b => hit (flag false l o b) (flag false l o a) = true → col b.s ≠ col a.s) → bip l o v cs = false := by
  intro v
  induction v with
  | nil => intros; rfl
  | cons w v ih =>
    intro r cs h1 h2 h3 h4
    rw [List.pairwise_cons] at h4
    change join (bip l o v) (flag false l o w) cs [flag false l o w] [] [] = false
    refine join_false (F := flag false l o) (h1 w (by simp)) (h3 w (by simp)) ?_ cs _ _ _ h2 (by simp) ?_ (by simp)
    · intro cs' hcs'
      refine ih (w :: r) cs' (fun x hx => h1 x (by simp [hx])) hcs' ?_ h4.2
      intro x hx w' hw'
      simp only [List.mem_cons] at hw'
      rcases hw' with rfl | hw'
      · exact h4.1 x hx
      · exact h3 x (by simp [hx]) w' hw'
    · intro e he
      simp only [List.mem_singleton] at he
      exact ⟨w, by simp, he.symm, rfl⟩
lemma anyE_false : ∀ {m : List ℕ}, m.Pairwise (fun p q => hit p q = false) → anyE m = false := by
  intro m
  induction m with
  | nil => intro _; rfl
  | cons f t ih =>
    intro h
    rw [List.pairwise_cons] at h
    change (Bool.rec (motive := fun _ => Bool) (anyE t) true (hits f t) : Bool) = false
    rw [bR, hits_false h.1, ih h.2]; rfl
lemma rmF_eq (F : W → ℕ) (f : ℕ) (t : List W) : rmF f (t.map F) = (t.eraseP (fun q => hit f (F q))).map F := by
  induction t with
  | nil => rfl
  | cons x t ih =>
    change (Bool.rec (motive := fun _ => List ℕ) (F x :: rmF f (t.map F)) (t.map F) (hit f (F x)) : List ℕ) = _
    rw [List.eraseP_cons]
    cases h : hit f (F x)
    · simp [ih]
    · simp
lemma eraseP_not {α : Type} {p : α → Bool} {a : α} : ∀ {t : List α}, t.Nodup → a ∈ t → p a = true → (∀ x ∈ t, p x = true → x = a) → a ∉ t.eraseP p := by
  intro t
  induction t with
  | nil => intro _ h; simp at h
  | cons x t ih =>
    intro hn ha hp hx
    rw [List.nodup_cons] at hn
    rw [List.eraseP_cons]
    cases h : p x
    · have hax : a ≠ x := fun e => by rw [← e, hp] at h; simp at h
      simp only [Bool.false_eq_true, if_false, List.mem_cons, not_or]
      simp only [List.mem_cons] at ha
      exact ⟨hax, ih hn.2 (ha.resolve_left hax) hp fun y hy => hx y (by simp [hy])⟩
    · have := hx x (by simp) h
      subst this
      simpa using hn.1
lemma star_false {F : W → ℕ} {a : W} : ∀ {v : List W}, v.Nodup → star (v.map F) = false →
    ∃ p q : W, [p, q].Sublist v ∧ hit (F p) (F q) = true ∧ p ≠ a ∧ q ≠ a := by
  intro v hn hst
  by_contra hno
  push Not at hno
  have bad : ∀ p q : W, [p, q].Sublist v → hit (F p) (F q) = true → p = a ∨ q = a := by
    intro p q h1 h2
    by_cases h : p = a
    · exact Or.inl h
    · exact Or.inr (hno p q h1 h2 h)
  clear hno
  have key : star (v.map F) = true := by
    clear hst
    induction v with
    | nil => rfl
    | cons w t ih =>
      rw [List.nodup_cons] at hn
      have bt : ∀ p q : W, [p, q].Sublist t → hit (F p) (F q) = true → p = a ∨ q = a := fun p q h => bad p q (h.cons w)
      have e : star ((w :: t).map F) = bif hits (F w) (t.map F) then (bif anyE (t.map F) then (bif hits (F w) (rmF (F w) (t.map F)) then false else
          (bif anyE (rmF (F w) (t.map F)) then false else true)) else true) else star (t.map F) := by
        change (Bool.rec (motive := fun _ => Bool) (star (t.map F)) (Bool.rec (motive := fun _ => Bool) true (Bool.rec (motive := fun _ => Bool)
          (Bool.rec (motive := fun _ => Bool) true false (anyE (rmF (F w) (t.map F)))) false (hits (F w) (rmF (F w) (t.map F)))) (anyE (t.map F))) (hits (F w) (t.map F)) : Bool) = _
        rw [bR, bR, bR, bR]
      rw [e]
      have edge : ∀ u : List W, u.Sublist t → a ∉ u → anyE (u.map F) = false := by
        intro u hu ha
        refine anyE_false ?_
        rw [List.pairwise_map, List.pairwise_iff_forall_sublist]
        intro p q hpq
        by_contra hc
        rw [Bool.not_eq_false] at hc
        have hm : ∀ x ∈ [p, q], x ∈ u := fun x hx => hpq.subset hx
        rcases bt p q (hpq.trans hu) hc with rfl | rfl
        · exact ha (hm p (by simp))
        · exact ha (hm q (by simp))
      cases h1 : hits (F w) (t.map F) with
      | false => rw [cond_false]; exact ih hn.2 bt
      | true =>
        rw [cond_true]
        have part : ∀ q ∈ t, hit (F w) (F q) = true → w = a ∨ q = a := fun q hq h => bad w q ((List.singleton_sublist.2 hq).cons_cons w) h
        by_cases hwa : w = a
        · subst hwa
          rw [edge t (List.Sublist.refl t) hn.1]; rfl
        · have pa : ∀ q ∈ t, hit (F w) (F q) = true → q = a := fun q hq h => (part q hq h).resolve_left hwa
          obtain ⟨x, hx, hhx⟩ := hits_true h1
          obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
          have hqa := pa q hq hhx
          subst hqa
          have hna : q ∉ t.eraseP (fun q => hit (F w) (F q)) := eraseP_not hn.2 hq hhx pa
          rw [rmF_eq, edge _ List.eraseP_sublist hna]
          have : hits (F w) ((t.eraseP (fun q => hit (F w) (F q))).map F) = false := by
            refine hits_false fun e he => ?_
            obtain ⟨y, hy, rfl⟩ := List.mem_map.1 he
            by_contra hc
            rw [Bool.not_eq_false] at hc
            have hyt : y ∈ t := List.eraseP_sublist.subset hy
            exact hna (pa y hyt hc ▸ hy)
          rw [this]
          cases anyE (t.map F) <;> rfl
  rw [key] at hst; simp at hst
lemma flk_eq (l o : ℕ) (v : List W) : ∀ k, flk l o v k = k (v.map (flag false l o)) := by
  induction v with
  | nil => intro k; rfl
  | cons w v ih =>
    intro k
    change flk l o v (fun r => k (flag false l o w :: r)) = _
    rw [ih]; rfl
def NK (R : ℕ → ℕ) (m T k' t : ℕ) (S : Finset ℕ) : Prop :=
  (∀ d a b S1 k0, k' = k0 + 1 → Bi R d a b S S1 → Live R m T k0 t S1 → S1.card < S.card) ∧
  ∀ a S1 k0 t0, k' = k0 + 1 → t = t0 + 1 → Un m a S S1 → Live R m T k0 t0 S1 → S1.card ≤ S.card
lemma Rep.nodup {v : List W} {S : Finset ℕ} (h : Rep v S) : v.Nodup := List.Nodup.of_map _ h.1
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma nk_ok {k k' t z : ℕ} {v : List W} {S : Finset ℕ} (hs : StOk P T l k z v S) (hm : Min R m T k' t S)
    (hx : k' ≤ S.card + t) (hst : flk l (wst (pos' t) l v) v star = false) : NK R m T k' t S := by
  rw [flk_eq] at hst
  have hsz := hm.size
  have av : ∀ a : ℕ, a ∈ S → ∃ p q : ℕ, p ∈ S ∧ q ∈ S ∧ p ≠ q ∧ p ≠ a ∧ q ≠ a ∧ Ht I.NN m T (pos' t) S p q := by
    intro a ha
    obtain ⟨wa, hwa, rfl⟩ := hs.rep.mem.1 ha
    obtain ⟨p, q, hpq, hh, h1, h2⟩ := star_false (F := flag false l (wst (pos' t) l v)) (a := wa) hs.rep.nodup hst
    have hp : p ∈ v := hpq.subset (by simp)
    have hq : q ∈ v := hpq.subset (by simp)
    have hne : p ≠ q := by
      have := hs.rep.nodup.sublist hpq
      simpa using this
    refine ⟨p.s, q.s, hs.rep.mem.2 ⟨p, hp, rfl⟩, hs.rep.mem.2 ⟨q, hq, rfl⟩, fun e => hne (hs.rep.inj hp hq e), fun e => h1 (hs.rep.inj hp hwa e),
      fun e => h2 (hs.rep.inj hq hwa e), hit_ht X hs hp hq hh⟩
  have he : ∀ t', pos' t = true ∨ t = t' → pos' t = true ∨ t' = 0 := by
    intro t' h
    rcases h with h | h
    · exact Or.inl h
    · subst h
      rcases Nat.eq_zero_or_pos t with h | h
      · exact Or.inr h
      · exact Or.inl (by simp [pos', h])
  have kb : ∀ d a b S1 k0, k' = k0 + 1 → Bi R d a b S S1 → Live R m T k0 t S1 → ∀ U, S = insert a (insert b U) → S1 = insert (op d a b) U → a ∈ U → b ∉ U → False := by
    rintro d a b S1 k0 rfl hb hl U rfl rfl ha hbU
    have hab := hb.1
    have hfS : op d a b ∉ insert a (insert b U) := fun h => hb.fresh hl hm.2 (sub_C _ _ (by simpa using h))
    have hf : op d a b ∉ U := fun h => hfS (by simp [h])
    have eS : insert a (insert b U) = insert b U := Finset.insert_eq_of_mem (by simp [ha])
    obtain ⟨x, f, h1, h2, h3⟩ := chrom (N := I.NN) (e := pos' t) hl (hb.min hl hm.2).2 (he t (Or.inr rfl))
    rw [Finset.card_insert_of_notMem hf] at h1
    rw [eS, Finset.card_insert_of_notMem hbU] at hx
    obtain ⟨p, q, hp, hq, hpq, hpa, hqa, hh⟩ := av a (by simp)
    have := ht_bi hab (Or.inr rfl) hl hp hq (fun e => absurd e hpa) (fun _ => hbU) (fun e => absurd e hqa) (fun _ => hbU) hh
    have m1 := phi_mem (g := op d a b) hp
    have m2 := phi_mem (g := op d a b) hq
    have hne : (if p = a ∨ p = b then op d a b else p) ≠ (if q = a ∨ q = b then op d a b else q) := by
      simp only [hpa, hqa, false_or]
      have h1' : p = b ∨ p ∈ U := by simp at hp; tauto
      have h2' : q = b ∨ q ∈ U := by simp at hq; tauto
      split_ifs with r s s
      · exact absurd (r.trans s.symm) hpq
      · intro e; exact hf (e ▸ h2'.resolve_left s)
      · intro e; exact hf (e ▸ h1'.resolve_left r)
      · exact hpq
    have k1 := h3 _ m1 _ m2 hne this
    have c1 := h2 _ m1; have c2 := h2 _ m2
    omega
  constructor
  · intro d a b S1 k0 hk' hb hl
    by_contra hc
    obtain ⟨hab, U, e1, e2, hal⟩ := id hb
    have hfS : op d a b ∉ S := fun h => hb.fresh hl (by rw [← hk']; exact hm.2) (sub_C _ _ (by simpa using h))
    have hf : op d a b ∉ U := fun h => hfS (by rw [e1]; simp [h])
    have hs1 := (hb.min hl (by rw [← hk']; exact hm.2)).size.1
    have hcS1 : S1.card = U.card + 1 := by rw [e2, Finset.card_insert_of_notMem hf]
    by_cases ha : a ∈ U
    · by_cases hbU : b ∈ U
      · have : S = U := by rw [e1, Finset.insert_eq_of_mem hbU, Finset.insert_eq_of_mem ha]
        rw [this] at hx; omega
      · exact kb d a b S1 k0 hk' hb hl U e1 e2 ha hbU
    · by_cases hbU : b ∈ U
      · exact kb d b a S1 k0 hk' hb.symm hl U (by rw [e1, Finset.insert_comm]) (by rw [e2, op_comm]) hbU ha
      · have : S.card = U.card + 2 := by
          rw [e1, Finset.card_insert_of_notMem (by simp [hab, ha]), Finset.card_insert_of_notMem hbU]
        omega
  · rintro a S1 k0 t0 rfl rfl hu hl
    by_contra hc
    obtain ⟨U, rfl, rfl⟩ := id hu
    have hf : a ^^^ m ∉ U := fun h => hu.fresh hl hm.2 (sub_C _ _ (by simp [h]))
    have ha : a ∈ U := by
      by_contra ha
      rw [Finset.card_insert_of_notMem hf, Finset.card_insert_of_notMem ha] at hc; omega
    have eS : insert a U = U := Finset.insert_eq_of_mem ha
    obtain ⟨x, f, h1, h2, h3⟩ := chrom (N := I.NN) (e := true) hl (hu.min hl hm.2).2 (Or.inl rfl)
    rw [Finset.card_insert_of_notMem hf] at h1
    rw [eS] at hx
    obtain ⟨p, q, hp, hq, hpq, hpa, hqa, hh⟩ := av a (by simp)
    have hpos : pos' (t0 + 1) = true := by simp [pos']
    rw [hpos] at hh
    have := ht_un hp hq (fun e => absurd e hpa) (fun e => absurd e hqa) hh
    simp only [hpa, hqa, if_false] at this
    have m1 : p ∈ insert (a ^^^ m) U := by rw [eS] at hp; simp [hp]
    have m2 : q ∈ insert (a ^^^ m) U := by rw [eS] at hq; simp [hq]
    have k1 := h3 _ m1 _ m2 hpq this
    have c1 := h2 _ m1; have c2 := h2 _ m2
    omega
lemma tst_sound {k k' t z : ℕ} {v : List W} {S : Finset ℕ} (hs : StOk P T l k z v S) (hm : Min R m T k' t S) (hk : k' ≤ k) :
    ∃ y, (∀ F : ℕ → Bool, tst (pos' t) l (k + 1 - t) v F = F y) ∧ (y = 0 ∨ (y = 1 ∧ v.length + t = k ∧ NK R m T k' t S)) := by
  have hsz := hm.size
  have hcard := hs.rep.card
  have e : ∀ F : ℕ → Bool, tst (pos' t) l (k + 1 - t) v F = bif Nat.beq v.length (k + 1 - t) then (bif rect (pos' t) l (wst (pos' t) l v) v [] then false else F 0) else
      (bif Nat.beq (v.length + 1) (k + 1 - t) then (bif bip l (wst (pos' t) l v) v [] then false else
        (bif flk l (wst (pos' t) l v) v star then F 0 else F 1)) else F 0) := by
    intro F
    change (Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) (F 0) (Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) (F 1) (F 0) (flk l (wst (pos' t) l v) v star)) false
        (bip l (wst (pos' t) l v) v [])) (Nat.beq (v.length + 1) (k + 1 - t)))
      (Bool.rec (motive := fun _ => Bool) (F 0) false (rect (pos' t) l (wst (pos' t) l v) v [])) (Nat.beq v.length (k + 1 - t)) : Bool) = _
    rw [bR, bR, bR, bR, bR]
  cases h1 : Nat.beq v.length (k + 1 - t) with
  | true =>
    have h1' := Nat.eq_of_beq_eq_true h1
    have hr := rect_ok X hs hm hk (by omega)
    exact ⟨0, fun F => by rw [e, h1, hr]; rfl, Or.inl rfl⟩
  | false =>
    cases h2 : Nat.beq (v.length + 1) (k + 1 - t) with
    | false => exact ⟨0, fun F => by rw [e, h1, h2]; rfl, Or.inl rfl⟩
    | true =>
      have h2' := Nat.eq_of_beq_eq_true h2
      have hbip : bip l (wst (pos' t) l v) v [] = false := by
        obtain ⟨x, f, q1, q2, q3⟩ := chrom (N := I.NN) (e := pos' t) hm.1 hm.2 (by
          rcases Nat.eq_zero_or_pos t with h | h
          · exact Or.inr h
          · exact Or.inl (by simp [pos', h]))
        refine bip_aux (col := f) v [] [] ?_ (by simp) (by simp) ?_
        · intro w hw
          have := q2 w.s (hs.rep.mem.2 ⟨w, hw, rfl⟩); omega
        · have hnd : v.Pairwise (fun a b => a.s ≠ b.s) := List.pairwise_map.1 hs.rep.1
          refine hnd.imp_of_mem fun {a b} ha hb hab hh => ?_
          exact q3 b.s (hs.rep.mem.2 ⟨b, hb, rfl⟩) a.s (hs.rep.mem.2 ⟨a, ha, rfl⟩) (Ne.symm hab) (hit_ht X hs hb ha hh)
      cases h3 : flk l (wst (pos' t) l v) v star with
      | true => exact ⟨0, fun F => by rw [e, h1, h2, hbip, h3]; rfl, Or.inl rfl⟩
      | false => exact ⟨1, fun F => by rw [e, h1, h2, hbip, h3]; rfl, Or.inr ⟨rfl, by omega, nk_ok X hs hm (by omega) h3⟩⟩
lemma cv_ok {t k k' z : ℕ} {v : List W} {S : Finset ℕ} {b : Bool} (hs : StOk P T l k z v S) (hl : Live R m T k' t S)
    (h : cv (pos' t) l v b = false) : b = false := by
  have hcov : Nat.beq (cov (pos' t) l v) l = true := by
    rw [Nat.beq_eq]
    apply Nat.eq_of_testBit_eq; intro i
    cases hli : l.testBit i with
    | false =>
      by_contra hc
      obtain ⟨w, _, hw⟩ := (cov_bit _ _ _ _).1 (by simpa using hc)
      rw [sp_bit, hli] at hw; simp at hw
    | true =>
      rw [cov_bit]
      obtain ⟨⟨m1, m2, t1, t2⟩, _⟩ := X.lg i hli
      obtain ⟨w, hw, hs1⟩ := hl.cov m1 m2 t1 t2
      obtain ⟨w', hw', rfl⟩ := hs.rep.mem.1 hw
      exact ⟨w', hw', by rw [sp_bit, hli, hs1]; rfl⟩
  simp only [cv, cvC, bR, hcov, cond_true] at h
  cases hp : pos' t <;> rw [hp] at h <;> simpa using h
end sound
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma gate_sound {f : ℕ → List W → Bool} {d : Bool} {e n z t k k' : ℕ} {v : List W} {S S' : Finset ℕ} {a c : W} {d' : Bool}
    (hs : StOk P T l (k + 1) z v S) (hm : Min R m T (k' + 1) t S) (hk : k' ≤ k) (hd : d = pos' t) (hn : n = v.length)
    (hSe : S'.card ≤ e) (hb : Bi R d' a.s c.s S S') (hl : Live R m T k' t S') (ha : a ∈ v) (hc : c ∈ v)
    (hp : pair (modeF n e (mid f m g e (Nat.pred n) z v)) (mkx d l (wst d l v) a) (mkx d l (wst d l v) c) = false) :
    ∃ z' r, f z' r = false ∧ StOk P T l k z' r S' ∧ ∀ w ∈ r, w = opW d' a c ∨ w ∈ v := by
  subst hd hn
  have hmin := hb.min hl hm.2
  have hpos := hl.pos
  have hfr := hb.fresh hl hm.2
  have hosS : ∀ w ∈ v, w.s ≠ (opW d' a c).s := fun w hw e => hfr (by
    rw [← opW_s, ← e]; exact sub_C _ _ (by simpa using hs.rep.mem.2 ⟨w, hw, rfl⟩))
  have ho0 : (opW d' a c).s ≠ 0 := fun e => hfr (by rw [← opW_s, e]; simp [C])
  have ho1 : (opW d' a c).s ≠ m := fun e => hfr (by rw [← opW_s, e]; simp [C])
  obtain ⟨r0, hr0, hins⟩ := ins_spec (opW d' a c) v hosS
  obtain ⟨s1, s2, s3, s4⟩ := shape_all hosS hr0 hs.rep.1 ha hc hb.1
  have hp := pair_false hp d'
  generalize hoa : dfc (pos' t) d' l (wst (pos' t) l v) a c = da at hp
  generalize hoc : dfc (pos' t) d' l (wst (pos' t) l v) c a = dc at hp
  have filt : ∀ {x y : W}, (∀ i, (Nat.land (sp (pos' t) l x.s) (wst (pos' t) l v)).testBit i = true → bif d' then y.s.testBit (I.NN + i) = false else y.s.testBit i = true) →
      dfc (pos' t) d' l (wst (pos' t) l v) x y = 0 := by
    intro x y hu
    unfold dfc
    generalize Nat.land (sp (pos' t) l x.s) (wst (pos' t) l v) = u at *
    cases d'
    · simp only [Bool.cond_false, nl, nx] at hu ⊢
      apply Nat.eq_of_testBit_eq; intro i
      have := hu i
      rw [Nat.testBit_xor, Nat.testBit_and]; cases h1 : u.testBit i <;> simp_all
    · simp only [Bool.cond_true, nl, nsr] at hu ⊢
      apply Nat.eq_of_testBit_eq; intro i
      have := hu i
      rw [Nat.testBit_and, Nat.testBit_shiftRight]; cases h1 : u.testBit i <;> simp_all
  have fa : a.s ∉ S' → da = 0 := fun h => by
    rw [← hoa]; exact filt fun i hi => drop_ok X hs.rep hb hl ha h hi
  have fc : c.s ∉ S' → dc = 0 := fun h => by
    rw [← hoc]; exact filt fun i hi => drop_ok X hs.rep hb.symm hl hc h hi
  have b0 : ∀ {q : ℕ}, q = 0 → Nat.beq q 0 = true := fun h => by rw [h]; rfl
  have hput : ∀ h, put m (opW d' a c).s (opW d' a c).a (opW d' a c).b v h = h r0 := fun h => by
    rw [put_eq (by cases d' <;> rfl) (by cases d' <;> rfl) ho0 ho1, hins]
  have hv2 : 2 ≤ v.length := by
    rw [← hs.rep.card]
    have : ({a.s, c.s} : Finset ℕ) ⊆ S := by
      intro x hx; simp at hx; rcases hx with rfl | rfl; exacts [hb.sub.1, hb.sub.2.1]
    have h2 := Finset.card_le_card this
    rwa [Finset.card_pair hb.1] at h2
  have hpr : Nat.pred v.length + 1 = v.length := by simp [Nat.pred_eq_sub_one]; omega
  have main : ∀ {ka kc : Bool} {r : List W}, ka = decide (a.s ∈ S') → kc = decide (c.s ∈ S') → Shape (opW d' a c) a c v ka kc r →
      r.length = S'.card ∧ StOk P T l k (z + (a.c &&& c.c) - (opW d' a c).c - (bif ka then a.c else 0) - (bif kc then c.c else 0)) r S' ∧
      ∀ w ∈ r, w = opW d' a c ∨ w ∈ v := by
    intro ka kc r h1 h2 h3
    have := (bi_st X hs hm hk hb hl ha hc h1 h2 h3).1
    exact ⟨this.rep.card.symm, this, fun w hw => h3.mem hw⟩
  have hguard : Nat.beq (Nat.land (z + (a.c &&& c.c) - (opW d' a c).c) g) g = true := by
    by_cases q1 : a.s ∈ S' <;> by_cases q2 : c.s ∈ S'
    · exact (bi_st X hs hm hk hb hl ha hc (by simp [q1]) (by simp [q2]) s4).2
    · exact (bi_st X hs hm hk hb hl ha hc (by simp [q1]) (by simp [q2]) s2).2
    · exact (bi_st X hs hm hk hb hl ha hc (by simp [q1]) (by simp [q2]) s3).2
    · exact (bi_st X hs hm hk hb hl ha hc (by simp [q1]) (by simp [q2]) s1).2
  have fin : ∀ {z' : ℕ} {r : List W} {mk : (List W → Bool) → Bool}, (∀ h, mk h = h r) → StOk P T l k z' r S' → (∀ w ∈ r, w = opW d' a c ∨ w ∈ v) →
      child f g mk z' = false → ∃ z' r, f z' r = false ∧ StOk P T l k z' r S' ∧ ∀ w ∈ r, w = opW d' a c ∨ w ∈ v :=
    fun {z' r mk} h1 h2 h3 h4 => ⟨z', r, child_sound X h1 h2 hmin hk h4, h2, h3⟩
  by_cases q1 : a.s ∈ S' <;> by_cases q2 : c.s ∈ S'
  · obtain ⟨c1, c3, c4⟩ := main (by simp [q1]) (by simp [q2]) s4
    have hlen := s4.len; simp at hlen
    have hmid := mid_false (modeF_false hp (fun h => by omega) (fun h => by omega)) hguard
    exact fin hput c3 c4 ((kids_false hmid).2.2.2 (by omega))
  · obtain ⟨c1, c3, c4⟩ := main (by simp [q1]) (by simp [q2]) s2
    have hlen := s2.len; simp only [Bool.cond_true, Bool.cond_false] at hlen
    have hmid := mid_false (modeF_false hp (fun h => by omega) (fun h => Or.inr (fc q2))) hguard
    exact fin (fun h => by rw [hput, rm_eq]) (by simpa using c3) c4 ((kids_false hmid).2.1 (b0 (fc q2)) (by omega))
  · obtain ⟨c1, c3, c4⟩ := main (by simp [q1]) (by simp [q2]) s3
    have hlen := s3.len; simp only [Bool.cond_true, Bool.cond_false] at hlen
    have hmid := mid_false (modeF_false hp (fun h => by omega) (fun h => Or.inl (fa q1))) hguard
    exact fin (fun h => by rw [hput, rm_eq]) (by simpa using c3) c4 ((kids_false hmid).2.2.1 (b0 (fa q1)) (by omega))
  · obtain ⟨c1, c3, c4⟩ := main (by simp [q1]) (by simp [q2]) s1
    have hlen := s1.len; simp only [Bool.cond_false] at hlen
    have hmid := mid_false (modeF_false hp (fun h => ⟨fa q1, fc q2⟩) (fun h => Or.inl (fa q1))) hguard
    exact fin (fun h => by rw [hput, rm_eq]) (by simpa using c3) c4 ((kids_false hmid).1 (b0 (fa q1)) (b0 (fc q2)))
end sound
def notW (m : ℕ) (a : W) : W := ⟨a.s ^^^ m, a.b, a.a, a.c, 0⟩
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma un_st {k k' t z : ℕ} {v r : List W} {S S' : Finset ℕ} {a : W} {ka : Bool}
    (hs : StOk P T l (k + 1) z v S) (hm : Min R m T (k' + 1) (t + 1) S) (hk : k' ≤ k) (hb : Un m a.s S S')
    (hl : Live R m T k' t S') (ha : a ∈ v) (hka : ka = decide (a.s ∈ S'))
    (hsh : bif ka then r.Perm (notW m a :: v) else (a :: r).Perm (notW m a :: v)) :
    StOk P T l k (z - a.c - (bif ka then a.c else 0)) r S' := by
  obtain ⟨b, hb15, hcl, hz⟩ := hs.bud
  have hle := cnt_le X hs.rep hs.wok hcl hm (by omega)
  have hfr := hb.fresh hl hm.2
  have hfS : a.s ^^^ m ∉ S := fun h => hfr (sub_C _ _ (by simpa using h))
  have wa := hs.wok a ha
  have haS : a.s ∈ S := hb.sub.1
  have wo : WOk P (notW m a) := by
    refine ⟨wa.pb, wa.pa, by rw [Nat.or_comm]; exact wa.ec, fun j hj h => ?_, fun j hj h => ?_⟩
    · change (a.s ^^^ m) &&& _ = _
      rw [and_neg (X.hP j hj).1, wa.cb j hj h]; simp
    · change (a.s ^^^ m) &&& _ = _
      rw [and_neg (X.hP j hj).1, wa.ca j hj h]; simp
  have hov : ((notW m a :: v).map W.s).Nodup := by
    simp only [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => hfS ?_, hs.rep.1⟩
    rw [← hs.rep.2]; simpa [notW] using hm
  have hov2 : ∀ x, x ∈ (notW m a :: v).map W.s ↔ x = a.s ^^^ m ∨ x ∈ S := fun x => by
    rw [← hs.rep.2]; simp [notW]
  have hS' : ∀ x, x ∈ S' ↔ x = a.s ^^^ m ∨ (x ∈ S ∧ (x = a.s → ka = true)) := by
    intro x
    obtain ⟨U, e1, e2⟩ := hb
    rw [e2, Finset.mem_insert]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · refine Or.inr ⟨by rw [e1]; simp [h], ?_⟩
        rintro rfl; rw [hka, e2]; simp [h]
    · rintro (h | ⟨h, f1⟩)
      · exact Or.inl h
      · rw [e1] at h; simp only [Finset.mem_insert] at h
        rcases h with h | h
        · have := f1 h; rw [hka, decide_eq_true_eq, e2, Finset.mem_insert] at this; rw [h]; exact this
        · exact Or.inr h
  have hne : a.s ≠ a.s ^^^ m := fun e => hfS (e ▸ haS)
  have hrep : Rep r S' := by
    cases hkk : ka with
    | true =>
      rw [hkk] at hsh hS'
      have hn := (hsh.map W.s).nodup_iff.2 hov
      refine ⟨hn, Finset.ext fun x => ?_⟩
      rw [List.mem_toFinset, (hsh.map W.s).mem_iff, hov2, hS']; simp
    | false =>
      rw [hkk] at hsh hS'
      have hn := (hsh.map W.s).nodup_iff.2 hov
      simp only [List.map_cons, List.nodup_cons] at hn
      refine ⟨hn.2, Finset.ext fun x => ?_⟩
      have hx := (hsh.map W.s).mem_iff (a := x)
      rw [hov2] at hx; simp only [List.map_cons, List.mem_cons] at hx
      rw [List.mem_toFinset, hS']
      constructor
      · intro h1
        rcases hx.1 (Or.inr h1) with e | e
        · exact Or.inl e
        · exact Or.inr ⟨e, fun e => absurd (e ▸ h1) hn.1⟩
      · rintro (e | ⟨e, f1⟩)
        · exact (hx.2 (Or.inl e)).resolve_left fun e' => hne (e'.symm.trans e)
        · exact (hx.2 (Or.inr e)).resolve_left fun e' => by simpa using f1 e'
  have hmem : ∀ w ∈ r, w = notW m a ∨ w ∈ v := by
    intro w hw
    have : w ∈ notW m a :: v := by
      cases hkk : ka <;> rw [hkk] at hsh
      · exact List.Perm.subset hsh (by simp [hw])
      · exact List.Perm.subset hsh hw
    simpa using this
  have hcnt : ∀ j, cnt r j + (bif ka then 0 else fl a j) = fl a j + cnt v j := by
    intro j
    have ef : fl (notW m a) j = fl a j := rfl
    cases hkk : ka <;> rw [hkk] at hsh
    · have := cnt_perm hsh j; simp only [cnt_cons, ef] at this; simp; omega
    · have := cnt_perm hsh j; simp only [cnt_cons, ef] at this; simp; omega
  have hwok : ∀ w ∈ r, WOk P w := fun w hw => (hmem w hw).elim (fun e => e ▸ wo) (hs.wok w)
  have hgood : ∀ w ∈ r, Good l w.s := fun w hw => by
    rcases hmem w hw with rfl | h
    · have hg := hs.good a ha
      refine ⟨fun i j h h1 h2 => ?_, fun i j h h1 h2 => ?_⟩
      · change (a.s ^^^ m).testBit i = (a.s ^^^ m).testBit j
        rw [Nat.testBit_xor, Nat.testBit_xor, hg.1 i j h h1 h2, (X.lg i h1).1.1, (X.lg j h2).1.1]
      · change (a.s ^^^ m).testBit (I.NN + i) = (a.s ^^^ m).testBit (I.NN + j)
        rw [Nat.testBit_xor, Nat.testBit_xor, hg.2 i j h h1 h2, (X.lg i h1).1.2.1, (X.lg j h2).1.2.1]
    · exact hs.good w h
  let b' : ℕ → ℕ := fun j => b j - fl a j
  have hcl' : Cl P T k b' S' := by
    intro j hj q hq hsol
    have hl1 := hle j hj
    have h2 := cnt_one ha hs.rep.1 j
    simp only [b'] at hq
    by_cases hkill : a.c.testBit (5 * j) = true
    · refine hcl j hj q ?_ (hb.kill (X.hP j hj).1 (wa.cst hj hkill) hsol)
      have : fl a j = 1 := by simp [fl, hkill]
      omega
    · refine hcl j hj (q + 1) ?_ (hb.im (X.hP j hj).1 hsol)
      have e1 : fl a j = 0 := by simp [fl, hkill]
      omega
  have hle' := cnt_le X hrep hwok hcl' (hb.min hl hm.2) hk
  refine ⟨hrep, hwok, hgood, b', fun j hj => ?_, hcl', ?_⟩
  · have := hb15 j hj; simp only [b']; omega
  · have ea : (bif ka then a.c else 0) = pk P.length (fun j => bif ka then fl a j else 0) := by
      cases ka
      · simp [pk]
      · exact fl_pk wa
    have le1 : ∀ j, (bif ka then fl a j else 0) ≤ 1 := fun j => by cases ka <;> simp [fl_le]
    rw [ea, hz]
    conv_lhs => rw [fl_pk wa]
    rw [pk_sub, pk_sub]
    · refine pk_congr fun j hj => ?_
      have q1 := hle j hj; have q2 := hle' j hj; have q3 := cnt_one ha hs.rep.1 j; have q4 := hb15 j hj
      have q5 := hcnt j; have q6 := fl_le a j
      simp only [b'] at q2 ⊢
      cases ka <;> simp at q5 ⊢ <;> omega
    · intro j hj; have := hle j hj; have := le1 j; have := fl_le a j; omega
    · intro j hj; have := hle j hj; have := fl_le a j; omega
end sound
lemma nots_false {f : ℕ → ℕ → List W → Bool} {m g e n z q : ℕ} {v r : List W} (h : nots f m g e n z q v r = false)
    {a : W} (ha : a ∈ r) (hq : a.s + 1 ≠ q) : ins (notW m a) v (fun v =>
      (bif (bif Nat.ble n e then child (f (a.s ^^^ m)) g (rm a.s a.s v) (z - a.c) else false) then true else
      (bif Nat.ble (n + 1) e then child (f (a.s ^^^ m)) g (fun h => h v) (z - a.c - a.c) else false))) = false := by
  induction r with
  | nil => simp at ha
  | cons w r ih =>
    change (Bool.rec (motive := fun _ => Bool) (nots f m g e n z q v r) true (Bool.rec (motive := fun _ => Bool)
      (st (Nat.xor w.s m) (fun s => st (Nat.sub z w.c) (fun z => ins ⟨s, w.b, w.a, w.c, 0⟩ v (fun v =>
        Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false
          (child (f s) g (fun h => h v) (Nat.sub z w.c)) (Nat.ble (Nat.succ n) e)) true
          (Bool.rec (motive := fun _ => Bool) false (child (f s) g (rm w.s w.s v) z) (Nat.ble n e)))))) false (Nat.beq (Nat.succ w.s) q)) : Bool) = false at h
    rw [bR, bR] at h
    simp only [st_eq, bR] at h
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · rw [Bool.eq_false_iff.2 fun h => hq (Nat.eq_of_beq_eq_true h), Bool.cond_false] at h
      cases hh : ins (notW m a) v (fun v =>
        (bif (bif Nat.ble n e then child (f (a.s ^^^ m)) g (rm a.s a.s v) (z - a.c) else false) then true else
        (bif Nat.ble (n + 1) e then child (f (a.s ^^^ m)) g (fun h => h v) (z - a.c - a.c) else false))) with
      | false => rfl
      | true =>
        have h : (bif ins (notW m a) v (fun v =>
          (bif (bif Nat.ble n e then child (f (a.s ^^^ m)) g (rm a.s a.s v) (z - a.c) else false) then true else
          (bif Nat.ble (n + 1) e then child (f (a.s ^^^ m)) g (fun h => h v) (z - a.c - a.c) else false))) then true
          else nots f m g e n z q v r) = false := h
        rw [hh] at h; simp at h
    · refine ih ?_ ha
      revert h
      cases nots f m g e n z q v r <;> simp
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma nots_sound {f : ℕ → ℕ → List W → Bool} {e n z q t k k' : ℕ} {v : List W} {S S' : Finset ℕ} {a : W}
    (hs : StOk P T l (k + 1) z v S) (hm : Min R m T (k' + 1) (t + 1) S) (hk : k' ≤ k) (hn : n = v.length)
    (hSe : S'.card ≤ e) (hb : Un m a.s S S') (hl : Live R m T k' t S') (ha : a ∈ v) (hq : a.s + 1 ≠ q) {rr : List W} (har' : a ∈ rr)
    (hp : nots f m g e n z q v rr = false) : ∃ z' r, f (a.s ^^^ m) z' r = false ∧ StOk P T l k z' r S' ∧ ∀ w ∈ r, w = notW m a ∨ w ∈ v := by
  subst hn
  have hmin := hb.min hl hm.2
  have hfr := hb.fresh hl hm.2
  have hosS : ∀ w ∈ v, w.s ≠ (notW m a).s := fun w hw e => hfr (by
    change a.s ^^^ m ∈ _
    have : w.s = a.s ^^^ m := e
    rw [← this]; exact sub_C _ _ (by simpa using hs.rep.mem.2 ⟨w, hw, rfl⟩))
  obtain ⟨r0, hr0, hins⟩ := ins_spec (notW m a) v hosS
  have h := nots_false hp har' hq
  rw [hins] at h
  have hl0 : r0.length = v.length + 1 := by rw [hr0.length_eq]; simp
  have hnd : (r0.map W.s).Nodup := by
    refine (hr0.map W.s).nodup_iff.2 ?_
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and]
    exact ⟨fun w hw => hosS w hw, hs.rep.1⟩
  have har : a ∈ r0 := hr0.symm.subset (by simp [ha])
  have hmem : ∀ w ∈ r0, w = notW m a ∨ w ∈ v := fun w hw => by simpa using hr0.subset hw
  by_cases q1 : a.s ∈ S'
  · have hst := un_st X hs hm hk hb hl ha (ka := true) (by simp [q1]) hr0
    have hc := hst.rep.card
    have hb1 : Nat.ble (v.length + 1) e = true := Nat.ble_eq_true_of_le (by omega)
    rw [hb1] at h
    have h : child (f (a.s ^^^ m)) g (fun h => h r0) (z - a.c - a.c) = false := by
      revert h; simp only [Bool.cond_true]
      cases child (f (a.s ^^^ m)) g (fun h => h r0) (z - a.c - a.c) <;> simp
    exact ⟨_, _, child_sound X (fun h => rfl) hst hmin hk h, hst, hmem⟩
  · have hperm : (a :: r0.filter (fun w => !(Nat.beq w.s a.s || Nat.beq w.s a.s))).Perm (notW m a :: v) := by
      rw [filter1]; exact (filter_perm hnd har).trans hr0
    have hst := un_st X hs hm hk hb hl ha (ka := false) (by simp [q1]) hperm
    simp only [Bool.cond_false, Nat.sub_zero] at hst
    have hc := hst.rep.card
    have hlen := hperm.length_eq
    simp only [List.length_cons] at hlen
    have hb1 : Nat.ble v.length e = true := Nat.ble_eq_true_of_le (by omega)
    rw [hb1] at h
    have h : child (f (a.s ^^^ m)) g (rm a.s a.s r0) (z - a.c) = false := by
      revert h; simp only [Bool.cond_true]
      cases child (f (a.s ^^^ m)) g (rm a.s a.s r0) (z - a.c) <;> simp
    exact ⟨_, _, child_sound X (rm_eq _ _ _) hst hmin hk h, hst, fun w hw => hmem w (List.mem_of_mem_filter hw)⟩
end sound
lemma scan_false {p : XW → Bool} {xs : List XW} (h : scan p xs = false) : ∀ c ∈ xs, p c = false := by
  induction xs with
  | nil => simp
  | cons a r ih =>
    change (Bool.rec (motive := fun _ => Bool) (scan p r) true (p a) : Bool) = false at h
    rw [bR] at h
    intro c hc
    simp only [List.mem_cons] at hc
    rcases hc with rfl | hc
    · revert h; cases p c <;> simp
    · refine ih ?_ c hc
      revert h; cases scan p r <;> simp
lemma pairs_false {h : XW → XW → Bool} {xs : List XW} (hp : pairs h xs = false) : xs.Pairwise (fun a c => h a c = false) := by
  induction xs with
  | nil => simp
  | cons a r ih =>
    change (Bool.rec (motive := fun _ => Bool) (pairs h r) true (scan (h a) r) : Bool) = false at hp
    rw [bR] at hp
    rw [List.pairwise_cons]
    constructor
    · apply scan_false; revert hp; cases scan (h a) r <;> simp
    · apply ih; revert hp; cases pairs h r <;> simp
lemma beq_f {x y : ℕ} (h : x ≠ y) : Nat.beq x y = false := Bool.eq_false_iff.2 fun h' => h (Nat.eq_of_beq_eq_true h')
lemma pairsP_false {h : XW → XW → Bool} {xs : List XW} {q : ℕ} {a c : XW} (hp : pairsP q h xs = false) (ha : a ∈ xs) (hq : a.s = q)
    (hc : c ∈ xs) (hcq : c.s ≠ q) : h a c = false := by
  have h1 := scan_false hp a ha
  simp only [bR] at h1
  rw [hq, Nat.beq_refl, Bool.cond_true] at h1
  have h2 := scan_false h1 c hc
  beta_reduce at h2
  rwa [beq_f hcq, Bool.cond_false] at h2
lemma pairsQ_false {h : XW → XW → Bool} {xs : List XW} {q q' : ℕ} {a c : XW} (hp : pairsQ q q' h xs = false) (ha : a ∈ xs) (hq : a.s = q)
    (hc : c ∈ xs) (hcq : c.s = q') : h a c = false := by
  have h1 := scan_false hp a ha
  simp only [bR] at h1
  rw [hq, Nat.beq_refl, Bool.cond_true] at h1
  have h2 := scan_false h1 c hc
  beta_reduce at h2
  rwa [hcq, Nat.beq_refl, Bool.cond_true] at h2
lemma pos_eq (t : ℕ) : pos t = pos' t := by cases t <;> simp [pos, pos']
lemma fr_mem {xs : List XW} {a : XW} (ha : a ∈ xs) (h : a.w.r = 0) : a ∈ fr xs := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    change a ∈ Bool.rec (motive := fun _ => List XW) (fr xs) (x :: fr xs) (Nat.beq x.w.r 0)
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · rw [h]; simp
    · cases Nat.beq x.w.r 0
      · exact ih ha
      · exact List.mem_cons_of_mem _ (ih ha)
lemma fs_mem {xs : List XW} {a : XW} (ha : a ∈ xs) (h : a.w.r ≠ 0) : a ∈ fs xs := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    change a ∈ Bool.rec (motive := fun _ => List XW) (x :: fs xs) (fs xs) (Nat.beq x.w.r 0)
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · rw [beq_f h]; simp
    · cases Nat.beq x.w.r 0
      · exact List.mem_cons_of_mem _ (ih ha)
      · exact ih ha
lemma pairs_any {h : XW → XW → Bool} {xs : List XW} (hp : pairs h xs = false) {a c : XW} (ha : a ∈ xs) (hc : c ∈ xs) (hne : a ≠ c) :
    h a c = false ∨ h c a = false := by
  have hpw := pairs_false hp
  have : Std.Symm (fun a c : XW => h a c = false ∨ h c a = false) := ⟨fun a b h => h.symm⟩
  exact (hpw.imp (S := fun a c => h a c = false ∨ h c a = false) fun h => Or.inl h).forall ha hc hne
lemma pairsN_false {h : XW → XW → Bool} {xs : List XW} (hp : pairsN h xs = false) {a c : XW} (ha : a ∈ xs) (hc : c ∈ xs) (hne : a ≠ c)
    (hr : a.w.r = 0 ∨ c.w.r = 0) : h a c = false ∨ h c a = false := by
  simp only [pairsN, bR] at hp
  cases h1 : pairs h (fr xs) with
  | true => rw [h1] at hp; simp at hp
  | false =>
    rw [h1, cond_false] at hp
    by_cases hra : a.w.r = 0
    · by_cases hrc : c.w.r = 0
      · exact pairs_any h1 (fr_mem ha hra) (fr_mem hc hrc) hne
      · exact Or.inl (scan_false (scan_false hp a (fr_mem ha hra)) c (fs_mem hc hrc))
    · have hrc := hr.resolve_left hra
      exact Or.inr (scan_false (scan_false hp c (fr_mem hc hrc)) a (fs_mem ha hra))
def Cod (R : ℕ → ℕ) (v : List W) : Prop := ∀ w ∈ v, w.r = 0 ∨ w.r = R w.s
def RR (R : ℕ → ℕ) : Prop := ∀ d a b, R a ≠ 0 → R b ≠ 0 → ¬ Al R d a b
lemma opW_r (d : Bool) (a c : W) : (opW d a c).r = 0 := by cases d <;> rfl
lemma mv_false (F : ℕ → ℕ → ℕ → List W → Bool) (l m g k t z : ℕ) (v : List W) (y : ℕ) (h : mv F l m g k t z v y = false) :
    node (F (k - 1) t) (pos' t) l m g (k - t - y) v.length z v pairsN = false ∧
    ∀ s, t = s + 1 → nots (fun q z v => cv (pos' s) l v (tst (pos' s) l (k - s) v (fun y =>
      bif node (F (k - 2) s) (pos' s) l m g (k - 1 - s - y) v.length z v (pairsP q) then true
      else prd s (fun s => nots (fun q' z v => cv (pos' s) l v (tst (pos' s) l (k - 1 - s) v (fun y =>
        node (F (k - 3) s) (pos' s) l m g (k - 2 - s - y) v.length z v (pairsQ q q'))))
        m g (k - 1 - s - y) v.length z (q + 1) v v)))) m g (k - s - y) v.length z 0 v v = false := by
  change (Bool.rec (motive := fun _ => Bool) (prd t (fun s => nots (fun q z v => cv (pos s) l v (tst (pos s) l (k - s) v (fun y =>
      (Bool.rec (motive := fun _ => Bool) (prd s (fun s => nots (fun q' z v => cv (pos s) l v (tst (pos s) l (k - 1 - s) v (fun y =>
        node (F (k - 3) s) (pos s) l m g (k - 2 - s - y) v.length z v (pairsQ q q'))))
        m g (k - 1 - s - y) v.length z (q + 1) v v)) true
        (node (F (k - 2) s) (pos s) l m g (k - 1 - s - y) v.length z v (pairsP q)) : Bool)))) m g (k - s - y) v.length z 0 v v)) true
      (node (F (k - 1) t) (pos t) l m g (k - t - y) v.length z v pairsN) : Bool) = false at h
  simp only [bR, pos_eq] at h
  cases h1 : node (F (k - 1) t) (pos' t) l m g (k - t - y) v.length z v pairsN with
  | true => rw [h1] at h; simp at h
  | false =>
    rw [h1, Bool.cond_false] at h
    refine ⟨rfl, ?_⟩
    rintro s rfl
    exact h
lemma NK.sizeB {m T k k' t : ℕ} {S S1 : Finset ℕ} {d : Bool} {a b n y : ℕ} (hn : S.card = n) (hm : Min R m T (k' + 1) t S) (hk : k' + 1 ≤ k)
    (hb : Bi R d a b S S1) (hl : Live R m T k' t S1) (hy : y = 0 ∨ (y = 1 ∧ n + t = k ∧ NK R m T (k' + 1) t S)) : S1.card ≤ k - t - y := by
  have hs := (hb.min hl hm.2).size.1
  rcases hy with rfl | ⟨rfl, h1, h2⟩
  · omega
  · have := h2.1 d a b S1 k' rfl hb hl; omega
lemma NK.sizeU {m T k k' t : ℕ} {S S1 : Finset ℕ} {a n y : ℕ} (hn : S.card = n) (hm : Min R m T (k' + 1) (t + 1) S) (hk : k' + 1 ≤ k)
    (hb : Un m a S S1) (hl : Live R m T k' t S1) (hy : y = 0 ∨ (y = 1 ∧ n + (t + 1) = k ∧ NK R m T (k' + 1) (t + 1) S)) : S1.card ≤ k - t - y := by
  have hs := (hb.min hl hm.2).size.1
  rcases hy with rfl | ⟨rfl, h1, h2⟩
  · omega
  · have := h2.2 a S1 k' t rfl rfl hb hl; omega
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma node_bi {f : ℕ → List W → Bool} {d : Bool} {e n z t k k' : ℕ} {v : List W} {S S' : Finset ℕ} {x y : ℕ} {d' : Bool}
    {go : (XW → XW → Bool) → List XW → Bool}
    (hs : StOk P T l (k + 1) z v S) (hm : Min R m T (k' + 1) t S) (hk : k' ≤ k) (hd : d = pos' t) (hn : n = v.length)
    (hSe : S'.card ≤ e) (hb : Bi R d' x y S S') (hl : Live R m T k' t S')
    (hgo : ∀ h xs, go h xs = false → ∀ a c : W, a ∈ v → c ∈ v → a.s = x → c.s = y → xs = v.map (mkx d l (wst d l v)) →
      h (mkx d l (wst d l v) a) (mkx d l (wst d l v) c) = false ∨ h (mkx d l (wst d l v) c) (mkx d l (wst d l v) a) = false)
    (hp : node f d l m g e n z v go = false) : ∃ z' r, f z' r = false ∧ StOk P T l k z' r S' ∧ ∀ w ∈ r, (w.s = op d' x y ∧ w.r = 0) ∨ w ∈ v := by
  rw [node_eq] at hp
  obtain ⟨a, ha, rfl⟩ := hs.rep.mem.1 hb.sub.1
  obtain ⟨c, hc, rfl⟩ := hs.rep.mem.1 hb.sub.2.1
  rcases hgo _ _ hp a c ha hc rfl rfl rfl with h | h
  · obtain ⟨z', r, h1, h2, h3⟩ := gate_sound X hs hm hk hd hn hSe hb hl ha hc h
    exact ⟨z', r, h1, h2, fun w hw => (h3 w hw).imp (fun e => ⟨by rw [e, opW_s], by rw [e, opW_r]⟩) id⟩
  · obtain ⟨z', r, h1, h2, h3⟩ := gate_sound X hs hm hk hd hn hSe hb.symm hl hc ha h
    exact ⟨z', r, h1, h2, fun w hw => (h3 w hw).imp (fun e => ⟨by rw [e, opW_s, op_comm], by rw [e, opW_r]⟩) id⟩
lemma mv_sound (hR : RR R) {F : ℕ → ℕ → ℕ → List W → Bool}
    (hF : ∀ (k t z : ℕ) (v : List W) (S : Finset ℕ), F k t z v = false → StOk P T l k z v S → Cod R v → ∀ k' ≤ k, ¬ Min R m T k' t S)
    {k t z y : ℕ} {v : List W} {S : Finset ℕ} (hs : StOk P T l k z v S) (hcod : Cod R v) (hlen : 2 ≤ v.length)
    (h : mv F l m g k t z v y = false) : ∀ k' ≤ k, Min R m T k' t S → (y = 0 ∨ (y = 1 ∧ v.length + t = k ∧ NK R m T k' t S)) → False := by
  intro k' hk hm hy
  obtain ⟨hA, hN⟩ := mv_false F l m g k t z v y h
  have hcard := hs.rep.card
  have codB : ∀ {v r : List W} {o : ℕ}, Cod R v → (∀ w ∈ r, (w.s = o ∧ w.r = 0) ∨ w ∈ v) → Cod R r := by
    intro v r o hv hr w hw
    rcases hr w hw with ⟨_, h⟩ | h
    · exact Or.inl h
    · exact hv w h
  have codU : ∀ {v r : List W} {a : W}, Cod R v → (∀ w ∈ r, w = notW m a ∨ w ∈ v) → Cod R r := by
    intro v r o hv hr w hw
    rcases hr w hw with h | h
    · exact Or.inl (by rw [h]; rfl)
    · exact hv w h
  rcases first_move k' t S hm (by omega) with
    ⟨k0, d, a, b, S1, rfl, hb, hl⟩ | ⟨k0, t0, a, d, c, S1, S2, rfl, rfl, hu, hb, hl⟩ |
    ⟨k0, t0, a, a', d, S1, S2, S3, rfl, rfl, hu, hne, hu', hb, hl⟩
  · obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    obtain ⟨z', r, hf, hst, hmem⟩ := node_bi X hs hm (by omega) rfl rfl (NK.sizeB hcard hm hk hb hl hy) hb hl (fun h xs hp a c ha hc hax hcy hxs => by
      subst hxs
      refine pairsN_false hp (List.mem_map_of_mem ha) (List.mem_map_of_mem hc) ?_ ?_
      · intro e
        have : a.s = c.s := congrArg XW.s e
        exact hb.1 (by rw [← hax, ← hcy, this])
      · by_contra hc'
        push Not at hc'
        obtain ⟨_, U, _, _, hal⟩ := hb
        have h1 : a.r = R a.s := (hcod a ha).resolve_left hc'.1
        have h2 : c.r = R c.s := (hcod c hc).resolve_left hc'.2
        have g1 : a.r ≠ 0 := hc'.1
        have g2 : c.r ≠ 0 := hc'.2
        rw [← hax, ← hcy] at hal
        exact hR _ _ _ (by rw [← h1]; exact g1) (by rw [← h2]; exact g2) hal) hA
    exact hF _ _ _ _ _ hf hst (codB hcod hmem) k0 (by simpa using hk) (hb.min hl hm.2)
  · obtain ⟨k, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    have hl1 := hb.live hl
    obtain ⟨wa, hwa, rfl⟩ := hs.rep.mem.1 hu.sub.1
    have h2 := hN t0 rfl
    obtain ⟨z1, r1, hf1, hst1, hmem1⟩ := nots_sound X (k := k + 1) hs hm (by omega) rfl (NK.sizeU hcard hm hk hu hl1 hy) hu hl1 hwa (by omega) hwa h2
    have hm1 := hu.min hl1 hm.2
    have hf1 := cv_ok X hst1 hl1 hf1
    obtain ⟨y1, hF1, hy1⟩ := tst_sound X hst1 hm1 (by omega)
    have hf1 := (hF1 _).symm.trans hf1
    beta_reduce at hf1
    rw [Bool.cond_eq_ite] at hf1
    split_ifs at hf1 with hf2
    rw [Bool.not_eq_true] at hf2
    obtain ⟨z', r, hf, hst, hmem⟩ := node_bi X hst1 hm1 (by omega) rfl rfl (NK.sizeB hst1.rep.card hm1 (by omega) hb hl hy1) hb hl (fun h xs hp a c ha hc hax hcy hxs => by
      subst hxs
      exact Or.inl (pairsP_false hp (List.mem_map_of_mem ha) hax (List.mem_map_of_mem hc) (fun e => hb.1 (by rw [← hcy, ← e]; rfl)))) hf2
    exact hF _ _ _ _ _ hf hst (codB (codU hcod hmem1) hmem) k0 (by simpa using hk) (hb.min hl hm1.2)
  · obtain ⟨k, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
    have hl1 := hb.live hl
    have hl2 := hu'.live hl1
    obtain ⟨wa, hwa, rfl⟩ := hs.rep.mem.1 hu.sub.1
    have h2 := hN (t0 + 1) rfl
    obtain ⟨z1, r1, hf1, hst1, hmem1⟩ := nots_sound X (k := k + 2) hs hm (by omega) rfl (NK.sizeU hcard hm hk hu hl2 hy) hu hl2 hwa (by omega) hwa h2
    have hm1 := hu.min hl2 hm.2
    have hf1 := cv_ok X hst1 hl2 hf1
    obtain ⟨y1, hF1, hy1⟩ := tst_sound X hst1 hm1 (by omega)
    have hf1 := (hF1 _).symm.trans hf1
    beta_reduce at hf1
    rw [Bool.cond_eq_ite] at hf1
    split_ifs at hf1 with hf2
    obtain ⟨wa', hwa', rfl⟩ := hst1.rep.mem.1 hu'.sub.1
    obtain ⟨z2, r2, hf3, hst2, hmem2⟩ := nots_sound X (k := k + 1) hst1 hm1 (by omega) rfl (NK.sizeU hst1.rep.card hm1 (by omega) hu' hl1 hy1) hu' hl1 hwa' (by omega) hwa' hf1
    have hm2 := hu'.min hl1 hm1.2
    have hf3 := cv_ok X hst2 hl1 hf3
    obtain ⟨y2, hF3, hy2⟩ := tst_sound X hst2 hm2 (by omega)
    have hf3 := (hF3 _).symm.trans hf3
    beta_reduce at hf3
    obtain ⟨z', r, hf, hst, hmem⟩ := node_bi X hst2 hm2 (by omega) rfl rfl (NK.sizeB hst2.rep.card hm2 (by omega) hb hl hy2) hb hl (fun h xs hp a c ha hc hax hcy hxs => by
      subst hxs
      exact Or.inl (pairsQ_false hp (List.mem_map_of_mem ha) hax (List.mem_map_of_mem hc) hcy)) hf3
    exact hF _ _ _ _ _ hf hst (codB (codU (codU hcod hmem1) hmem2) hmem) k0 (by simpa using hk) (hb.min hl hm2.2)
theorem look_sound (hR : RR R) : ∀ (fuel k t z : ℕ) (v : List W) (S : Finset ℕ), look l m g fuel k t z v = false → StOk P T l k z v S → Cod R v →
    ∀ k' ≤ k, ¬ Min R m T k' t S := by
  intro fuel
  induction fuel with
  | zero => intro k t z v S h; simp [look, lookC] at h
  | succ fuel ih =>
    intro k t z v S h hs hcod k' hk hm
    change (Bool.rec (motive := fun _ => Bool) (tst (pos t) l (k + 1 - t) v (fun y => mv (look l m g fuel) l m g k t z v y)) true (Nat.ble v.length 1) : Bool) = false at h
    rw [bR, pos_eq] at h
    cases h0 : Nat.ble v.length 1 with
    | true => rw [h0] at h; simp at h
    | false =>
      rw [h0, cond_false] at h
      have hlen : 2 ≤ v.length := by
        by_contra hc
        rw [Nat.ble_eq_true_of_le (by omega)] at h0; simp at h0
      obtain ⟨y, hFy, hyk⟩ := tst_sound X hs hm hk
      have hy := (hFy _).symm.trans h
      beta_reduce at hy
      exact mv_sound X hR ih hs hcod hlen hy k' hk hm hyk
end sound
lemma Live.W {m T k t : ℕ} {S : Finset ℕ} {Q : Set ℕ} (hl : Live R m T k t S) (hQ : (S : Set ℕ) ⊆ Q) : Sol Z0 m T k Q := hl.sol.mono le_rfl hQ
lemma front {m T : ℕ} (hR : ∀ d a b, (R a = 0 ∨ R b = 0) → Al R d a b) {k t : ℕ} {S : Finset ℕ} (hl : Live Z0 m T k t S)
    (hm : ∀ q < k, ¬ Sol Z0 m T q (C m ({x | R x ≠ 0} ∪ (S : Set ℕ)))) :
    Live R m T k t S ∨ ∃ k0 d a b S1, k = k0 + 1 ∧ R a ≠ 0 ∧ R b ≠ 0 ∧ Bi Z0 d a b S S1 ∧ Live Z0 m T k0 t S1 := by
  induction hl with
  | stop => exact Or.inl .stop
  | @un k t a U hl ih =>
    set Q : Set ℕ := {x | R x ≠ 0} with hQ
    have hfr : a ^^^ m ∉ C m (Q ∪ ((insert a U : Finset ℕ) : Set ℕ)) := by
      intro hg
      apply hm k (by omega)
      refine hl.sol.mono le_rfl fun x hx => ?_
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx
      rcases hx with rfl | hx
      · exact hg
      · exact Or.inl (Or.inr (by simp [hx]))
    have hfU : a ^^^ m ∉ U := fun h => hfr (Or.inl (Or.inr (by simp [h])))
    have hfR : R (a ^^^ m) = 0 := by
      by_contra h; exact hfr (Or.inl (Or.inl h))
    have hm' : ∀ q < k, ¬ Sol Z0 m T q (C m (Q ∪ ((insert (a ^^^ m) U : Finset ℕ) : Set ℕ))) := by
      intro q hq hs
      refine hm (q + 1) (by omega) (.un (a := a) (Or.inl (Or.inr (by simp))) (hs.mono le_rfl ?_))
      rintro x ((hx | hx) | hx)
      · exact Or.inr (Or.inl (Or.inl hx))
      · simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx
        rcases hx with rfl | hx
        · exact Or.inl rfl
        · exact Or.inr (Or.inl (Or.inr (by simp [hx])))
      · exact Or.inr (Or.inr hx)
    rcases ih hm' with h | ⟨k0, d, x, y, S1, rfl, hx, hy, ⟨hxy, V, e1, rfl, hal⟩, hl1⟩
    · exact Or.inl (.un h)
    · have nx : x ≠ a ^^^ m := fun e => hx (e ▸ hfR)
      have ny : y ≠ a ^^^ m := fun e => hy (e ▸ hfR)
      have hmV : a ^^^ m ∈ V := by
        have : a ^^^ m ∈ insert x (insert y V) := by rw [← e1]; simp
        simp at this
        rcases this with h | h | h
        · exact absurd h.symm nx
        · exact absurd h.symm ny
        · exact h
      have eU : U = insert x (insert y (V.erase (a ^^^ m))) := by
        ext z
        by_cases hz : z = a ^^^ m
        · subst hz
          simp [hfU, Ne.symm nx, Ne.symm ny]
        · have : z ∈ insert (a ^^^ m) U ↔ z ∈ insert x (insert y V) := by rw [e1]
          simp only [Finset.mem_insert, hz, false_or, Finset.mem_erase, ne_eq, not_false_eq_true, true_and] at this ⊢
          exact this
      refine Or.inr ⟨k0 + 1, d, x, y, insert a (insert (op d x y) (V.erase (a ^^^ m))), rfl, hx, hy,
        ⟨hxy, insert a (V.erase (a ^^^ m)), ?_, ?_, hal⟩, ?_⟩
      · rw [eU]; ext z; simp only [Finset.mem_insert]; tauto
      · ext z; simp only [Finset.mem_insert]; tauto
      · refine .un ?_
        have : insert (a ^^^ m) (insert (op d x y) (V.erase (a ^^^ m))) = insert (op d x y) V := by
          rw [Finset.insert_comm, Finset.insert_erase hmV]
        rw [this]; exact hl1
  | @bi k t d0 a b U hab hal0 hl ih =>
    set Q : Set ℕ := {x | R x ≠ 0} with hQ
    have hb0 : Bi Z0 d0 a b (insert a (insert b U)) (insert (op d0 a b) U) := ⟨hab, U, rfl, rfl, hal0⟩
    by_cases hW : R a ≠ 0 ∧ R b ≠ 0
    · exact Or.inr ⟨k, d0, a, b, _, rfl, hW.1, hW.2, hb0, hl⟩
    have hal : Al R d0 a b := hR _ _ _ (by
      by_contra hc; push Not at hc; exact hW hc)
    have hfr : op d0 a b ∉ C m (Q ∪ ((insert a (insert b U) : Finset ℕ) : Set ℕ)) := by
      intro hg
      apply hm k (by omega)
      refine hl.sol.mono le_rfl fun x hx => ?_
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx
      rcases hx with rfl | hx
      · exact hg
      · exact Or.inl (Or.inr (by simp [hx]))
    have hfU : op d0 a b ∉ U := fun h => hfr (Or.inl (Or.inr (by simp [h])))
    have hfa : op d0 a b ≠ a := fun h => hfr (Or.inl (Or.inr (by simp [h])))
    have hfb : op d0 a b ≠ b := fun h => hfr (Or.inl (Or.inr (by simp [h])))
    have hfR : R (op d0 a b) = 0 := by
      by_contra h; exact hfr (Or.inl (Or.inl h))
    have hm' : ∀ q < k, ¬ Sol Z0 m T q (C m (Q ∪ ((insert (op d0 a b) U : Finset ℕ) : Set ℕ))) := by
      intro q hq hs
      refine hm (q + 1) (by omega) (.bi (d := d0) (a := a) (b := b) (Or.inl (Or.inr (by simp))) (Or.inl (Or.inr (by simp))) (al0 _ _ _) (hs.mono le_rfl ?_))
      rintro x ((hx | hx) | hx)
      · exact Or.inr (Or.inl (Or.inl hx))
      · simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx
        rcases hx with rfl | hx
        · exact Or.inl rfl
        · exact Or.inr (Or.inl (Or.inr (by simp [hx])))
      · exact Or.inr (Or.inr hx)
    rcases ih hm' with h | ⟨k0, d, x, y, S1, rfl, hx, hy, ⟨hxy, V, e1, rfl, hal'⟩, hl1⟩
    · exact Or.inl (.bi hab hal h)
    · set o := op d0 a b with ho
      have nx : x ≠ o := fun e => hx (e ▸ hfR)
      have ny : y ≠ o := fun e => hy (e ▸ hfR)
      have hmV : o ∈ V := by
        have : o ∈ insert x (insert y V) := by rw [← e1]; simp
        simp at this
        rcases this with h | h | h
        · exact absurd h.symm nx
        · exact absurd h.symm ny
        · exact h
      have eU : U = insert x (insert y (V.erase o)) := by
        ext z
        by_cases hz : z = o
        · subst hz
          simp [hfU, Ne.symm nx, Ne.symm ny]
        · have : z ∈ insert o U ↔ z ∈ insert x (insert y V) := by rw [e1]
          simp only [Finset.mem_insert, hz, false_or, Finset.mem_erase, ne_eq, not_false_eq_true, true_and] at this ⊢
          exact this
      refine Or.inr ⟨k0 + 1, d, x, y, insert a (insert b (insert (op d x y) (V.erase o))), rfl, hx, hy,
        ⟨hxy, insert a (insert b (V.erase o)), ?_, ?_, hal'⟩, ?_⟩
      · rw [eU]; ext z; simp only [Finset.mem_insert]
        constructor <;> (rintro (h | h | h | h | h) <;> simp only [h, true_or, or_true])
      · ext z; simp only [Finset.mem_insert]
        constructor <;> (rintro (h | h | h | h) <;> simp only [h, true_or, or_true])
      · refine .bi hab hal0 ?_
        have : insert (op d0 a b) (insert (op d x y) (V.erase o)) = insert (op d x y) V := by
          rw [Finset.insert_comm, ← ho, Finset.insert_erase hmV]
        rw [this]; exact hl1
lemma Min.Z {m T k t : ℕ} {S : Finset ℕ} (h : Min R m T k t S) : Min Z0 m T k t S := ⟨h.1.rel fun d a b _ => al0 d a b, h.2⟩
lemma NK.toR {m T k t : ℕ} {S : Finset ℕ} (h : NK Z0 m T k t S) : NK R m T k t S :=
  ⟨fun d a b S1 k0 e hb hl => h.1 d a b S1 k0 e (hb.rel fun d a b _ => al0 d a b) (hl.rel fun d a b _ => al0 d a b),
    fun a S1 k0 t0 e e' hu hl => h.2 a S1 k0 t0 e e' hu (hl.rel fun d a b _ => al0 d a b)⟩
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma one_sound (hR : RR R) (hR2 : ∀ d a b, (R a = 0 ∨ R b = 0) → Al R d a b) {K : ℕ} {f : ℕ → ℕ → ℕ → List W → Bool}
    (hF : ∀ (k t z : ℕ) (v : List W) (S : Finset ℕ), f k t z v = false → StOk P T l k z v S → (∀ w ∈ v, w.r = R w.s) →
      ∀ k' ≤ k, Live Z0 m T k' t S → (∀ q < k', ¬ Sol Z0 m T q (C m ({x | R x ≠ 0} ∪ (S : Set ℕ)))) → False)
    {k t z y : ℕ} {v : List W} {S : Finset ℕ} (hs : StOk P T l k z v S) (hcod : ∀ w ∈ v, w.r = R w.s) (hlen : 2 ≤ v.length)
    {k' : ℕ} (hk : k' ≤ k) (hl : Live Z0 m T k' t S) (hmW : ∀ q < k', ¬ Sol Z0 m T q (C m ({x | R x ≠ 0} ∪ (S : Set ℕ))))
    (hy : y = 0 ∨ (y = 1 ∧ v.length + t = k ∧ NK Z0 m T k' t S))
    (h2 : mv (look l m g K) l m g k t z v y = false)
    (h1 : ∀ a ∈ v, ∀ c ∈ v, a.s ≠ c.s → a.r ≠ 0 → c.r ≠ 0 → ∃ go : (XW → XW → Bool) → List XW → Bool,
      node (f (k - 1) t) (pos' t) l m g (k - t - y) v.length z v go = false ∧
      ∀ h, go h (v.map (mkx (pos' t) l (wst (pos' t) l v))) = false →
        h (mkx (pos' t) l (wst (pos' t) l v) a) (mkx (pos' t) l (wst (pos' t) l v) c) = false ∨
        h (mkx (pos' t) l (wst (pos' t) l v) c) (mkx (pos' t) l (wst (pos' t) l v) a) = false) : False := by
  have hmin : Min Z0 m T k' t S := ⟨hl, fun q hq hs => hmW q hq (hs.mono le_rfl (C_mono Set.subset_union_right))⟩
  have hcard := hs.rep.card
  rcases front hR2 hl hmW with hlR | ⟨k0, d, a, b, S1, rfl, ha, hb', hb, hl1⟩
  · exact mv_sound X hR (look_sound X hR K) hs (fun w hw => Or.inr (hcod w hw)) hlen h2 k' hk ⟨hlR, hmin.2⟩ (hy.imp id fun ⟨q1, q2, q3⟩ => ⟨q1, q2, q3.toR⟩)
  · obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    obtain ⟨wa, hwa, rfl⟩ := hs.rep.mem.1 hb.sub.1
    obtain ⟨wb, hwb, rfl⟩ := hs.rep.mem.1 hb.sub.2.1
    obtain ⟨go, hg1, hg2⟩ := h1 wa hwa wb hwb hb.1 (by rw [hcod wa hwa]; exact ha) (by rw [hcod wb hwb]; exact hb')
    obtain ⟨z', r, hf, hst, hmem⟩ := node_bi X hs hmin (by omega) rfl rfl (NK.sizeB hcard hmin hk hb hl1 hy) hb hl1 (fun h xs hp a c ha hc hax hcy hxs => by
      subst hxs
      rw [hs.rep.inj ha hwa hax, hs.rep.inj hc hwb hcy]
      exact hg2 h hp) hg1
    have hfr : R (op d wa.s wb.s) = 0 := by
      by_contra hne
      refine hmW k0 (by omega) (hl1.sol.mono le_rfl fun x hx => ?_)
      have hx' := hb.sub.2.2 hx
      simp only [Finset.mem_insert] at hx'
      rcases hx' with rfl | hx'
      · exact Or.inl (Or.inl hne)
      · exact Or.inl (Or.inr hx')
    refine hF _ _ _ _ _ hf hst ?_ k0 (by simpa using hk) hl1 ?_
    · intro w hw
      rcases hmem w hw with ⟨e1, e2⟩ | h
      · rw [e1, e2, hfr]
      · exact hcod w h
    · intro q hq hs'
      refine hmW (q + 1) (by omega) (.bi (d := d) (a := wa.s) (b := wb.s) (Or.inl (Or.inr hb.sub.1)) (Or.inl (Or.inr hb.sub.2.1)) (al0 _ _ _) (hs'.mono le_rfl ?_))
      rintro x ((hx | hx) | hx)
      · exact Or.inr (Or.inl (Or.inl hx))
      · have hx' := hb.sub.2.2 hx
        simp only [Finset.mem_insert] at hx'
        rcases hx' with rfl | hx'
        · exact Or.inl rfl
        · exact Or.inr (Or.inl (Or.inr hx'))
      · exact Or.inr (Or.inr hx)
lemma or_false' {a b : Bool} (h : (Bool.rec (motive := fun _ => Bool) b true a : Bool) = false) : a = false ∧ b = false := by
  clear X
  cases a <;> simp_all
theorem look1_sound (hR : RR R) (hR2 : ∀ d a b, (R a = 0 ∨ R b = 0) → Al R d a b) {K : ℕ} : ∀ (fuel k t z : ℕ) (v : List W) (S : Finset ℕ),
    look1 l m g K fuel k t z v = false → StOk P T l k z v S → (∀ w ∈ v, w.r = R w.s) →
      ∀ k' ≤ k, Live Z0 m T k' t S → (∀ q < k', ¬ Sol Z0 m T q (C m ({x | R x ≠ 0} ∪ (S : Set ℕ)))) → False := by
  intro fuel
  induction fuel with
  | zero => intro k t z v S h; simp [look1, look1C] at h
  | succ fuel ih =>
    intro k t z v S h hs hcod k' hk hl hmW
    change (Bool.rec (motive := fun _ => Bool) (tst (pos t) l (k + 1 - t) v (fun y => Bool.rec (motive := fun _ => Bool) (mv (look l m g K) l m g k t z v y) true
        (node (look1 l m g K fuel (k - 1) t) (pos t) l m g (k - t - y) v.length z v pairsS))) true (Nat.ble v.length 1) : Bool) = false at h
    rw [bR, pos_eq] at h
    cases h0 : Nat.ble v.length 1 with
    | true => rw [h0] at h; simp at h
    | false =>
      rw [h0, cond_false] at h
      have hlen : 2 ≤ v.length := by
        by_contra hc
        rw [Nat.ble_eq_true_of_le (by omega)] at h0; simp at h0
      have hmin : Min Z0 m T k' t S := ⟨hl, fun q hq hs => hmW q hq (hs.mono le_rfl (C_mono Set.subset_union_right))⟩
      obtain ⟨y, hFy, hyk⟩ := tst_sound X hs hmin hk
      have hy := (hFy _).symm.trans h
      beta_reduce at hy
      obtain ⟨hy1, hy2⟩ := or_false' X hy
      refine one_sound X hR hR2 ih hs hcod hlen hk hl hmW hyk hy2 fun a ha c hc hne har hcr => ⟨pairsS, hy1, fun h hp => ?_⟩
      exact pairs_any hp (fs_mem (List.mem_map_of_mem ha) har) (fs_mem (List.mem_map_of_mem hc) hcr) (fun e => hne (congrArg XW.s e))
end sound

end engine_ok
def xw (e : ℕ × ℕ) : ℕ := I.rawP.getD e.1 0 ||| I.rawP.getD e.2 0
def rawL (E : List (ℕ × ℕ)) : List ℕ := I.rawP ++ E.map xw
def six : List (ℕ × ℕ) := []
def rawG : List ℕ := rawL six
def FPM : ℕ := 2 ^ 64 - 1
def FULL : ℕ := 2 ^ I.NN - 1
def kz (Z : ℕ) : ℕ := (List.range 6).foldr (fun i x =>
  let a := I.rawP.getD i 0
  let b := Nat.shiftRight a I.NN
  let z0 := if Z.testBit i then Nat.land (Nat.lor a b) FULL else 0
  let z1 := if Z.testBit (i + 6) then Nat.lor (Nat.land (Nat.xor a FULL) FULL) (Nat.land (Nat.xor b FULL) I.AA) else 0
  Nat.lor x (Nat.lor z0 z1)) 0
def lz (Z : ℕ) : ℕ := Nat.land I.AA (Nat.xor (kz Z) FULL)
def fz (Z : ℕ) : ℕ := Nat.land FPM (Nat.xor (kz Z) FULL)
def mz (Z : ℕ) : ℕ := Nat.lor (Nat.lor (lz Z) (fz Z)) (Nat.shiftLeft (lz Z) I.NN)
def tz (Z : ℕ) : ℕ := Nat.land I.TG (mz Z)

section engine_ok2
lemma lz_lg (Z i : ℕ) (h : (lz Z).testBit i = true) : Lg I.NN (mz Z) (tz Z) i ∧ I.AA.testBit i = true := by
  have hA : I.AA.testBit i = true := by
    simp only [lz, nl, Nat.testBit_and, Bool.and_eq_true] at h; exact h.1
  have hT : I.TG.testBit i = true := by
    have := congrArg (fun x => x.testBit i) IOk.AA_TG
    simp [hA] at this; exact this
  have m1 : (mz Z).testBit i = true := by simp [mz, no, h]
  have m2 : (mz Z).testBit (I.NN + i) = true := by
    simp only [mz, no, Nat.testBit_or, Nat.shiftLeft_eq, Bool.or_eq_true]
    right
    change (lz Z <<< I.NN).testBit (I.NN + i) = true
    rw [Nat.testBit_shiftLeft]; simp [h]
  refine ⟨⟨m1, m2, ?_, ?_⟩, hA⟩
  · simp only [tz, nl, Nat.testBit_and, hT, m1]; rfl
  · simp only [tz, nl, Nat.testBit_and]
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le IOk.TG_lt (Nat.pow_le_pow_right (by omega) (by omega)))]; rfl
lemma segGood_eq {w o : ℕ} {s : ℕ × ℕ} (h : segGood w o s = true) {i j : ℕ} (h1 : s.1 < i) (h2 : i < s.2) (h3 : s.1 < j) (h4 : j < s.2) :
    w.testBit (o + i) = w.testBit (o + j) := by
  have key : ∀ i, s.1 < i → i < s.2 → w.testBit (o + i) = ((w >>> (o + s.1 + 1)) % 2 ^ (s.2 - s.1 - 1)).testBit (i - s.1 - 1) := by
    intro i h1 h2
    rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, show o + s.1 + 1 + (i - s.1 - 1) = o + i by omega]
    simp [show i - s.1 - 1 < s.2 - s.1 - 1 by omega]
  rw [key i h1 h2, key j h3 h4]
  simp only [segGood, Bool.or_eq_true, Nat.beq_eq] at h
  rcases h with h | h <;> rw [h]
  · simp
  · rw [Nat.testBit_two_pow_sub_one, Nat.testBit_two_pow_sub_one]
    simp [show i - s.1 - 1 < s.2 - s.1 - 1 by omega, show j - s.1 - 1 < s.2 - s.1 - 1 by omega]
lemma wire_good {w : ℕ} (hw : w ∈ rawG) (Z : ℕ) : Good (lz Z) (w &&& mz Z) := by
  have h := List.all_eq_true.1 IOk.raw_good w (by simpa [rawG, rawL, six] using hw)
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  refine ⟨fun i j hij h1 h2 => ?_, fun i j hij h1 h2 => ?_⟩ <;> obtain ⟨s, hs, a1, a2, a3, a4⟩ := hij
  · have := segGood_eq (h.1 s hs) a1 a2 a3 a4
    simp only [Nat.zero_add] at this
    rw [Nat.testBit_and, Nat.testBit_and, this, (lz_lg Z i h1).1.1, (lz_lg Z j h2).1.1]
  · have := segGood_eq (h.2 s hs) a1 a2 a3 a4
    rw [Nat.testBit_and, Nat.testBit_and, this, (lz_lg Z i h1).1.2.1, (lz_lg Z j h2).1.2.1]
noncomputable section
def pL (L : List ℕ) : ℕ := List.rec (motive := fun _ => ℕ) 0 (fun d _ ih => Nat.add (Nat.shiftLeft ih 5) d) L
end
lemma pL_cons (d : ℕ) (L : List ℕ) : pL (d :: L) = 2 ^ 5 * pL L + d := by
  change (pL L <<< 5) + d = _; rw [Nat.shiftLeft_eq]; ring
lemma pL_pk (L : List ℕ) : pL L = pk L.length (fun j => L.getD j 0) := by
  induction L with
  | nil => simp [pL, pk]
  | cons d L ih =>
    rw [pL_cons, ih, pk, pk, List.length_cons, Finset.sum_range_succ', Finset.mul_sum]
    simp only [Nat.mul_zero, pow_zero, mul_one, List.getD_cons_zero, List.getD_cons_succ]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show 5 * (j + 1) = 5 * j + 5 by ring, pow_add]; ring
lemma pL_bit {L : List ℕ} (h : ∀ d ∈ L, d ≤ 1) : ∀ i, (pL L).testBit i = true ↔ (i % 5 = 0 ∧ i / 5 < L.length ∧ L.getD (i / 5) 0 = 1) := by
  induction L with
  | nil => intro i; simp [pL]
  | cons d L ih =>
    intro i
    have hd := h d (by simp)
    have ih := ih fun x hx => h x (by simp [hx])
    rw [pL_cons, Nat.testBit_two_pow_mul_add _ (by omega)]
    split_ifs with hi
    · have : i / 5 = 0 := by omega
      rw [this]
      rcases Nat.eq_zero_or_pos i with rfl | hp
      · interval_cases d <;> simp
      · constructor
        · intro hb
          have : d.testBit i = false := Nat.testBit_lt_two_pow (lt_of_le_of_lt hd (Nat.one_lt_two_pow (by omega)))
          rw [this] at hb; simp at hb
        · intro hb; omega
    · rw [ih, show i / 5 = (i - 5) / 5 + 1 by omega]
      simp only [List.length_cons, List.getD_cons_succ]
      constructor
      · rintro ⟨a, b, c⟩; exact ⟨by omega, by omega, c⟩
      · rintro ⟨a, b, c⟩; exact ⟨by omega, by omega, c⟩
lemma pL_isPk {L : List ℕ} (h : ∀ d ∈ L, d ≤ 1) : isPk L.length (pL L) := fun i hi => by
  have := (pL_bit h i).1 hi; exact ⟨this.1, this.2.1⟩
def bit01 (b : Bool) : ℕ := bif b then 1 else 0
def mkW (P : List ℕ) (s : ℕ) : W := ⟨s, pL (P.map fun n => bit01 (Nat.beq (Nat.land s n) 0)), pL (P.map fun n => bit01 (Nat.beq (Nat.land s n) n)),
  Nat.lor (pL (P.map fun n => bit01 (Nat.beq (Nat.land s n) 0))) (pL (P.map fun n => bit01 (Nat.beq (Nat.land s n) n))), 3⟩
lemma mkW_ok (P : List ℕ) (s : ℕ) : WOk P (mkW P s) := by
  have h01 : ∀ f : ℕ → Bool, ∀ d ∈ P.map (fun n => bit01 (f n)), d ≤ 1 := by
    intro f d hd; simp only [List.mem_map] at hd
    obtain ⟨n, _, rfl⟩ := hd; cases f n <;> simp [bit01]
  have bt : ∀ f : ℕ → Bool, ∀ j < P.length, (pL (P.map fun n => bit01 (f n))).testBit (5 * j) = true → f (P.getD j 0) = true := by
    intro f j hj h
    have h := ((pL_bit (h01 f) _).1 h).2.2
    rw [show 5 * j / 5 = j by omega, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj] at h
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    simp at h ⊢
    cases hf : f P[j] <;> simp [bit01, hf] at h ⊢
  refine ⟨?_, ?_, rfl, fun j hj h => ?_, fun j hj h => ?_⟩
  · have := pL_isPk (h01 fun n => Nat.beq (Nat.land s n) 0); rwa [List.length_map] at this
  · have := pL_isPk (h01 fun n => Nat.beq (Nat.land s n) n); rwa [List.length_map] at this
  · exact Nat.eq_of_beq_eq_true (bt (fun n => Nat.beq (Nat.land s n) 0) j hj h)
  · exact Nat.eq_of_beq_eq_true (bt (fun n => Nat.beq (Nat.land s n) n) j hj h)
noncomputable section
def addS (o : W) (v : List W) : List W := List.rec (motive := fun _ => List W) [o]
  (fun w t ih => Bool.rec (motive := fun _ => List W) (w :: ih) (Bool.rec (motive := fun _ => List W) (o :: w :: t) (w :: t) (Nat.beq o.s w.s)) (Nat.ble w.s o.s)) v
def avl (P : List ℕ) (m : ℕ) (L : List ℕ) : List W := List.rec (motive := fun _ => List W) []
  (fun w _ ih => Bool.rec (motive := fun _ => List W) (Bool.rec (motive := fun _ => List W) (addS (mkW P (Nat.land w m)) ih) ih (Nat.beq (Nat.land w m) m)) ih (Nat.beq (Nat.land w m) 0)) L
def frc (v : List W) : (List W → Bool) → Bool := List.rec (motive := fun _ => (List W → Bool) → Bool) (fun h => h [])
  (fun w _ ih h => st w.s fun s => st w.a fun a => st w.b fun b => st w.c fun c => ih fun r => h (⟨s, a, b, c, w.r⟩ :: r)) v
def anySubC (NN : ℕ) (d : Bool) (l : ℕ) (v : List W) : ℕ → (List W → Bool) → Bool := List.rec (motive := fun _ => ℕ → (List W → Bool) → Bool) (fun _ h => h [])
  (fun w t ih c h => Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (ih c h) (Nat.beq (Nat.lor c (covC NN d l t)) l)) true
    (st (Nat.lor c (spC NN d l w.s)) fun c => ih c fun r => h (w :: r))) v
abbrev anySub := anySubC I.NN
def sumc (v : List W) : ℕ := List.rec (motive := fun _ => ℕ) 0 (fun w _ ih => Nat.add w.c ih) v
def MM : ℕ := 214
def hb (H x : ℕ) : Bool := Nat.beq (Nat.land (Nat.shiftRight H (Nat.mod x MM)) 1) 1
def pairsC (H : ℕ) (h : XW → XW → Bool) (xs : List XW) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun a r ih => Bool.rec (motive := fun _ => Bool) ih true
    (scan (fun x => Bool.rec (motive := fun _ => Bool) false (h a x) (hb H (Nat.add a.s x.s))) r)) xs
def topCC (NN AA HX HY l m g K H ph k t z : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) (tstC NN AA HX HY (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
    Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (mvC NN AA HX HY (lookC NN AA HX HY l m g K) l m g k t z v y) (Nat.beq ph 1)) true
      (nodeC NN (look1C NN AA HX HY l m g K K (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) v.length z v (fun h xs => pairsC H h (fs xs))))) true (Nat.ble v.length 1)
abbrev topC := topCC I.NN I.AA I.HX I.HY
def hasP (p : ℕ) (v : List W) : Bool := Bool.rec (motive := fun _ => Bool)
  (List.rec (motive := fun _ => Bool) false (fun w _ ih => Bool.rec (motive := fun _ => Bool) ih true (Nat.beq w.s p)) v) true (Nat.beq p 0)
def startvC (NN AA HX HY l m g B K t p H ph : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
    (child (fun z r => topCC NN AA HX HY l m g K H ph K t z r) g (fun h => h v) (Nat.sub B (sumc v)))
    (Nat.ble v.length (Nat.sub (Nat.succ K) t))) (hasP p v)
abbrev startv := startvC I.NN I.AA I.HX I.HY
end
lemma frc_eq (v : List W) : ∀ h, frc v h = h v := by
  induction v with
  | nil => intro h; rfl
  | cons w v ih =>
    intro h
    change st w.s (fun s => st w.a fun a => st w.b fun b => st w.c fun c => frc v fun r => h (⟨s, a, b, c, w.r⟩ :: r)) = _
    simp only [st_eq]; rw [ih]
lemma anySub_false {d : Bool} {l : ℕ} {v : List W} : ∀ {c : ℕ} {h : List W → Bool}, (∀ i, c.testBit i = true → l.testBit i = true) → anySub d l v c h = false →
    ∀ r, r.Sublist v → (∀ i, l.testBit i = true → c.testBit i = true ∨ (cov d l r).testBit i = true) → h r = false := by
  induction v with
  | nil => intro c h _ hh r hr _; rw [List.sublist_nil.1 hr]; exact hh
  | cons w v ih =>
    intro c h hcl hh r hr hcov
    change (Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (anySub d l v c h) (Nat.beq (Nat.lor c (cov d l v)) l)) true
      (st (Nat.lor c (sp d l w.s)) fun c => anySub d l v c fun r => h (w :: r)) : Bool) = false at hh
    rw [bR, bR, st_eq] at hh
    cases h1 : anySub d l v (Nat.lor c (sp d l w.s)) (fun r => h (w :: r)) with
    | true => rw [h1] at hh; simp at hh
    | false =>
      rw [h1, Bool.cond_false] at hh
      have hc2 : ∀ i, (cov d l v).testBit i = true → l.testBit i = true := by
        intro i hi
        obtain ⟨w', _, hw'⟩ := (cov_bit _ _ _ _).1 hi
        rw [sp_bit, Bool.and_eq_true] at hw'; exact hw'.1
      cases hr with
      | cons _ hr =>
        have : Nat.beq (Nat.lor c (cov d l v)) l = true := by
          rw [Nat.beq_eq]
          apply Nat.eq_of_testBit_eq; intro i
          rw [no, Nat.testBit_or]
          cases hli : l.testBit i with
          | false =>
            by_contra hc
            rw [Bool.not_eq_false, Bool.or_eq_true] at hc
            rcases hc with h | h
            · rw [hcl i h] at hli; simp at hli
            · rw [hc2 i h] at hli; simp at hli
          | true =>
            rcases hcov i hli with h | h
            · rw [h]; rfl
            · obtain ⟨w', hw', h2⟩ := (cov_bit _ _ _ _).1 h
              rw [(cov_bit d l i v).2 ⟨w', hr.subset hw', h2⟩]; simp
        rw [this, Bool.cond_true] at hh
        exact ih hcl hh r hr hcov
      | cons_cons _ hr =>
        rename_i r'
        refine ih (c := Nat.lor c (sp d l w.s)) ?_ h1 r' hr ?_
        · intro i hi
          rw [no, Nat.testBit_or, Bool.or_eq_true] at hi
          rcases hi with h | h
          · exact hcl i h
          · rw [sp_bit, Bool.and_eq_true] at h; exact h.1
        · intro i hi
          rw [no, Nat.testBit_or, Bool.or_eq_true]
          rcases hcov i hi with h | h
          · exact Or.inl (Or.inl h)
          · change (Nat.lor (sp d l w.s) (cov d l r')).testBit i = true at h
            rw [no, Nat.testBit_or, Bool.or_eq_true] at h
            rcases h with h | h
            · exact Or.inl (Or.inr h)
            · exact Or.inr h
lemma addS_cons (o w : W) (t : List W) : addS o (w :: t) = bif Nat.ble w.s o.s then (bif Nat.beq o.s w.s then w :: t else o :: w :: t) else w :: addS o t := by
  change Bool.rec (motive := fun _ => List W) (w :: addS o t) (Bool.rec (motive := fun _ => List W) (o :: w :: t) (w :: t) (Nat.beq o.s w.s)) (Nat.ble w.s o.s) = _
  cases Nat.ble w.s o.s <;> cases Nat.beq o.s w.s <;> rfl
def Srt (v : List W) : Prop := v.Pairwise (fun a b => b.s < a.s)
lemma addS_spec {o : W} {v : List W} (hv : Srt v) : Srt (addS o v) ∧ (∀ w ∈ addS o v, w = o ∨ w ∈ v) ∧
    (∃ w ∈ addS o v, w.s = o.s) ∧ ∀ w ∈ v, w ∈ addS o v := by
  induction v with
  | nil => exact ⟨List.pairwise_singleton _ _, by simp [addS], ⟨o, by simp [addS], rfl⟩, by simp⟩
  | cons x t ih =>
    have hp := List.pairwise_cons.1 hv
    obtain ⟨i1, i2, i3, i4⟩ := ih hp.2
    rw [addS_cons]
    cases h1 : Nat.ble x.s o.s with
    | true =>
      have hle := Nat.le_of_ble_eq_true h1
      cases h2 : Nat.beq o.s x.s with
      | true => exact ⟨hv, fun w hw => Or.inr hw, ⟨x, by simp, (Nat.eq_of_beq_eq_true h2).symm⟩, fun w hw => hw⟩
      | false =>
        have hne : o.s ≠ x.s := fun e => by rw [e, Nat.beq_refl] at h2; simp at h2
        refine ⟨List.pairwise_cons.2 ⟨fun w hw => ?_, hv⟩, fun w hw => by simpa using hw, ⟨o, by simp, rfl⟩, fun w hw => by simp at hw ⊢; tauto⟩
        simp only [List.mem_cons] at hw
        rcases hw with rfl | hw
        · omega
        · have := hp.1 w hw; omega
    | false =>
      have hlt : o.s < x.s := by
        by_contra hc; rw [Nat.ble_eq_true_of_le (by omega)] at h1; simp at h1
      refine ⟨List.pairwise_cons.2 ⟨fun w hw => ?_, i1⟩, fun w hw => ?_, ?_, fun w hw => ?_⟩
      · rcases i2 w hw with rfl | h
        · exact hlt
        · exact hp.1 w h
      · simp only [Bool.cond_false, List.mem_cons] at hw ⊢
        rcases hw with rfl | hw
        · simp
        · rcases i2 w hw with h | h <;> simp [h]
      · obtain ⟨w, hw, e⟩ := i3; exact ⟨w, by simp [hw], e⟩
      · simp only [Bool.cond_false, List.mem_cons] at hw ⊢
        rcases hw with rfl | hw
        · simp
        · exact Or.inr (i4 w hw)
lemma avl_spec (P : List ℕ) (m : ℕ) (L : List ℕ) : Srt (avl P m L) ∧ (∀ w ∈ avl P m L, ∃ x ∈ L, w = mkW P (x &&& m)) ∧
    ∀ x ∈ L, x &&& m ≠ 0 → x &&& m ≠ m → ∃ w ∈ avl P m L, w.s = x &&& m := by
  induction L with
  | nil => exact ⟨List.Pairwise.nil, by simp [avl], by simp⟩
  | cons y L ih =>
    obtain ⟨i1, i2, i3⟩ := ih
    have e : avl P m (y :: L) = bif Nat.beq (Nat.land y m) 0 then avl P m L else bif Nat.beq (Nat.land y m) m then avl P m L else addS (mkW P (Nat.land y m)) (avl P m L) := by
      change Bool.rec (motive := fun _ => List W) (Bool.rec (motive := fun _ => List W) (addS (mkW P (Nat.land y m)) (avl P m L)) (avl P m L) (Nat.beq (Nat.land y m) m)) (avl P m L) (Nat.beq (Nat.land y m) 0) = _
      cases Nat.beq (Nat.land y m) 0 <;> cases Nat.beq (Nat.land y m) m <;> rfl
    have old : ∀ w ∈ avl P m L, ∃ x ∈ y :: L, w = mkW P (x &&& m) := fun w hw => by
      obtain ⟨x, hx, e⟩ := i2 w hw; exact ⟨x, by simp [hx], e⟩
    rw [e]
    cases h1 : Nat.beq (Nat.land y m) 0 with
    | true =>
      refine ⟨i1, old, fun x hx h2 h3 => ?_⟩
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact absurd (Nat.eq_of_beq_eq_true h1) h2
      · exact i3 x hx h2 h3
    | false =>
      cases h1' : Nat.beq (Nat.land y m) m with
      | true =>
        refine ⟨i1, old, fun x hx h2 h3 => ?_⟩
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact absurd (Nat.eq_of_beq_eq_true h1') h3
        · exact i3 x hx h2 h3
      | false =>
        obtain ⟨j1, j2, j3, j4⟩ := addS_spec (o := mkW P (Nat.land y m)) i1
        refine ⟨j1, fun w hw => ?_, fun x hx h2 h3 => ?_⟩
        · rcases j2 w hw with rfl | h
          · exact ⟨y, by simp, rfl⟩
          · exact old w h
        · simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact j3
          · obtain ⟨w, hw, e⟩ := i3 x hx h2 h3; exact ⟨w, j4 w hw, e⟩
lemma pairsC_false {H : ℕ} {h : XW → XW → Bool} {xs : List XW} (hp : pairsC H h xs = false) :
    xs.Pairwise (fun a b => hb H (a.s + b.s) = true → h a b = false) := by
  induction xs with
  | nil => simp
  | cons a r ih =>
    change (Bool.rec (motive := fun _ => Bool) (pairsC H h r) true
      (scan (fun x => Bool.rec (motive := fun _ => Bool) false (h a x) (hb H (Nat.add a.s x.s))) r) : Bool) = false at hp
    rw [bR] at hp
    rw [List.pairwise_cons]
    constructor
    · intro b hbm hi
      have h1 : scan (fun x => Bool.rec (motive := fun _ => Bool) false (h a x) (hb H (Nat.add a.s x.s))) r = false := by
        revert hp
        cases scan (fun x => Bool.rec (motive := fun _ => Bool) false (h a x) (hb H (Nat.add a.s x.s))) r <;> simp
      have h2 := scan_false h1 b hbm
      beta_reduce at h2
      rw [bR] at h2
      have h3 : hb H (Nat.add a.s b.s) = true := hi
      rwa [h3, Bool.cond_true] at h2
    · apply ih; revert hp; cases pairsC H h r <;> simp
def mFull (M : List (ℕ × ℕ)) : Bool := (List.range MM).all (fun r => M.any (fun p => hb p.1 r)) && M.any (fun p => Nat.beq p.2 1)
lemma hb_mod (H x : ℕ) : hb H x = hb H (x % MM) := by
  unfold hb
  change Nat.beq ((H >>> (x % MM)) &&& 1) 1 = Nat.beq ((H >>> (x % MM % MM)) &&& 1) 1
  rw [Nat.mod_mod]
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma topC_sound (hR : RR R) (hR2 : ∀ d a b, (R a = 0 ∨ R b = 0) → Al R d a b) {K k t z : ℕ} {v : List W} {S : Finset ℕ} {M : List (ℕ × ℕ)}
    (hM : mFull M = true) (h : ∀ p ∈ M, topC l m g K p.1 p.2 k t z v = false) (hs : StOk P T l k z v S) (hcod : ∀ w ∈ v, w.r = R w.s)
    {k' : ℕ} (hk : k' ≤ k) (hl : Live Z0 m T k' t S) (hmW : ∀ q < k', ¬ Sol Z0 m T q (C m ({x | R x ≠ 0} ∪ (S : Set ℕ)))) : False := by
  simp only [mFull, Bool.and_eq_true, List.all_eq_true, List.mem_range, List.any_eq_true] at hM
  obtain ⟨hM1, p0, hp0, hp1⟩ := hM
  have un : ∀ p ∈ M, 2 ≤ v.length ∧ tst (pos' t) l (k + 1 - t) v (fun y =>
      Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (mv (look l m g K) l m g k t z v y) (Nat.beq p.2 1)) true
      (node (look1 l m g K K (k - 1) t) (pos' t) l m g (k - t - y) v.length z v (fun h xs => pairsC p.1 h (fs xs)))) = false := by
    intro p hp
    have h := h p hp
    change (Bool.rec (motive := fun _ => Bool) (tst (pos t) l (k + 1 - t) v (fun y =>
      Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (mv (look l m g K) l m g k t z v y) (Nat.beq p.2 1)) true
      (node (look1 l m g K K (k - 1) t) (pos t) l m g (k - t - y) v.length z v (fun h xs => pairsC p.1 h (fs xs))))) true (Nat.ble v.length 1) : Bool) = false at h
    rw [bR, pos_eq] at h
    cases h0 : Nat.ble v.length 1 with
    | true => rw [h0] at h; simp at h
    | false =>
      rw [h0, cond_false] at h
      refine ⟨?_, h⟩
      by_contra hc
      rw [Nat.ble_eq_true_of_le (by omega)] at h0; simp at h0
  have hmin : Min Z0 m T k' t S := ⟨hl, fun q hq hs => hmW q hq (hs.mono le_rfl (C_mono Set.subset_union_right))⟩
  obtain ⟨y, hFy, hyk⟩ := tst_sound X hs hmin hk
  have un2 := fun p hp => (hFy _).symm.trans (un p hp).2
  refine one_sound X hR hR2 (K := K) (f := look1 l m g K K) (look1_sound X hR hR2 (K := K) K) hs hcod (un p0 hp0).1 hk hl hmW hyk ?_ ?_
  · have := (or_false' X (un2 p0 hp0)).2
    rw [bR, hp1, cond_true] at this; exact this
  · intro a ha c hc hne har hcr
    obtain ⟨p, hpM, hpb⟩ := hM1 ((a.s + c.s) % MM) (Nat.mod_lt _ (by decide))
    rw [← hb_mod] at hpb
    refine ⟨_, (or_false' X (un2 p hpM)).1, fun h hp => ?_⟩
    have hpw := pairsC_false hp
    have : Std.Symm (fun a b : XW => hb p.1 (a.s + b.s) = true → (h a b = false ∨ h b a = false)) :=
      ⟨fun a b h e => (h (by rw [Nat.add_comm]; exact e)).symm⟩
    exact (hpw.imp (S := fun a b => hb p.1 (a.s + b.s) = true → (h a b = false ∨ h b a = false)) fun h e => Or.inl (h e)).forall
      (fs_mem (List.mem_map_of_mem ha) har) (fs_mem (List.mem_map_of_mem hc) hcr) (fun e => hne (congrArg XW.s e)) hpb
end sound
def WZ (E : List (ℕ × ℕ)) (Z : ℕ) : Set ℕ := {x | ∃ w ∈ rawL E, x = w &&& mz Z}
def Imp (E : List (ℕ × ℕ)) (Z L : ℕ) : Prop := ∀ q < L, ¬ Sol Z0 (mz Z) (tz Z) q (C (mz Z) (WZ E Z))
def PZ (Q : List (ℕ × ℕ)) : List ℕ := Q.map (fun e => mz e.1)
def pOk (Z : ℕ) (Q : List (ℕ × ℕ)) : Bool := !Nat.beq (tz Z) 0 && !Nat.beq (tz Z) (mz Z) && Q.all (fun e => Nat.beq (Nat.land (mz e.1) (mz Z)) (mz e.1) &&
  !Nat.beq (tz e.1) 0 && !Nat.beq (tz e.1) (mz e.1))
def pwr (E : List (ℕ × ℕ)) (Z : ℕ) : ℕ := (E.map fun e => Nat.land (xw e) (mz Z)).headD 0
noncomputable def chk (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ) : Bool :=
  (fun l => (fun m => (fun P => (fun g => (fun B => (fun p =>
    frc (avl P m (rawL E)) (fun v => st l fun l => st m fun m => st g fun g => st B fun B => st p fun p =>
      st I.NN fun nn => st I.AA fun aa => st I.HX fun hx => st I.HY fun hy =>
      anySubC nn (pos t) l v 0 (fun r => startvC nn aa hx hy l m g B K t p H ph r)))
    (pwr E Z)) (pL (Q.map fun e => 16 + (K - e.2)))) (pL (Q.map fun _ => 16))) (PZ Q)) (mz Z)) (lz Z)
lemma tz_sub {Z Z' : ℕ} (h : mz Z' &&& mz Z = mz Z') : tz Z &&& mz Z' = tz Z' := by
  simp only [tz, nl, Nat.and_assoc]; rw [Nat.and_comm (mz Z), h]
lemma Im_WZ {E : List (ℕ × ℕ)} {Z Z' : ℕ} (h : mz Z' &&& mz Z = mz Z') {S : Finset ℕ} (hS : (S : Set ℕ) ⊆ WZ E Z) : Im (mz Z') S ⊆ WZ E Z' := by
  rintro x ⟨y, hy, rfl⟩
  obtain ⟨w, hw, rfl⟩ := hS hy
  exact ⟨w, hw, by simp only [Nat.and_assoc]; rw [Nat.and_comm (mz Z), h]⟩
lemma sumc_eq {P : List ℕ} {v : List W} (hw : ∀ w ∈ v, WOk P w) : sumc v = pk P.length (cnt v) := by
  induction v with
  | nil => simp [sumc, pk, cnt]
  | cons w v ih =>
    change w.c + sumc v = _
    rw [ih fun x hx => hw x (by simp [hx]), fl_pk (hw w (by simp)), pk_add]
    exact pk_congr fun j _ => by rw [cnt_cons]
lemma pk16 (Q : List (ℕ × ℕ)) (K : ℕ) : pL (Q.map fun e => 16 + (K - e.2)) = pk (PZ Q).length (fun j => 16 + (K - (Q.getD j (0, K)).2)) := by
  rw [pL_pk, PZ, List.length_map, List.length_map]
  refine pk_congr fun j hj => ?_
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]; rfl
open Classical in
noncomputable def RZ (E : List (ℕ × ℕ)) (Z : ℕ) : ℕ → ℕ := fun s => if s ∈ WZ E Z then 3 else 0
lemma RZ_set (E : List (ℕ × ℕ)) (Z : ℕ) : {x | RZ E Z x ≠ 0} = WZ E Z := by
  ext x; simp only [RZ, Set.mem_setOf_eq]; split_ifs with h <;> simp [h]
lemma RZ_R (E : List (ℕ × ℕ)) (Z : ℕ) : RR (RZ E Z) := by
  intro d a b ha hb h
  have h3 : ∀ x, RZ E Z x ≠ 0 → RZ E Z x = 3 := by
    intro x hx; unfold RZ at hx ⊢; split_ifs at hx ⊢ with h
    · rfl
    · simp at hx
  unfold Al at h
  rw [h3 a ha, h3 b hb] at h
  cases d <;> simp at h
lemma RZ_R2 (E : List (ℕ × ℕ)) (Z : ℕ) : ∀ d a b, (RZ E Z a = 0 ∨ RZ E Z b = 0) → Al (RZ E Z) d a b := by
  intro d a b h
  unfold Al
  rcases h with h | h <;> rw [h] <;> simp
lemma hasP_ok {p : ℕ} {v : List W} (h : p = 0 ∨ ∃ w ∈ v, w.s = p) : hasP p v = true := by
  unfold hasP
  rw [bR]
  rcases h with rfl | ⟨w, hw, rfl⟩
  · rfl
  · have : (List.rec (motive := fun _ => Bool) false (fun w' _ ih => Bool.rec (motive := fun _ => Bool) ih true (Nat.beq w'.s w.s)) v : Bool) = true := by
      induction v with
      | nil => simp at hw
      | cons x v ih =>
        change (Bool.rec (motive := fun _ => Bool) (List.rec (motive := fun _ => Bool) false (fun w' _ ih => Bool.rec (motive := fun _ => Bool) ih true (Nat.beq w'.s w.s)) v : Bool) true (Nat.beq x.s w.s) : Bool) = true
        rw [bR]
        simp only [List.mem_cons] at hw
        rcases hw with rfl | hw
        · rw [Nat.beq_refl]; rfl
        · rw [ih hw]; cases Nat.beq x.s w.s <;> rfl
    rw [this]; cases Nat.beq w.s 0 <;> rfl
lemma rawL_sub {E : List (ℕ × ℕ)} (hE : ∀ e ∈ E, e ∈ six) {w : ℕ} (hw : w ∈ rawL E) : w ∈ rawG := by
  simp only [rawG, rawL, List.mem_append, List.mem_map] at hw ⊢
  rcases hw with h | ⟨e, he, rfl⟩
  · exact Or.inl h
  · exact Or.inr ⟨e, hE e he, rfl⟩
theorem imp_of_live {E Q : List (ℕ × ℕ)} {Z L k t : ℕ} {S : Finset ℕ}
    (hE : E = [] ∨ ∃ e ∈ six, E = [e] ∧ Imp [] Z L) (hp : pOk Z Q = true) (hL : L ≤ 15)
    (hI : ∀ e ∈ Q, Imp E e.1 e.2)
    (hk : k < L) (hS : (S : Set ℕ) ⊆ C (mz Z) (WZ E Z)) (hl : Live Z0 (mz Z) (tz Z) k t S)
    (hmin : ∀ q < k, ¬ Sol Z0 (mz Z) (tz Z) q (C (mz Z) (WZ E Z)))
    (hb : (∃ e ∈ Q, L ≤ e.2) ∨ ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk E Q Z (L - 1) t p.1 p.2 = false) : False := by
  simp only [pOk, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at hp
  obtain ⟨⟨hp0, hp1⟩, hp2⟩ := hp
  have nb : ∀ {x y : ℕ}, Nat.beq x y = false → x ≠ y := fun h e => by rw [e, Nat.beq_refl] at h; simp at h
  have hT : tz Z &&& mz Z = tz Z := by simp only [tz, nl, Nat.and_assoc, Nat.and_self]
  have hE6 : ∀ e ∈ E, e ∈ six := by
    rcases hE with rfl | ⟨e, he, rfl, _⟩
    · simp
    · intro e' he'; simp only [List.mem_singleton] at he'; rw [he']; exact he
  classical
  have hCS : C (mz Z) (S : Set ℕ) ⊆ C (mz Z) (WZ E Z) := by
    rintro x (hx | hx)
    · exact hS hx
    · exact Or.inr hx
  have hm : Min Z0 (mz Z) (tz Z) k t S := ⟨hl, fun q' hq' hs => hmin q' hq' (hs.mono le_rfl hCS)⟩
  have hbd : ∀ x ∈ S, x &&& mz Z = x := by
    intro x hx
    rcases hS hx with ⟨w, _, rfl⟩ | h
    · rw [Nat.and_assoc, Nat.and_self]
    · simp at h; rcases h with rfl | rfl <;> simp
  obtain ⟨h0, h1⟩ := hm.proper hT (nb hp0) (nb hp1) hbd
  have hSW : (S : Set ℕ) ⊆ WZ E Z := by
    intro x hx
    rcases hS hx with h | h
    · exact h
    · simp at h; rcases h with rfl | rfl
      · exact absurd hx h0
      · exact absurd hx h1
  have hproj : ∀ e ∈ Q, mz e.1 &&& mz Z = mz e.1 ∧ tz e.1 ≠ 0 ∧ tz e.1 ≠ mz e.1 := by
    intro e he
    obtain ⟨⟨a, b⟩, c⟩ := hp2 e he
    exact ⟨Nat.eq_of_beq_eq_true a, nb b, nb c⟩
  have hno : ∀ e ∈ Q, ∀ q < e.2, ¬ Sol Z0 (mz e.1) (tz Z &&& mz e.1) q (C (mz e.1) (Im (mz e.1) S)) := by
    intro e he q hq hs
    have h3 := (hproj e he).1
    rw [tz_sub h3] at hs
    exact hI e he q hq (hs.mono le_rfl (C_mono (Im_WZ h3 hSW)))
  have htk := hm.size.2
  rcases hb with ⟨e, he, hle⟩ | hb
  · have h3 := hproj e he
    obtain ⟨q', hq', hs'⟩ := hm.const h3.1 (by rw [tz_sub h3.1]; exact h3.2.1) (by rw [tz_sub h3.1]; exact h3.2.2)
    exact hno e he q' (by omega) hs'
  have hpw : pwr E Z = 0 ∨ pwr E Z ∈ S := by
    rcases hE with rfl | ⟨e, he, rfl, hraw⟩
    · exact Or.inl rfl
    · by_contra hc
      push Not at hc
      refine hraw k (by omega) (hl.sol.mono le_rfl ?_)
      intro x hx
      obtain ⟨w, hw, rfl⟩ := hSW hx
      simp only [rawL, List.mem_append, List.map_cons, List.map_nil, List.mem_singleton] at hw
      rcases hw with hw | rfl
      · exact Or.inl ⟨w, by simp [rawL, hw], rfl⟩
      · have hx : xw e &&& mz Z ∈ S := by simpa using hx
        exact absurd (show pwr [e] Z ∈ S from hx) hc.2
  obtain ⟨M, hMf, hchk⟩ := hb
  obtain ⟨a1, a2, a3⟩ := avl_spec (PZ Q) (mz Z) (rawL E)
  set v := (avl (PZ Q) (mz Z) (rawL E)).filter (fun w => decide (w.s ∈ S)) with hv
  have hsub : v.Sublist (avl (PZ Q) (mz Z) (rawL E)) := List.filter_sublist
  have hnd : (v.map W.s).Nodup := by
    rw [List.Nodup, List.pairwise_map]
    exact (a1.sublist hsub).imp fun h => Nat.ne_of_gt h
  have hrep : Rep v S := by
    refine ⟨hnd, Finset.ext fun x => ?_⟩
    rw [List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [hv, List.mem_filter] at hw; simpa using hw.2
    · intro hx
      obtain ⟨w, hw, rfl⟩ := hSW hx
      obtain ⟨w', hw', e⟩ := a3 w hw (fun e => h0 (e ▸ hx)) (fun e => h1 (e ▸ hx))
      exact ⟨w', by rw [hv, List.mem_filter]; exact ⟨hw', by simpa [e] using hx⟩, e⟩
  have hwok : ∀ w ∈ v, WOk (PZ Q) w := by
    intro w hw
    obtain ⟨x, _, rfl⟩ := a2 w (hsub.subset hw); exact mkW_ok _ _
  have hcod : ∀ w ∈ v, w.r = RZ E Z w.s := by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := a2 w (hsub.subset hw)
    have : x &&& mz Z ∈ WZ E Z := ⟨x, hx, rfl⟩
    change 3 = RZ E Z (x &&& mz Z)
    rw [RZ, if_pos this]
  have hgood : ∀ w ∈ v, Good (lz Z) w.s := by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := a2 w (hsub.subset hw); exact wire_good (rawL_sub hE6 hx) Z
  have hPlen : (PZ Q).length = Q.length := by simp [PZ]
  have hPget : ∀ j < (PZ Q).length, (PZ Q).getD j 0 = mz (Q.getD j (0, L - 1)).1 ∧ Q.getD j (0, L - 1) ∈ Q := by
    intro j hj
    rw [hPlen] at hj
    simp [PZ, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]
  have X : Ctx (PZ Q) (lz Z) (mz Z) (pL (Q.map fun _ => 16)) (tz Z) := by
    refine ⟨fun i hi => lz_lg Z i hi, fun j hj => ?_, ?_⟩
    · obtain ⟨e1, e2⟩ := hPget j hj
      have h3 := hproj _ e2
      rw [e1, tz_sub h3.1]; exact h3
    · rw [pL_pk, List.length_map, hPlen]
      refine pk_congr fun j hj => ?_
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]; rfl
  have hcl : Cl (PZ Q) (tz Z) (L - 1) (fun j => L - 1 - (Q.getD j (0, L - 1)).2) S := by
    intro j hj q hq
    obtain ⟨e1, e2⟩ := hPget j hj
    have hq' : q + (L - 1 - (Q.getD j (0, L - 1)).2) < L - 1 := hq
    rw [e1]; exact hno _ e2 q (by omega)
  have hle := cnt_le X hrep hwok hcl hm (by omega)
  have hst : StOk (PZ Q) (tz Z) (lz Z) (L - 1) (pL (Q.map fun e => 16 + (L - 1 - e.2)) - sumc v) v S := by
    refine ⟨hrep, hwok, hgood, _, fun j _ => by omega, hcl, ?_⟩
    rw [sumc_eq hwok, pk16, pk_sub]
    intro j hj; have := hle j hj; omega
  have hcov : ∀ i, (lz Z).testBit i = true → (0 : ℕ).testBit i = true ∨ (cov (pos t) (lz Z) v).testBit i = true := by
    intro i hli
    right
    rw [cov_bit]
    obtain ⟨⟨m1, m2, t1, t2⟩, _⟩ := lz_lg Z i hli
    obtain ⟨w, hw, hs⟩ := hl.cov m1 m2 t1 t2
    obtain ⟨w', hw', rfl⟩ := hrep.mem.1 hw
    exact ⟨w', hw', by rw [sp_bit, hli, pos_eq, hs]; rfl⟩
  have hsz := hm.size.1
  have hcard := hrep.card
  have hble : Nat.ble v.length (Nat.sub (Nat.succ (L - 1)) t) = true := Nat.ble_eq_true_of_le (by
    change v.length ≤ L - 1 + 1 - t; omega)
  have hhas : hasP (pwr E Z) v = true := hasP_ok (hpw.imp id fun h => hrep.mem.1 h)
  have all : ∀ p ∈ M, topC (lz Z) (mz Z) (pL (Q.map fun _ => 16)) (L - 1) p.1 p.2 (L - 1) t (pL (Q.map fun e => 16 + (L - 1 - e.2)) - sumc v) v = false := by
    intro p hpM
    have h2 := hchk p hpM
    simp only [chk, frc_eq, st_eq] at h2
    have h3 := anySub_false (by simp) h2 v hsub hcov
    simp only [startv, startvC, bR, hhas, hble, Bool.cond_true] at h3
    exact child_sound X (f := fun z r => topC (lz Z) (mz Z) _ (L - 1) p.1 p.2 (L - 1) t z r) (fun h => rfl) hst hm (by omega) h3
  refine topC_sound X (RZ_R E Z) (RZ_R2 E Z) hMf all hst hcod (by omega) hl ?_
  intro q hq hs
  rw [RZ_set] at hs
  refine hmin q hq (hs.mono le_rfl ?_)
  rintro x ((hx | hx) | hx)
  · exact Or.inl hx
  · exact Or.inl (hSW hx)
  · exact Or.inr hx
theorem imp_of {E Q : List (ℕ × ℕ)} {Z L : ℕ} (hE : E = [] ∨ ∃ e ∈ six, E = [e] ∧ Imp [] Z L) (hp : pOk Z Q = true) (hL : L ≤ 15) (hI : ∀ e ∈ Q, Imp E e.1 e.2)
    (hb : (∃ e ∈ Q, L ≤ e.2) ∨ ∀ t < L, ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk E Q Z (L - 1) t p.1 p.2 = false) : Imp E Z L := by
  intro q hq hsol
  simp only [pOk, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at hp
  obtain ⟨⟨hp0, hp1⟩, hp2⟩ := hp
  have nb : ∀ {x y : ℕ}, Nat.beq x y = false → x ≠ y := fun h e => by rw [e, Nat.beq_refl] at h; simp at h
  have hT : tz Z &&& mz Z = tz Z := by simp only [tz, nl, Nat.and_assoc, Nat.and_self]
  have hE6 : ∀ e ∈ E, e ∈ six := by
    rcases hE with rfl | ⟨e, he, rfl, _⟩
    · simp
    · intro e' he'; simp only [List.mem_singleton] at he'; rw [he']; exact he
  classical
  have hex : ∃ q, Sol Z0 (mz Z) (tz Z) q (C (mz Z) (WZ E Z)) := ⟨q, hsol⟩
  have hqL : Nat.find hex < L := lt_of_le_of_lt (Nat.find_min' hex hsol) hq
  obtain ⟨k, hk, t, S, hS, hl⟩ := (Nat.find_spec hex).live
  have hCS : C (mz Z) (S : Set ℕ) ⊆ C (mz Z) (WZ E Z) := by
    rintro x (hx | hx)
    · exact hS hx
    · exact Or.inr hx
  have hkeq : k = Nat.find hex := le_antisymm hk (Nat.find_min' hex (hl.sol.mono le_rfl hS))
  have hm : Min Z0 (mz Z) (tz Z) k t S := ⟨hl, fun q' hq' hs => Nat.find_min hex (by omega) (hs.mono le_rfl hCS)⟩
  have hbd : ∀ x ∈ S, x &&& mz Z = x := by
    intro x hx
    rcases hS hx with ⟨w, _, rfl⟩ | h
    · rw [Nat.and_assoc, Nat.and_self]
    · simp at h; rcases h with rfl | rfl <;> simp
  obtain ⟨h0, h1⟩ := hm.proper hT (nb hp0) (nb hp1) hbd
  have hSW : (S : Set ℕ) ⊆ WZ E Z := by
    intro x hx
    rcases hS hx with h | h
    · exact h
    · simp at h; rcases h with rfl | rfl
      · exact absurd hx h0
      · exact absurd hx h1
  have hproj : ∀ e ∈ Q, mz e.1 &&& mz Z = mz e.1 ∧ tz e.1 ≠ 0 ∧ tz e.1 ≠ mz e.1 := by
    intro e he
    obtain ⟨⟨a, b⟩, c⟩ := hp2 e he
    exact ⟨Nat.eq_of_beq_eq_true a, nb b, nb c⟩
  have hno : ∀ e ∈ Q, ∀ q < e.2, ¬ Sol Z0 (mz e.1) (tz Z &&& mz e.1) q (C (mz e.1) (Im (mz e.1) S)) := by
    intro e he q hq hs
    have h3 := (hproj e he).1
    rw [tz_sub h3] at hs
    exact hI e he q hq (hs.mono le_rfl (C_mono (Im_WZ h3 hSW)))
  have htk := hm.size.2
  rcases hb with ⟨e, he, hle⟩ | hb
  · have h3 := hproj e he
    obtain ⟨q', hq', hs'⟩ := hm.const h3.1 (by rw [tz_sub h3.1]; exact h3.2.1) (by rw [tz_sub h3.1]; exact h3.2.2)
    exact hno e he q' (by omega) hs'
  have hpw : pwr E Z = 0 ∨ pwr E Z ∈ S := by
    rcases hE with rfl | ⟨e, he, rfl, hraw⟩
    · exact Or.inl rfl
    · by_contra hc
      push Not at hc
      refine hraw k (by omega) (hl.sol.mono le_rfl ?_)
      intro x hx
      obtain ⟨w, hw, rfl⟩ := hSW hx
      simp only [rawL, List.mem_append, List.map_cons, List.map_nil, List.mem_singleton] at hw
      rcases hw with hw | rfl
      · exact Or.inl ⟨w, by simp [rawL, hw], rfl⟩
      · have hx : xw e &&& mz Z ∈ S := by simpa using hx
        exact absurd (show pwr [e] Z ∈ S from hx) hc.2
  obtain ⟨M, hMf, hchk⟩ := hb t (by omega)
  obtain ⟨a1, a2, a3⟩ := avl_spec (PZ Q) (mz Z) (rawL E)
  set v := (avl (PZ Q) (mz Z) (rawL E)).filter (fun w => decide (w.s ∈ S)) with hv
  have hsub : v.Sublist (avl (PZ Q) (mz Z) (rawL E)) := List.filter_sublist
  have hnd : (v.map W.s).Nodup := by
    rw [List.Nodup, List.pairwise_map]
    exact (a1.sublist hsub).imp fun h => Nat.ne_of_gt h
  have hrep : Rep v S := by
    refine ⟨hnd, Finset.ext fun x => ?_⟩
    rw [List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [hv, List.mem_filter] at hw; simpa using hw.2
    · intro hx
      obtain ⟨w, hw, rfl⟩ := hSW hx
      obtain ⟨w', hw', e⟩ := a3 w hw (fun e => h0 (e ▸ hx)) (fun e => h1 (e ▸ hx))
      exact ⟨w', by rw [hv, List.mem_filter]; exact ⟨hw', by simpa [e] using hx⟩, e⟩
  have hwok : ∀ w ∈ v, WOk (PZ Q) w := by
    intro w hw
    obtain ⟨x, _, rfl⟩ := a2 w (hsub.subset hw); exact mkW_ok _ _
  have hcod : ∀ w ∈ v, w.r = RZ E Z w.s := by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := a2 w (hsub.subset hw)
    have : x &&& mz Z ∈ WZ E Z := ⟨x, hx, rfl⟩
    change 3 = RZ E Z (x &&& mz Z)
    rw [RZ, if_pos this]
  have hgood : ∀ w ∈ v, Good (lz Z) w.s := by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := a2 w (hsub.subset hw); exact wire_good (rawL_sub hE6 hx) Z
  have hPlen : (PZ Q).length = Q.length := by simp [PZ]
  have hPget : ∀ j < (PZ Q).length, (PZ Q).getD j 0 = mz (Q.getD j (0, L - 1)).1 ∧ Q.getD j (0, L - 1) ∈ Q := by
    intro j hj
    rw [hPlen] at hj
    simp [PZ, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]
  have X : Ctx (PZ Q) (lz Z) (mz Z) (pL (Q.map fun _ => 16)) (tz Z) := by
    refine ⟨fun i hi => lz_lg Z i hi, fun j hj => ?_, ?_⟩
    · obtain ⟨e1, e2⟩ := hPget j hj
      have h3 := hproj _ e2
      rw [e1, tz_sub h3.1]; exact h3
    · rw [pL_pk, List.length_map, hPlen]
      refine pk_congr fun j hj => ?_
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]; rfl
  have hcl : Cl (PZ Q) (tz Z) (L - 1) (fun j => L - 1 - (Q.getD j (0, L - 1)).2) S := by
    intro j hj q hq
    obtain ⟨e1, e2⟩ := hPget j hj
    have hq' : q + (L - 1 - (Q.getD j (0, L - 1)).2) < L - 1 := hq
    rw [e1]; exact hno _ e2 q (by omega)
  have hle := cnt_le X hrep hwok hcl hm (by omega)
  have hst : StOk (PZ Q) (tz Z) (lz Z) (L - 1) (pL (Q.map fun e => 16 + (L - 1 - e.2)) - sumc v) v S := by
    refine ⟨hrep, hwok, hgood, _, fun j _ => by omega, hcl, ?_⟩
    rw [sumc_eq hwok, pk16, pk_sub]
    intro j hj; have := hle j hj; omega
  have hcov : ∀ i, (lz Z).testBit i = true → (0 : ℕ).testBit i = true ∨ (cov (pos t) (lz Z) v).testBit i = true := by
    intro i hli
    right
    rw [cov_bit]
    obtain ⟨⟨m1, m2, t1, t2⟩, _⟩ := lz_lg Z i hli
    obtain ⟨w, hw, hs⟩ := hl.cov m1 m2 t1 t2
    obtain ⟨w', hw', rfl⟩ := hrep.mem.1 hw
    exact ⟨w', hw', by rw [sp_bit, hli, pos_eq, hs]; rfl⟩
  have hsz := hm.size.1
  have hcard := hrep.card
  have hble : Nat.ble v.length (Nat.sub (Nat.succ (L - 1)) t) = true := Nat.ble_eq_true_of_le (by
    change v.length ≤ L - 1 + 1 - t; omega)
  have hhas : hasP (pwr E Z) v = true := hasP_ok (hpw.imp id fun h => hrep.mem.1 h)
  have all : ∀ p ∈ M, topC (lz Z) (mz Z) (pL (Q.map fun _ => 16)) (L - 1) p.1 p.2 (L - 1) t (pL (Q.map fun e => 16 + (L - 1 - e.2)) - sumc v) v = false := by
    intro p hpM
    have h2 := hchk p hpM
    simp only [chk, frc_eq, st_eq] at h2
    have h3 := anySub_false (by simp) h2 v hsub hcov
    simp only [startv, startvC, bR, hhas, hble, Bool.cond_true] at h3
    exact child_sound X (f := fun z r => topC (lz Z) (mz Z) _ (L - 1) p.1 p.2 (L - 1) t z r) (fun h => rfl) hst hm (by omega) h3
  refine topC_sound X (RZ_R E Z) (RZ_R2 E Z) hMf all hst hcod (by omega) hl ?_
  intro q hq hs
  rw [RZ_set] at hs
  refine Nat.find_min hex (show q < Nat.find hex by omega) (hs.mono le_rfl ?_)
  rintro x ((hx | hx) | hx)
  · exact Or.inl hx
  · exact Or.inl (hSW hx)
  · exact Or.inr hx
def FF : ℕ := 2 ^ MM - 1
lemma ffull : mFull [(FF, 1)] = true := by decide +kernel
noncomputable def okT (E Q : List (ℕ × ℕ)) (Z L : ℕ) (ts : List ℕ) : Bool := ts.all (fun t => !chk E Q Z (L - 1) t FF 1)
noncomputable def okE (E Q : List (ℕ × ℕ)) (e : ℕ × ℕ) : Bool := pOk e.1 Q && Nat.ble e.2 15 && (Q.any (fun x => Nat.ble e.2 x.2) || okT E Q e.1 e.2 (List.range e.2))
lemma imp_okE {E Q : List (ℕ × ℕ)} {e : ℕ × ℕ} (hE : E = [] ∨ ∃ e' ∈ six, E = [e'] ∧ Imp [] e.1 e.2) (h : okE E Q e = true) (hI : ∀ e' ∈ Q, Imp E e'.1 e'.2) : Imp E e.1 e.2 := by
  simp only [okE, okT, Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true, List.all_eq_true, List.mem_range, Bool.not_eq_true'] at h
  refine imp_of hE h.1.1 (Nat.le_of_ble_eq_true h.1.2) hI (h.2.imp (fun ⟨x, hx, hx2⟩ => ⟨x, hx, Nat.le_of_ble_eq_true hx2⟩) fun h t ht =>
    ⟨[(FF, 1)], ffull, fun p hp => ?_⟩)
  simp only [List.mem_singleton] at hp; subst hp; exact h t ht
def pr (T : List (ℕ × ℕ)) (Z : ℕ) : List (ℕ × ℕ) := T.filter (fun e => Nat.beq (Nat.land Z e.1) Z && !Nat.beq Z e.1)
lemma okAll {T U : List (ℕ × ℕ)} (h : U.all (fun e => okE [] (pr T e.1) e) = true)
    (hT : ∀ e ∈ T, Imp [] e.1 e.2) : ∀ e ∈ U, Imp [] e.1 e.2 := fun e he => imp_okE
  (Or.inl rfl) (List.all_eq_true.1 h e he) (fun e' h' => hT e' (List.mem_of_mem_filter h'))
lemma apI {E A B : List (ℕ × ℕ)} (ha : ∀ e ∈ A, Imp E e.1 e.2) (hb : ∀ e ∈ B, Imp E e.1 e.2) : ∀ e ∈ A ++ B, Imp E e.1 e.2 := fun e he =>
  (List.mem_append.1 he).elim (ha e) (hb e)
lemma imp_ts {E Q : List (ℕ × ℕ)} {L : ℕ} (hE : E = [] ∨ ∃ p ∈ six, E = [p] ∧ Imp [] 0 L) (hp : pOk 0 Q = true) (hL : L ≤ 15) (hI : ∀ e ∈ Q, Imp E e.1 e.2)
    (h : ∀ t < L, ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk E Q 0 (L - 1) t p.1 p.2 = false) : Imp E 0 L :=
  imp_of hE hp hL hI (Or.inr h)
lemma one {E Q : List (ℕ × ℕ)} {K t : ℕ} (h : chk E Q 0 K t FF 1 = false) : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk E Q 0 K t p.1 p.2 = false :=
  ⟨[(FF, 1)], ffull, fun q hq => by simp only [List.mem_singleton] at hq; subst hq; exact h⟩

end engine_ok2

end engine
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
section circuit
variable (m : ℕ)
def gv (w : List ℕ) (g : Gate) : ℕ := match g.op, g.inputs with
  | .and, [] => m
  | .and, [i] => w.getD i 0
  | .and, i :: j :: _ => w.getD i 0 &&& w.getD j 0
  | .or, [] => 0
  | .or, [i] => w.getD i 0
  | .or, i :: j :: _ => w.getD i 0 ||| w.getD j 0
  | .not, [] => m
  | .not, i :: _ => w.getD i 0 ^^^ m
  | _, _ => 0
def ex (gs : List Gate) (w : List ℕ) : List ℕ := gs.foldl (fun w g => w ++ [gv m w g]) w
lemma getD_mem {S : Set ℕ} {w : List ℕ} (hw : ∀ x ∈ w, x ∈ S) (h0 : 0 ∈ S) (i : ℕ) : w.getD i 0 ∈ S := by
  rw [List.getD_eq_getElem?_getD]
  by_cases h : i < w.length
  · rw [List.getElem?_eq_getElem h]; exact hw _ (List.getElem_mem h)
  · rw [List.getElem?_eq_none (by omega)]; exact h0
lemma ex_sol {T : ℕ} (gs : List Gate) : ∀ (w : List ℕ) (S : Set ℕ), (∀ x ∈ w, x ∈ S) → 0 ∈ S → m ∈ S →
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    (∃ i, (ex m gs w).getD i 0 = T) → Sol Z0 m T gs.length S := by
  induction gs with
  | nil =>
    rintro w S hw h0 _ _ ⟨i, rfl⟩
    exact .done (getD_mem hw h0 i)
  | cons g gs ih =>
    intro w S hw h0 hm hg hT
    have hgs := fun x hx => hg x (List.mem_cons_of_mem _ hx)
    have rd := fun i => getD_mem hw h0 i
    have stay : gv m w g ∈ S → Sol Z0 m T (g :: gs).length S := fun h =>
      (ih (w ++ [gv m w g]) S (fun x hx => by
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact hw x hx
        · exact h) h0 hm hgs hT).mono (by simp) subset_rfl
    have go : Sol Z0 m T gs.length (insert (gv m w g) S) := ih (w ++ [gv m w g]) _ (fun x hx => by
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact Or.inr (hw x hx)
        · exact Or.inl rfl) (Or.inr h0) (Or.inr hm) hgs hT
    obtain ⟨hop, hlen⟩ := hg g List.mem_cons_self
    obtain ⟨o, l⟩ := g
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with rfl | rfl | rfl
    · match l with
      | [] => exact stay hm
      | [i] => exact stay (rd i)
      | i :: j :: _ => exact .bi (d := false) (rd i) (rd j) (al0 _ _ _) go
    · match l with
      | [] => exact stay h0
      | [i] => exact stay (rd i)
      | i :: j :: _ => exact .bi (d := true) (rd i) (rd j) (al0 _ _ _) go
    · match l with
      | [] => exact stay hm
      | i :: _ => exact .un (rd i) go
lemma gv_sub {w : List ℕ} (hw : ∀ x ∈ w, x &&& m = x) (g : Gate) : gv m w g &&& m = gv m w g := by
  have rd : ∀ i, w.getD i 0 &&& m = w.getD i 0 := fun i => getD_mem (S := {x | x &&& m = x}) hw (by simp) i
  unfold gv
  split
  · simp
  · exact rd _
  · rw [Nat.and_assoc, rd]
  · simp
  · exact rd _
  · rw [Nat.and_or_distrib_right, rd, rd]
  · simp
  · rw [and_neg (Nat.and_self m), rd]
  · simp
lemma ex_sub {gs : List Gate} : ∀ {w : List ℕ}, (∀ x ∈ w, x &&& m = x) → ∀ x ∈ ex m gs w, x &&& m = x := by
  induction gs with
  | nil => intro w hw; exact hw
  | cons g gs ih =>
    intro w hw
    refine ih (w := w ++ [gv m w g]) fun x hx => ?_
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact hw x hx
    · exact gv_sub m hw g
lemma getD_map (w : List ℕ) (b i : ℕ) : (w.map (fun x => x.testBit b)).getD i false = (w.getD i 0).testBit b := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases w[i]? <;> simp
lemma gv_bit {b : ℕ} (hb : m.testBit b = true) (w : List ℕ) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    (gv m w g).testBit b = g.op.eval (g.inputs.map fun i => (w.map (fun x => x.testBit b)).getD i false) := by
  have e1 : ∀ l, GateOp.and.eval l = l.all id := fun _ => rfl
  have e2 : ∀ l, GateOp.or.eval l = l.any id := fun _ => rfl
  have e3 : ∀ l, GateOp.not.eval l = !(l.headD false) := fun _ => rfl
  obtain ⟨o, l⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  simp only [getD_map]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  simp only at hlen
  rcases hop with rfl | rfl | rfl
  · match l, hlen with
    | [], _ => simp [gv, e1, hb]
    | [i], _ => simp [gv, e1]
    | [i, j], _ => simp [gv, e1]
  · match l, hlen with
    | [], _ => simp [gv, e2]
    | [i], _ => simp [gv, e2]
    | [i, j], _ => simp [gv, e2]
  · match l, hlen with
    | [], _ => simp [gv, e3, hb]
    | [i], _ => simp [gv, e3, hb]
    | [i, j], _ => simp [gv, e3, hb]
lemma ex_bit {b : ℕ} (hb : m.testBit b = true) (gs : List Gate) : ∀ (w : List ℕ),
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    (ex m gs w).map (fun x => x.testBit b) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (w.map (fun x => x.testBit b)) := by
  induction gs with
  | nil => intro w _; rfl
  | cons g gs ih =>
    intro w hg
    rw [List.foldl_cons, ← gv_bit m hb w g (hg g List.mem_cons_self)]
    have := ih (w ++ [gv m w g]) (fun x hx => hg x (List.mem_cons_of_mem _ hx))
    rw [List.map_append] at this
    exact this
end circuit
theorem fanInTwo_of {gates : List Gate} {o : ℕ}
    (h : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) :
    FanInTwo ⟨gates, o⟩ := by
  intro g hg; obtain ⟨ho, hl⟩ := h g hg
  exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using ho, hl⟩

lemma ex_sol_not {T : ℕ} (m : ℕ) (gs : List Gate) : ∀ (w : List ℕ) (S : Set ℕ),
    (∀ x ∈ w, x ∈ S) → 0 ∈ S → m ∈ S →
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    (∃ g ∈ gs, g.op = GateOp.not) →
    (∃ i, (ex m gs w).getD i 0 = T) →
    Sol Z0 m T (gs.length - 1) S ∨ ∃ t, 1 ≤ t ∧ ∃ S0 : Finset ℕ, (S0 : Set ℕ) ⊆ S ∧ Live Z0 m T gs.length t S0 := by
  induction gs with
  | nil => intro _ _ _ _ _ _ hnot; simp at hnot
  | cons g gs ih =>
    intro w S hw h0 hm hg hnot hT
    have hgs := fun x hx => hg x (List.mem_cons_of_mem _ hx)
    have rd := fun i => getD_mem hw h0 i
    have hwm_stay : gv m w g ∈ S → ∀ x ∈ w ++ [gv m w g], x ∈ S := fun h x hx => by
      simp only [List.mem_append, List.mem_singleton] at hx; rcases hx with hx | rfl; exact hw x hx; exact h
    have hwm_ins : ∀ x ∈ w ++ [gv m w g], x ∈ insert (gv m w g) S := fun x hx => by
      simp only [List.mem_append, List.mem_singleton] at hx; rcases hx with hx | rfl; exact Or.inr (hw x hx); exact Or.inl rfl
    obtain ⟨hop, hlen⟩ := hg g List.mem_cons_self
    obtain ⟨o, l⟩ := g
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with rfl | rfl | rfl
    · have hnot' : ∃ g' ∈ gs, g'.op = GateOp.not := by
        rcases hnot with ⟨g', hg', ho⟩; simp only [List.mem_cons] at hg'; rcases hg' with rfl | hg'; simp at ho; exact ⟨g', hg', ho⟩
      match l with
      | [] => exact Or.inl (ex_sol m gs (w ++ [gv m w ⟨.and, []⟩]) S (hwm_stay hm) h0 hm hgs hT)
      | [i] => exact Or.inl (ex_sol m gs (w ++ [gv m w ⟨.and, [i]⟩]) S (hwm_stay (rd i)) h0 hm hgs hT)
      | i :: j :: _ =>
        rcases ih (w ++ [gv m w ⟨.and, i :: j :: _⟩]) (insert (op false (w.getD i 0) (w.getD j 0)) S) hwm_ins (Or.inr h0) (Or.inr hm) hgs hnot' hT with hs | ⟨t, ht, S1, hS1, hl1⟩
        · exact Or.inl ((Sol.bi (d := false) (rd i) (rd j) (al0 _ _ _) hs).mono (by cases gs <;> simp at hnot' ⊢) subset_rfl)
        · by_cases hz : op false (w.getD i 0) (w.getD j 0) ∈ S1
          · by_cases hab : w.getD i 0 = w.getD j 0
            · have hsub : (S1 : Set ℕ) ⊆ S := fun x hx => (hS1 hx).elim (fun e => by subst e; rw [hab, op_self]; exact rd j) id
              exact Or.inl (hl1.sol.mono le_rfl hsub)
            · refine Or.inr ⟨t, ht, insert (w.getD i 0) (insert (w.getD j 0) (S1.erase (op false (w.getD i 0) (w.getD j 0)))), ?_, Live.bi hab (al0 _ _ _) (by rwa [Finset.insert_erase hz])⟩
              intro x hx; simp at hx; rcases hx with rfl | rfl | ⟨h1, h2⟩; exact rd i; exact rd j; exact (hS1 h1).resolve_left h2
          · exact Or.inl (hl1.sol.mono le_rfl (fun x hx => (hS1 hx).resolve_left (fun e => hz (e ▸ hx))))
    · have hnot' : ∃ g' ∈ gs, g'.op = GateOp.not := by
        rcases hnot with ⟨g', hg', ho⟩; simp only [List.mem_cons] at hg'; rcases hg' with rfl | hg'; simp at ho; exact ⟨g', hg', ho⟩
      match l with
      | [] => exact Or.inl (ex_sol m gs (w ++ [gv m w ⟨.or, []⟩]) S (hwm_stay h0) h0 hm hgs hT)
      | [i] => exact Or.inl (ex_sol m gs (w ++ [gv m w ⟨.or, [i]⟩]) S (hwm_stay (rd i)) h0 hm hgs hT)
      | i :: j :: _ =>
        rcases ih (w ++ [gv m w ⟨.or, i :: j :: _⟩]) (insert (op true (w.getD i 0) (w.getD j 0)) S) hwm_ins (Or.inr h0) (Or.inr hm) hgs hnot' hT with hs | ⟨t, ht, S1, hS1, hl1⟩
        · exact Or.inl ((Sol.bi (d := true) (rd i) (rd j) (al0 _ _ _) hs).mono (by cases gs <;> simp at hnot' ⊢) subset_rfl)
        · by_cases hz : op true (w.getD i 0) (w.getD j 0) ∈ S1
          · by_cases hab : w.getD i 0 = w.getD j 0
            · have hsub : (S1 : Set ℕ) ⊆ S := fun x hx => (hS1 hx).elim (fun e => by subst e; rw [hab, op_self]; exact rd j) id
              exact Or.inl (hl1.sol.mono le_rfl hsub)
            · refine Or.inr ⟨t, ht, insert (w.getD i 0) (insert (w.getD j 0) (S1.erase (op true (w.getD i 0) (w.getD j 0)))), ?_, Live.bi hab (al0 _ _ _) (by rwa [Finset.insert_erase hz])⟩
              intro x hx; simp at hx; rcases hx with rfl | rfl | ⟨h1, h2⟩; exact rd i; exact rd j; exact (hS1 h1).resolve_left h2
          · exact Or.inl (hl1.sol.mono le_rfl (fun x hx => (hS1 hx).resolve_left (fun e => hz (e ▸ hx))))
    · match l with
      | [] => exact Or.inl (ex_sol m gs (w ++ [gv m w ⟨.not, []⟩]) S (hwm_stay hm) h0 hm hgs hT)
      | i :: _ =>
        have go := ex_sol m gs (w ++ [gv m w ⟨.not, i :: _⟩]) (insert (w.getD i 0 ^^^ m) S) hwm_ins (Or.inr h0) (Or.inr hm) hgs hT
        obtain ⟨k, hk, t, S1, hS1, hl1⟩ := go.live
        by_cases hz : w.getD i 0 ^^^ m ∈ S1
        · have hsub : ((insert (w.getD i 0) (S1.erase (w.getD i 0 ^^^ m)) : Finset ℕ) : Set ℕ) ⊆ S := by
            intro x hx; simp at hx; rcases hx with rfl | ⟨h1, h2⟩; exact rd i; exact (hS1 h1).resolve_left h2
          have hlu : Live Z0 m T (k + 1) (t + 1) (insert (w.getD i 0) (S1.erase (w.getD i 0 ^^^ m))) := Live.un (by rwa [Finset.insert_erase hz])
          by_cases hkeq : k = gs.length
          · subst hkeq; exact Or.inr ⟨t + 1, by omega, _, hsub, hlu⟩
          · exact Or.inl (hlu.sol.mono (by simp; omega) hsub)
        · exact Or.inl (hl1.sol.mono (by simp; omega) (fun x hx => (hS1 hx).resolve_left (fun e => hz (e ▸ hx))))


section inst_data
def row3g0 : List (ℕ × ℕ) := [(22, 2), (26, 1), (28, 2), (38, 2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g0ok : row3g0.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g1 : List (ℕ × ℕ) := [(41, 2), (42, 1), (50, 1), (52, 2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g1ok : row3g1.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g2 : List (ℕ × ℕ) := [(56, 1), (70, 2), (76, 1), (82, 2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g2ok : row3g2.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g3 : List (ℕ × ℕ) := [(84, 4), (88, 2), (98, 2), (100, 2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g3ok : row3g3.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g4 : List (ℕ × ℕ) := [(112, 2), (133, 2), (137, 1), (140, 1)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g4ok : row3g4.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g5 : List (ℕ × ℕ) := [(145, 2), (148, 2), (152, 2), (161, 1)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g5ok : row3g5.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g6 : List (ℕ × ℕ) := [(164, 1), (168, 2), (176, 2), (196, 1)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g6ok : row3g6.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g7 : List (ℕ × ℕ) := [(200, 1), (208, 2), (224, 1), (265, 1)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g7ok : row3g7.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g8 : List (ℕ × ℕ) := [(273, 2), (289, 1), (296, 2), (385, 2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g8ok : row3g8.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g9 : List (ℕ × ℕ) := [(392, 1), (400, 2), (416, 1), (517, 2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g9ok : row3g9.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g10 : List (ℕ × ℕ) := [(518, 2), (529, 2), (530, 2), (532, 2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g10ok : row3g10.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g11 : List (ℕ × ℕ) := [(545, 2), (546, 2), (548, 2), (560, 2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g11ok : row3g11.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g12 : List (ℕ × ℕ) := [(578, 2), (580, 2), (592, 2), (608, 2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g12ok : row3g12.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g13 : List (ℕ × ℕ) := [(641, 4), (644, 2), (656, 2), (672, 2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g13ok : row3g13.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g14 : List (ℕ × ℕ) := [(769, 2), (784, 2), (800, 2), (896, 2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g14ok : row3g14.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g15 : List (ℕ × ℕ) := [(1029, 2), (1030, 1), (1033, 1), (1034, 1)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g15ok : row3g15.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g16 : List (ℕ × ℕ) := [(1036, 2), (1057, 1), (1058, 2), (1060, 1)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g16ok : row3g16.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g17 : List (ℕ × ℕ) := [(1064, 2), (1090, 1), (1092, 2), (1096, 2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g17ok : row3g17.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g18 : List (ℕ × ℕ) := [(1120, 1), (1153, 2), (1156, 4), (1160, 2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g18ok : row3g18.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g19 : List (ℕ × ℕ) := [(1184, 2), (1216, 2), (1288, 1), (1312, 1)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g19ok : row3g19.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g20 : List (ℕ × ℕ) := [(1537, 2), (1540, 2), (1568, 2), (1664, 2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g20ok : row3g20.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g21 : List (ℕ × ℕ) := [(1792, 1), (2053, 2), (2054, 1), (2057, 2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g21ok : row3g21.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g22 : List (ℕ × ℕ) := [(2058, 1), (2060, 1), (2065, 2), (2066, 2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g22ok : row3g22.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g23 : List (ℕ × ℕ) := [(2068, 2), (2072, 2), (2114, 1), (2116, 1)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g23ok : row3g23.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g24 : List (ℕ × ℕ) := [(2120, 1), (2128, 2), (2177, 4), (2180, 2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g24ok : row3g24.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g25 : List (ℕ × ℕ) := [(2184, 2), (2192, 2), (2305, 2), (2312, 2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g25ok : row3g25.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g26 : List (ℕ × ℕ) := [(2320, 2), (2432, 2), (2561, 2), (2564, 2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g26ok : row3g26.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g27 : List (ℕ × ℕ) := [(2576, 2), (2688, 2), (2816, 1), (3073, 2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g27ok : row3g27.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g28 : List (ℕ × ℕ) := [(3074, 2), (3076, 4), (3080, 4), (3136, 2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g28ok : row3g28.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g29 : List (ℕ × ℕ) := [(3200, 2), (3328, 1), (3584, 1)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g29ok : row3g29.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def rt3 : List (ℕ × ℕ) := row3g0 ++ row3g1 ++ row3g2 ++ row3g3 ++ row3g4 ++ row3g5 ++ row3g6 ++ row3g7 ++ row3g8 ++ row3g9 ++ row3g10 ++ row3g11 ++ row3g12 ++ row3g13 ++ row3g14 ++ row3g15 ++ row3g16 ++ row3g17 ++ row3g18 ++ row3g19 ++ row3g20 ++ row3g21 ++ row3g22 ++ row3g23 ++ row3g24 ++ row3g25 ++ row3g26 ++ row3g27 ++ row3g28 ++ row3g29
lemma r3 : rt3.all (fun e => okE [] (pr ([]) e.1) e) = true := by
  simp only [rt3, List.all_append, Bool.and_true, row3g0ok, row3g1ok, row3g2ok, row3g3ok, row3g4ok, row3g5ok, row3g6ok, row3g7ok, row3g8ok, row3g9ok, row3g10ok, row3g11ok, row3g12ok, row3g13ok, row3g14ok, row3g15ok, row3g16ok, row3g17ok, row3g18ok, row3g19ok, row3g20ok, row3g21ok, row3g22ok, row3g23ok, row3g24ok, row3g25ok, row3g26ok, row3g27ok, row3g28ok, row3g29ok]
lemma i3 : ∀ e ∈ rt3, Imp [] e.1 e.2 := okAll r3 (by simp)
def row2g0 : List (ℕ × ℕ) := [(5, 3), (6, 3), (9, 2), (10, 1)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row2g0ok : row2g0.all (fun e => okE [] (pr (rt3) e.1) e) = true := by decide +kernel
def row2g1 : List (ℕ × ℕ) := [(12, 2), (17, 3), (18, 3), (20, 5)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row2g1ok : row2g1.all (fun e => okE [] (pr (rt3) e.1) e) = true := by decide +kernel
def row2g2 : List (ℕ × ℕ) := [(24, 3), (33, 2), (34, 3), (36, 3)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row2g2ok : row2g2.all (fun e => okE [] (pr (rt3) e.1) e) = true := by decide +kernel
def row2g3 : List (ℕ × ℕ) := [(40, 3), (48, 3), (66, 3), (68, 5)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row2g3ok : row2g3.all (fun e => okE [] (pr (rt3) e.1) e) = true := by decide +kernel
def row2g4 : List (ℕ × ℕ) := [(72, 2), (80, 5), (96, 3), (129, 5)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row2g4ok : row2g4.all (fun e => okE [] (pr (rt3) e.1) e) = true := by decide +kernel
def row2g5 : List (ℕ × ℕ) := [(132, 5), (136, 4), (144, 6), (160, 4)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row2g5ok : row2g5.all (fun e => okE [] (pr (rt3) e.1) e) = true := by decide +kernel
def row2g6 : List (ℕ × ℕ) := [(192, 2), (257, 3), (264, 2), (272, 3)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row2g6ok : row2g6.all (fun e => okE [] (pr (rt3) e.1) e) = true := by decide +kernel
def row2g7 : List (ℕ × ℕ) := [(288, 2), (384, 3), (513, 5), (514, 3)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row2g7ok : row2g7.all (fun e => okE [] (pr (rt3) e.1) e) = true := by decide +kernel
def row2g8 : List (ℕ × ℕ) := [(516, 6), (528, 6), (544, 6), (576, 3)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row2g8ok : row2g8.all (fun e => okE [] (pr (rt3) e.1) e) = true := by decide +kernel
def row2g9 : List (ℕ × ℕ) := [(640, 5), (768, 3), (1025, 3), (1026, 2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row2g9ok : row2g9.all (fun e => okE [] (pr (rt3) e.1) e) = true := by decide +kernel
def row2g10 : List (ℕ × ℕ) := [(1028, 5), (1032, 5), (1056, 4), (1088, 3)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row2g10ok : row2g10.all (fun e => okE [] (pr (rt3) e.1) e) = true := by decide +kernel
def row2g11 : List (ℕ × ℕ) := [(1152, 5), (1280, 1), (1536, 3), (2049, 5)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row2g11ok : row2g11.all (fun e => okE [] (pr (rt3) e.1) e) = true := by decide +kernel
def row2g12 : List (ℕ × ℕ) := [(2050, 2), (2052, 5), (2056, 5), (2064, 6)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row2g12ok : row2g12.all (fun e => okE [] (pr (rt3) e.1) e) = true := by decide +kernel
def row2g13 : List (ℕ × ℕ) := [(2112, 2), (2176, 5), (2304, 3), (2560, 3)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row2g13ok : row2g13.all (fun e => okE [] (pr (rt3) e.1) e) = true := by decide +kernel
def row2g14 : List (ℕ × ℕ) := [(3072, 5)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row2g14ok : row2g14.all (fun e => okE [] (pr (rt3) e.1) e) = true := by decide +kernel
def rt2 : List (ℕ × ℕ) := row2g0 ++ row2g1 ++ row2g2 ++ row2g3 ++ row2g4 ++ row2g5 ++ row2g6 ++ row2g7 ++ row2g8 ++ row2g9 ++ row2g10 ++ row2g11 ++ row2g12 ++ row2g13 ++ row2g14
lemma r2 : rt2.all (fun e => okE [] (pr (rt3) e.1) e) = true := by
  simp only [rt2, List.all_append, Bool.and_true, row2g0ok, row2g1ok, row2g2ok, row2g3ok, row2g4ok, row2g5ok, row2g6ok, row2g7ok, row2g8ok, row2g9ok, row2g10ok, row2g11ok, row2g12ok, row2g13ok, row2g14ok]
lemma i2 : ∀ e ∈ rt2, Imp [] e.1 e.2 := okAll r2 (i3)
def row1g0 : List (ℕ × ℕ) := [(1, 6), (2, 4), (4, 8), (8, 6)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row1g0ok : row1g0.all (fun e => okE [] (pr (rt3 ++ rt2) e.1) e) = true := by decide +kernel
def row1g1 : List (ℕ × ℕ) := [(16, 9), (32, 7), (64, 6), (128, 9)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row1g1ok : row1g1.all (fun e => okE [] (pr (rt3 ++ rt2) e.1) e) = true := by decide +kernel
def row1g2 : List (ℕ × ℕ) := [(256, 4), (512, 9), (1024, 7), (2048, 8)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row1g2ok : row1g2.all (fun e => okE [] (pr (rt3 ++ rt2) e.1) e) = true := by decide +kernel
def rt1 : List (ℕ × ℕ) := row1g0 ++ row1g1 ++ row1g2
lemma r1 : rt1.all (fun e => okE [] (pr (rt3 ++ rt2) e.1) e) = true := by
  simp only [rt1, List.all_append, Bool.and_true, row1g0ok, row1g1ok, row1g2ok]
lemma i1 : ∀ e ∈ rt1, Imp [] e.1 e.2 := okAll r1 (apI i3 i2)
def rt : List (ℕ × ℕ) := (rt3 ++ rt2 ++ rt1).filter (fun e => Nat.ble 4 e.2)
lemma ir : ∀ e ∈ rt, Imp [] e.1 e.2 := fun e he => (apI (apI i3 i2) i1) e (List.mem_of_mem_filter he)
def memoCell (width shift : ℕ) : ℕ := Nat.land FF (Nat.shiftLeft (2 ^ width - 1) shift)
noncomputable section memo_data
def memoIter {α : Type} (base : α) (step : α → α) (wrap : Nat → α → α) : Nat → α
  | 0 => base
  | n + 1 => wrap (n + 1) (step (memoIter base step wrap n))

lemma memoIter_eq {α : Type} (base : α) (step : α → α) (wrap : Nat → α → α)
    (hw : ∀ n, wrap n (Nat.rec base (fun _ => step) n) = Nat.rec base (fun _ => step) n) :
    ∀ n, memoIter base step wrap n = Nat.rec base (fun _ => step) n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [memoIter, ih]
    exact hw (n + 1)

lemma subtypeList_sound {α : Type} {p : α → Prop} (xs : List {x : α // p x}) :
    ∀ x ∈ xs.map Subtype.val, p x := by
  intro x hx
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hx
  exact a.property

lemma checkedChunks_sound {α : Type} (F : α → Bool)
    (chunks : List {xs : List α // xs.all (fun x => !(F x)) = true}) :
    ∀ x ∈ (chunks.map Subtype.val).flatten, F x = false := by
  intro x hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hxs
  have hf := List.all_eq_true.mp a.property x hx
  cases h : F x <;> simp_all


abbrev Runner := Nat → Nat → Nat → List W → Bool
abbrev WireKey := Nat × Nat × Nat × Nat × Nat
abbrev MemoKey := Nat × Nat × Nat × Nat × List WireKey

def packW (v : List W) : List WireKey := v.map (fun w => (w.s,w.a,w.b,w.c,w.r))
def unpackW (v : List WireKey) : List W := v.map (fun (s,a,b,c,r) => ⟨s,a,b,c,r⟩)
lemma unpack_pack (v : List W) : unpackW (packW v) = v := by
  induction v with
  | nil => rfl
  | cons w v ih => cases w; simpa only [packW,unpackW,List.map_cons] using congrArg (List.cons _) ih

def keyRun (run : Nat → Runner) (e : MemoKey) : Bool :=
  run e.1 e.2.1 e.2.2.1 e.2.2.2.1 (unpackW e.2.2.2.2)
def memoWrap (keys : List MemoKey) (fuel : Nat) (run : Runner) : Runner :=
  fun k t z v => if k = 10 then if keys.contains (fuel,k,t,z,packW v) then false else run k t z v else run k t z v
lemma memoWrap_eq (keys : List MemoKey) (run : Nat → Runner)
    (h : ∀ e ∈ keys, keyRun run e = false) (fuel : Nat) : memoWrap keys fuel (run fuel) = run fuel := by
  funext k t z v
  unfold memoWrap
  split_ifs with hk hm
  · have he := h (fuel,k,t,z,packW v) (List.contains_iff_mem.mp hm)
    simpa only [keyRun,unpack_pack] using he.symm
  · rfl
  · rfl

def memoStepC (NN AA HX HY l m g : Nat) (ih : Runner) : Runner := fun k t z v => Bool.rec (motive := fun _ => Bool) (tstC NN AA HX HY (pos t) l (Nat.sub (Nat.succ k) t) v (fun y => mvC NN AA HX HY ih l m g k t z v y)) true (Nat.ble v.length 1)

def memoStepS (NN AA HX HY l m g K : Nat) (baseRun : Nat → Runner) (ih : Runner) : Runner := fun k t z v => Bool.rec (motive := fun _ => Bool) (tstC NN AA HX HY (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
      Bool.rec (motive := fun _ => Bool) (mvC NN AA HX HY (baseRun K) l m g k t z v y) true
        (nodeC NN (ih (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) v.length z v pairsS))) true (Nat.ble v.length 1)

def memoLookC (NN AA HX HY l m g : Nat) (keys : List MemoKey) : Nat → Runner :=
  memoIter (fun _ _ _ _ => true) (memoStepC NN AA HX HY l m g) (memoWrap keys)
lemma memoLookC_eq (NN AA HX HY l m g : Nat) (keys : List MemoKey)
    (h : ∀ e ∈ keys, keyRun (lookC NN AA HX HY l m g) e = false) :
    memoLookC NN AA HX HY l m g keys = lookC NN AA HX HY l m g := by
  funext fuel
  apply memoIter_eq
  intro n
  exact memoWrap_eq keys (lookC NN AA HX HY l m g) h n

def memoLookS (NN AA HX HY l m g K : Nat) (keysC keysS : List MemoKey) : Nat → Runner :=
  memoIter (fun _ _ _ _ => true)
    (memoStepS NN AA HX HY l m g K (memoLookC NN AA HX HY l m g keysC)) (memoWrap keysS)
lemma memoLookS_eq (NN AA HX HY l m g K : Nat) (keysC keysS : List MemoKey)
    (hC : ∀ e ∈ keysC, keyRun (lookC NN AA HX HY l m g) e = false)
    (hS : ∀ e ∈ keysS, keyRun (look1C NN AA HX HY l m g K) e = false) :
    memoLookS NN AA HX HY l m g K keysC keysS = look1C NN AA HX HY l m g K := by
  unfold memoLookS
  rw [memoLookC_eq NN AA HX HY l m g keysC hC]
  funext fuel
  apply memoIter_eq
  intro n
  exact memoWrap_eq keysS (look1C NN AA HX HY l m g K) hS n
def memoNat (xs : List Nat) : Nat := xs.foldr (fun x a => x + 18446744073709551616 * a) 0
def mn6 : Nat := memoNat [18374966859414961920,18437736880628760576,288138016101237677,12878817335954112192,3109755040310333597,2204256310830837,10772610308670226432,4220660260489565632,14411561356322408726,144022820509190858,8068761682857377792,549420269568]
def mn7 : Nat := 2 ^ 25 + 2 ^ 55 + 2 ^ 100 + 2 ^ 125 + 2 ^ 160
def mn8 : Nat := memoNat [32,69273664,4611686018427387904]
def mn9 : Nat := mn7 + (memoNat [32,69273664,4611686018427387904])
def mn10 : Nat := memoNat [17361641481138401520,3377619726790655,9511496860259320736,7643080346361135133,9697667896650000969,1840690998040130,9889904781705609216,3031212968811727108,9317988457543452804,144009638449252996,6917810296862021632,549244108800]
def mn11 : Nat := memoNat [1125935341372417,72057596185413632,134217728]
def mn12 : Nat := 2 ^ 185
def mn13 : Nat := mn11 + (2 ^ 185)
def mn14 : Nat := memoNat [14757395258967641292,3377566844936192,4323323701165554572,8121481554142690844,1069681015657296411,1597125839119595,6845471433603153920,1786707045623291814,9278140775125812701,11673198296087658543,1150950922138878975,4190208]
def mn15 : Nat := 2 ^ 150
def mn16 : Nat := memoNat [1190111385904776224,70368811286530,4503599627370624]
def mn17 : Nat := mn16 + (2 ^ 150)
def mn18 : Nat := memoNat [12297829382473034410,18439988731982082047,13258645680802494509,13442934226108285121,11668083973276817606,693004704395837,2494994193563254784,19198058348814946,4902599546693493291,10088067554888122385,7516193791,2047]
def mn19 : Nat := memoNat [35184372121632,2251799813685312,131072]
def mn20 : Nat := 1 + 2 ^ 35 + 2 ^ 40 + 2 ^ 175
def mn21 : Nat := mn19 + (1 + 2 ^ 35 + 2 ^ 40 + 2 ^ 175)
def mn22 : Nat := memoNat [18446744069414584320,0,13546735319465850880,16888781545144029,3441133003059626014,2217560074290936,17870283321406128128,8725990566066176,998461023428112352,2812,8069042975902007296,549449627647]
def mn23 : Nat := 2 ^ 65 + 2 ^ 85 + 2 ^ 105 + 2 ^ 170
def mn24 : Nat := memoNat [34635776,2380152403065307136,4228,256]
def mn25 : Nat := mn24 + (2 ^ 65 + 2 ^ 85 + 2 ^ 105 + 2 ^ 170)
def mn26 : Nat := mn22 - ((memoNat [4294836225,17605133979245346816,4396637214463,2111132801318307840,5076158837197126284,3355468806,1297056483892002816,7045825825656282944,2533547625842465,11817537781196914688,123123824698368]) * 2 ^ 16)
def mn27 : Nat := memoNat [1152922605192216577,65536,137438953476]
def mn28 : Nat := memoNat [34604032,72638634393600,4096,8]
def mn29 : Nat := mn27 + (memoNat [34604032,72638634393600,4096,8])
def mn455 : Nat := memoNat [3122880946823089843,8330789845346723177,12622123099851798986,4500]
def mn456 : Nat := mn455 - (memoNat [34635776,2380154602090659842,4398046515332,256])
def mn457 : Nat := memoNat [3050823352717005459,6025012740187331877,8010428276741450182,4508]
def mn458 : Nat := memoNat [3086852149734888051,5950705614011274471,3398746660655536450,4252]
def mn459 : Nat := memoNat [3120629076106791601,8258798288574256485,12477999115414481350,4508]
def mn460 : Nat := mn458 + (memoNat [34902861678640191,66708441216,8935141664863813632])
def mn461 : Nat := memoNat [1932769560883711635,8330785518095869285,12617610704123013446,4508]
def mn462 : Nat := memoNat [742658174944365171,5950564945244628325,12613111502546344258,4252]
def mn463 : Nat := mn459 + (memoNat [2180368066119617,69805798519213952,143974450855673856])
def mn464 : Nat := mn460 + (memoNat [1088483225502687,2147485632,287948901309087744])
def mn465 : Nat := memoNat [3048571482035341969,5955211339716728105,7866321884490185290,4764]
def mn466 : Nat := memoNat [3085726214429232754,8333112013766038761,3110520682416126538,4764]
def mn467 : Nat := memoNat [1896740763832274547,6099256163276266791,8005933473198717386,4764]
def mn468 : Nat := mn462 + (memoNat [35651584,2454463927218466688,9223376430606327816,511])
def mn469 : Nat := memoNat [3050751850102477426,6094822932460182761,8010296335345859146,4764]
def mn470 : Nat := mn466 + (memoNat [1088483226518527,69805796371726336,287948901309087744])
def mn471 : Nat := memoNat [1931643590142446225,10566827126841054567,12473504311871748554,4764]
def mn472 : Nat := memoNat [742658139579042418,10638814354215181669,12324885524306934090,4764]
def mn473 : Nat := memoNat [3120557607884507761,10562393896024970473,12477867174018890314,4764]
def mn474 : Nat := memoNat [3121717593726635665,10636703292024069417,12333611248589027914,4764]
def mn475 : Nat := mn471 + (memoNat [1089652532413409,139611592743456640,143974450855673856])
def mn476 : Nat := memoNat [742655907270838897,10708620150586909989,12612834425616021834,4764]
def mn477 : Nat := mn458 + (memoNat [34668544,2454463995942338562,4398046515464,512])
def mn478 : Nat := mn460 + (memoNat [34668544,4688249411118039042,4398046515464,512])
def mn479 : Nat := mn476 + (memoNat [1152923772314976258,2251799813685314,281474976837632])
def mn480 : Nat := mn464 + (memoNat [1099546263553,4758055205342281730,4398046515464,512])
def mn481 : Nat := memoNat [4203745957909188244,3644789897513049383,8010432812226914630,4244]
def mn482 : Nat := memoNat [4273551681298974386,5878575445899973991,12478003650899945798,4244]
def mn483 : Nat := memoNat [4274677616640346803,5950637440136093035,12333897259051329862,4244]
def mn484 : Nat := mn455 - (memoNat [37188780712559647,72567834476544,4503462196805760])
def mn485 : Nat := mn484 - (memoNat [34635776,2380154602090659842,4398046515332,256])
def mn486 : Nat := mn482 + (memoNat [2180368066119617,69805798519213952,143974450855673856])
def mn487 : Nat := mn458 + (memoNat [29696,74095944716582916,8796093022340,232])
def mn488 : Nat := mn460 + (memoNat [30720,2307881293322387460,8796093022340,232])
def mn489 : Nat := mn484 + (memoNat [18446742973124182015,2199025287167,4260607557628])
def mn490 : Nat := memoNat [1895579679551178355,8330644567945815399,12613120298639366342,4484]
def mn491 : Nat := memoNat [4275767199377476243,8328465406900806955,12621846160360417738,4492]
def mn492 : Nat := mn491 - (memoNat [1152922605226820609,72638634459136,137438957572,8])
def mn493 : Nat := memoNat [4201494087227524754,3574988497042445611,7866326419975649738,4500]
def mn494 : Nat := memoNat [4238648819621415539,5952889171091756267,3110525217901590986,4500]
def mn495 : Nat := memoNat [3049663369024457332,3719033320601984297,8005938008684181834,4500]
def mn496 : Nat := memoNat [1895580780172199540,6024806029788812519,3389748394928584906,4500]
def mn497 : Nat := memoNat [4203674455294660211,3714600089785900267,8010300870831323594,4500]
def mn498 : Nat := mn494 + (memoNat [1088483226518527,69805796371726336,287948901309087744])
def mn499 : Nat := mn489 - (memoNat [1124870190531585,144115192370761728,144115050905337852])
def mn500 : Nat := memoNat [1895580744771225203,8258591511540899175,12324890059792398538,4500]
def mn501 : Nat := memoNat [4273480213076690546,8182171053350687979,12477871709504354762,4500]
def mn502 : Nat := memoNat [4274640198918818450,8256480449349786923,12333615784074492362,4500]
def mn503 : Nat := mn489 - (memoNat [35217658118176,4503599627305088,140600049663996])
def mn504 : Nat := mn489 - (memoNat [1190112553062138913,2322168624906306,4784937161064572])
def mn505 : Nat := mn481 + (memoNat [34635776,2380156869833392132,8796093026436,256])
def mn506 : Nat := mn505 - (memoNat [34636800,2380225041699700736,4228,264])
def mn507 : Nat := memoNat [4239774754961705588,5950564803510637803,3398755594187516230,4236]
def mn508 : Nat := mn501 + (memoNat [71468256920640,76561195812782208,140737488617472])
def mn509 : Nat := mn508 - (memoNat [34636800,2380225041699700736,4228,264])
def mn510 : Nat := mn483 - (memoNat [0,72636486909952,0,8])
def mn511 : Nat := mn484 + (2 ^ 85 + 2 ^ 105 + 2 ^ 170)
def mn512 : Nat := mn511 - (memoNat [34636800,2380225041699700736,4228,264])
def mn513 : Nat := mn507 + (memoNat [16102550098919030784,4329595,9214364841890807808])
def mn514 : Nat := mn486 + (memoNat [34635776,2380156801116012548,8796093026436,256])
def mn515 : Nat := mn514 - (memoNat [34636800,2380225041699700736,4228,264])
def mn516 : Nat := mn510 + (memoNat [1088483225501663,1984,287948901309087744])
def mn517 : Nat := memoNat [5356668563169597045,8330930586995823849,3398751329284995530,4516]
def mn518 : Nat := mn517 - (memoNat [34635776,2380154602090659842,4398046515332,256])
def mn519 : Nat := memoNat [5354416692454346387,5953025581465701669,7866313363275069898,4516]
def mn520 : Nat := memoNat [5355542627795718804,6025087575701820713,7722206971426453962,4516]
def mn521 : Nat := mn520 - (memoNat [34635776,2380154602090659842,4398046515332,256])
def mn522 : Nat := memoNat [4166557177265902197,8405167413077974311,8005929350030117326,4772]
def mn523 : Nat := mn522 - (memoNat [34635776,2380154602090659842,4398046515332,256])
def mn524 : Nat := memoNat [2976445791291919957,3644792238136073509,8001425750406932806,4260]
def mn525 : Nat := memoNat [5356597060555101780,8402985982075575463,8010292212177259086,4772]
def mn526 : Nat := mn525 - (memoNat [34635776,2380154602090659842,4398046515332,256])
def mn527 : Nat := mn521 + (memoNat [1088483225502687,2147485632,287948901309087744])
def mn528 : Nat := mn477 - (memoNat [108086391089397760,4611688354889596928,12884897796])
def mn529 : Nat := Nat.xor mn465 (memoNat [2251293698,2305858404530264064,12])
def mn530 : Nat := memoNat [4202620022568930963,8333037109607830825,7722206833987496522,4756]
def mn531 : Nat := mn467 - (memoNat [17329851366088114176,16140903263517016063,3])
def mn532 : Nat := memoNat [2976444690706550356,8405094703511543077,8001430011014490442,4756]
def mn533 : Nat := Nat.xor mn469 (memoNat [1099612291105,2305858402382774336,12])
def mn534 : Nat := mn530 + (memoNat [1089582737096672,69805794224244672,287948901309087744])
def mn535 : Nat := memoNat [5282359098382896755,3649438632608173289,3254636132350773838,4772]
def mn536 : Nat := mn466 + (memoNat [2269816413400073218,70370893889536,270582943748,8])
def mn537 : Nat := memoNat [4130528380179829333,3793483456167711975,3394247721059305934,4772]
def mn538 : Nat := mn469 + (memoNat [2269816413400073218,70370893889536,270582943748,8])
def mn539 : Nat := memoNat [5284539466450032212,3789050225351627945,3398610583206447694,4772]
def mn540 : Nat := memoNat [4165431206490001011,8261054419732499751,7861818559732337102,4772]
def mn541 : Nat := memoNat [2976445755926597204,8333041647106626853,7713199772167522638,4772]
def mn542 : Nat := memoNat [5354345224232062547,8256621188916415657,7866181421879478862,4772]
def mn543 : Nat := memoNat [5355505210074190451,8330930584915514601,7721925496449616462,4772]
def mn544 : Nat := mn522 - (memoNat [36318243487777,4501400602017920,136339442106368])
def mn545 : Nat := mn525 - (memoNat [2380153536936708097,138538597220290,9143538700648704])
def mn546 : Nat := mn467 + (memoNat [1118053791900402720,68169788030976,4499197294280828])
def mn547 : Nat := mn528 + (memoNat [32,18446741874751309884,4611677222334365695])
def mn548 : Nat := mn481 + (memoNat [33619968,4760307073875443714,4398046511364,512])
def mn549 : Nat := mn548 - ((memoNat [1152922605192216577,68719544320,131200]) * 2 ^ 25)
def mn550 : Nat := memoNat [5318387895435415187,5955279511585262887,7866317757026617934,4772]
def mn551 : Nat := mn535 + (memoNat [32,18446739675728117820,4611677222334365695])
def mn552 : Nat := mn536 + (memoNat [32,69271616,4611686018427387904])
def mn553 : Nat := mn552 - ((memoNat [1152922605192216577,68719544320,131200]) * 2 ^ 25)
def mn554 : Nat := mn522 - (2 ^ 25 + 2 ^ 100 + 2 ^ 125 + 2 ^ 160)
def mn555 : Nat := mn537 + (memoNat [32,18446739675728119870,4611677222334365695])
def mn556 : Nat := mn532 + (memoNat [36029897673539585,4539780497410,137438961668,16])
def mn557 : Nat := mn524 + ((memoNat [17,72129133160660992,4503599627368448]) * 2 ^ 21)
def mn558 : Nat := mn538 - (memoNat [32,2199025352770,4398046511104])
def mn559 : Nat := mn539 + (memoNat [0,18446739675728119804,4611677222334365695])
def mn560 : Nat := mn527 + (memoNat [69238784,4758055205342281730,4398046519560,512])
def mn561 : Nat := mn525 - (memoNat [35994746551795681,2305843077933170624,140741783191552])
def mn562 : Nat := memoNat [5390445489472228979,5878718455289644263,3254631747189156166,4260]
def mn563 : Nat := mn518 - (memoNat [1154082588885812256,70300093906944,4503595340791936])
def mn564 : Nat := mn518 - (memoNat [18410786779306164289,2251731096305791,140733193650176])
def mn565 : Nat := memoNat [3084600281235312243,8186745025880687851,3254640268404271554,4508]
def mn566 : Nat := mn494 - (memoNat [34601984,16140903261369534464,8195])
def mn567 : Nat := memoNat [3049662268471594579,8330789847292744937,3394251857112803650,4508]
def mn568 : Nat := mn496 - (memoNat [17329851366157318208,16140762526162878463,8195])
def mn569 : Nat := mn477 - (memoNat [70403104014400,78812993476952190,136339442106504,256])
def mn570 : Nat := Nat.xor mn498 (memoNat [1099614388257,2305858402382774336,8204])
def mn571 : Nat := memoNat [4201460003507883603,8186747293556442345,3250136943646423370,4516]
def mn572 : Nat := memoNat [3012474552944479796,8258734520930569447,3101518156081608906,4516]
def mn573 : Nat := memoNat [5390374021249945139,8182314062740358251,3254499805793565130,4516]
def mn574 : Nat := memoNat [5391534007092073043,8256623458739457195,3110243880363702730,4516]
def mn575 : Nat := mn517 - (memoNat [1154118907129300033,4571700695924864,4639934782898304])
def mn576 : Nat := mn517 - (memoNat [2344196242533320770,2390269693526082,9284271894298880])
def mn577 : Nat := mn569 + (memoNat [70403103981632,4503599627436160,140737488617476])
def mn578 : Nat := mn562 + (memoNat [34635776,2380156801116014596,8796093026436,256])
def mn579 : Nat := mn563 + (memoNat [34635776,2380156801116012546,8796093026436,256])
def mn580 : Nat := mn564 + (memoNat [34635808,2380156801116012612,8796093026436,256])
def mn581 : Nat := mn517 + (memoNat [69805723357280318,133278335104,8935141669024563200])
def mn582 : Nat := mn581 - (memoNat [34635776,2380154602090659842,4398046515332,256])
def mn583 : Nat := mn581 - (memoNat [1125935341372417,72057596185413632,144115188210073600])
def mn584 : Nat := mn583 - (memoNat [34635776,2380154602090659842,4398046515332,256])
def mn585 : Nat := memoNat [4236362900621052563,8258798359374239077,12473495790656633162,4516]
def mn586 : Nat := memoNat [3046251514681706099,5878577786522998117,12468996589079963974,4260]
def mn587 : Nat := memoNat [5426402783910252146,8256616928371840229,12477858652803774922,4516]
def mn588 : Nat := mn562 + (memoNat [35991344904142878,68855926848,9223090566172901376])
def mn589 : Nat := mn529 - (memoNat [2147484674,2233785348605804544])
def mn590 : Nat := memoNat [4237522884280075890,8333037242680509673,3254636007796714058,4756]
def mn591 : Nat := memoNat [4272425745958717105,10566822657994755433,12189777672660527690,4756]
def mn592 : Nat := mn471 - (memoNat [17294948469008499712,18374688678694879231,3])
def mn593 : Nat := memoNat [3046250414096336498,10638880251898467685,12469000849687521610,4756]
def mn594 : Nat := Nat.xor mn473 (memoNat [1133874511872,72072987200716800,12])
def mn595 : Nat := mn591 + (memoNat [1089582737096672,69805794224244672,287948901309087744])
def mn596 : Nat := memoNat [5389319554166573682,8261124855044408553,2966405768949746254,4772]
def mn597 : Nat := mn540 - (memoNat [18411841176629937152,2233785415177863167])
def mn598 : Nat := mn586 + (memoNat [35651584,2454463927218466688,9223376430606327816,511])
def mn599 : Nat := mn542 - (memoNat [34392244193,2233785415177863104])
def mn600 : Nat := mn596 + (memoNat [1088483226518527,69805796371726336,287948901309087744])
def mn601 : Nat := memoNat [3046251479316383346,10566827195493551461,12180770610840553806,4772]
def mn602 : Nat := memoNat [5425310933463976593,10564716133302439209,12189496335122647630,4772]
def mn603 : Nat := memoNat [4236326582412200562,10634451560862880999,12473363849261042126,4772]
def mn604 : Nat := memoNat [3046249247008179825,10636632991865279781,12468719512149641550,4772]
def mn605 : Nat := mn471 + (memoNat [1187859552806141985,68169785931776,4499201455030396])
def mn606 : Nat := mn595 + (memoNat [36352604275745,2254000984424512,281474976841728])
def mn607 : Nat := Nat.xor mn591 (memoNat [0,6291470,288243570291245056])
def mn608 : Nat := mn550 + (memoNat [34902861678640127,66571993088,4160749568])
def mn609 : Nat := mn535 + ((memoNat [103079215169,4466766184448,12288]) * 2 ^ 20)
def mn610 : Nat := mn596 + (memoNat [0,18446741874686296062,288225978105200639])
def mn611 : Nat := mn603 + (memoNat [36282808959008,18379187878126155904,136339307888639])
def mn612 : Nat := mn604 + (memoNat [1128167649575938,2251799813685314,281474976841728])
def mn613 : Nat := Nat.xor mn601 ((memoNat [7340035,137445244928]) * 2 ^ 85)
def mn614 : Nat := memoNat [5425276882963221106,10562462134463401191,12477863050716072526,4772]
def mn615 : Nat := mn604 + (memoNat [2380187621797169185,140737622573060,9007199258935552])
def mn616 : Nat := mn602 + (memoNat [0,18446741874684198910,288225978105200639])
def mn617 : Nat := mn581 - (memoNat [1188985450564452383,70366663800832,4503599501541504])
def mn618 : Nat := mn617 - (memoNat [34635776,2380154602090659842,4398046515332,256])
def mn619 : Nat := mn564 + (memoNat [34902861678640191,66708441216,8935141664863813632])
def mn620 : Nat := Nat.xor mn582 (memoNat [7923122665692193,13209176115276,853221425938432])
def mn621 : Nat := memoNat [3049697417376681618,3719174195596399915,7722211094595054018,4508]
def mn622 : Nat := mn566 - (memoNat [1024,2233785348605804544])
def mn623 : Nat := mn565 + (memoNat [34902861678640191,66708441216,8935141664863813632])
def mn624 : Nat := mn508 - (memoNat [68157440,2199023255552,432345564227575812])
def mn625 : Nat := memoNat [3084565130150234770,8330789914001186153,12329393521976617282,4508]
def mn626 : Nat := mn500 - (memoNat [17294948469077703680,18374547941206523903,8195])
def mn627 : Nat := mn569 + (memoNat [34902861678640191,66708441216,8935141664863813632])
def mn628 : Nat := Nat.xor mn502 (memoNat [1133941620736,72072987200716800,8204])
def mn629 : Nat := memoNat [5353290757079419538,3575131573140557099,7578096181128673738,4516]
def mn630 : Nat := mn578 - (2 ^ 25 + 2 ^ 85 + 2 ^ 125 + 2 ^ 185 + 2 ^ 186)
def mn631 : Nat := memoNat [4201460038876352116,3719176396700095785,7717707769837205834,4516]
def mn632 : Nat := mn572 - (memoNat [18411841176629937088,2233785415043645439])
def mn633 : Nat := mn520 - (memoNat [71502649163809,2310344409817808958,136339442106368])
def mn634 : Nat := mn574 - (memoNat [34392244193,2233785415177863104])
def mn635 : Nat := mn585 - (memoNat [35434528769,72050999109355516,288217182146396160])
def mn636 : Nat := mn612 - (memoNat [34635776,2380150204039954432,432341166181060740,256])
def mn637 : Nat := mn583 - (memoNat [71468256919616,76558994639945854,136339442106368])
def mn638 : Nat := mn581 - (memoNat [37417756164129,74307194826260542,288507453082042368])
def mn639 : Nat := mn617 - (memoNat [36318243487777,4501400602017920,136339442106368])
def mn640 : Nat := mn576 + (memoNat [34902861678640191,66708441216,8935141664863813632])
def mn641 : Nat := mn488 + (memoNat [34605056,72273308770369536,4096,24])
def mn642 : Nat := mn460 - (memoNat [0,18446741874682101756,144106391982833663])
def mn643 : Nat := mn483 - (2 ^ 105 + 2 ^ 185)
def mn644 : Nat := mn520 + (2 ^ 65 + 2 ^ 105 + 2 ^ 170)
def mn645 : Nat := mn521 - (memoNat [0,18446739675660943356,144106391982833663])
def mn646 : Nat := memoNat [5391571424813601396,5950780449523666155,2966410167264684358,4260]
def mn647 : Nat := mn617 + (2 ^ 85 + 2 ^ 105 + 2 ^ 170)
def mn648 : Nat := mn617 - (memoNat [34635776,2380150204039954432,144110790029348996,256])
def mn649 : Nat := mn632 - (memoNat [1015808,74309325127806848,9367487220635668356,255])
def mn650 : Nat := mn640 + (memoNat [2380153536936708097,140737622572996,9147936747159808])
def mn651 : Nat := mn564 + (memoNat [34902861678640191,4464759146628,8791035272880979968])
def mn652 : Nat := mn649 + (memoNat [2380185319694665758,140737622572996,8725724282093568])
def mn653 : Nat := memoNat [3048503385398038133,8330789986946557289,12613116175466576330,4516]
def mn654 : Nat := mn653 - (memoNat [34635776,2380154602090659842,4398046515332,256])
def mn655 : Nat := mn603 + (memoNat [2216686309607394,74307199121231872,144110790297780224])
def mn656 : Nat := mn655 - (memoNat [34635776,2380154602090659842,4398046515332,256])
def mn657 : Nat := mn563 + (memoNat [35991344904142878,68855926848,9223090566172901376])
def mn658 : Nat := Nat.xor mn531 ((memoNat [1099615437027,2]) * 2 ^ 60)
def mn659 : Nat := memoNat [3049663369056995924,8405024472202122473,3394247596505246154,4756]
def mn660 : Nat := mn471 - (memoNat [1125897758310398,2196875771902,4])
def mn661 : Nat := mn606 - (memoNat [1188985450564452383,72565687056384,148618787577397376])
def mn662 : Nat := Nat.xor mn479 (memoNat [34603008,15393162788864,20975628])
def mn663 : Nat := mn475 - (memoNat [34084860493855,2199023255550,4])
def mn664 : Nat := mn593 + (memoNat [39405399376397313,69735429842145220,148337312990625920])
def mn665 : Nat := mn597 - (memoNat [36028797020012544,72057594037925886])
def mn666 : Nat := mn536 - (memoNat [1154082588885812256,70300093906944,4503595340791936])
def mn667 : Nat := mn556 - (2 ^ 25 + 2 ^ 85 + 2 ^ 125 + 2 ^ 150 + 2 ^ 151)
def mn668 : Nat := mn544 - (memoNat [35184405676032,2305843009215791038])
def mn669 : Nat := memoNat [4202548522170012243,8402917880937747689,3393966258967366094,4772]
def mn670 : Nat := mn612 - (2 ^ 20 + 2 ^ 120 + 2 ^ 150 + 2 ^ 151)
def mn671 : Nat := mn603 - (memoNat [35150013431839,72057594037927934])
def mn672 : Nat := memoNat [4237451418240896627,10636703362824052009,12329107923831179726,4772]
def mn673 : Nat := mn612 + (memoNat [1089652531364833,67553998705528704,143974450843090944])
def mn674 : Nat := mn461 + (memoNat [34635776,2380154602090659842,4398042321024,256])
def mn675 : Nat := mn674 - (memoNat [32768,2199025352706,4398050705536])
def mn676 : Nat := mn485 + (memoNat [32768,4760307005155966978,4398046511236,512])
def mn677 : Nat := Nat.xor mn485 ((memoNat [17179921507,2097152]) * 2 ^ 116)
def mn678 : Nat := mn522 - (2 ^ 25 + 2 ^ 125 + 2 ^ 150)
def mn679 : Nat := mn554 - (memoNat [32768,2130305875970,4393759932544])
def mn680 : Nat := mn669 + (memoNat [37452114821122,2251799815782400,281474976841600])
def mn681 : Nat := mn680 - (memoNat [32768,2199025352706,4398050705536])
def mn682 : Nat := mn611 + (memoNat [35433480193,2147485696,130023424])
def mn683 : Nat := mn682 - (memoNat [32768,2199025352706,4398050705536])
def mn684 : Nat := mn617 + (memoNat [33554432,2308094809027379200,4100,256])
def mn685 : Nat := mn672 + (memoNat [37417755050017,2249600788332606,277076926136064])
def mn686 : Nat := mn655 - (2 ^ 115 + 2 ^ 150)
def mn687 : Nat := mn686 - (memoNat [32768,2199025352706,4398050705536])
def mn688 : Nat := mn664 + (memoNat [1152921505749796864,145277268852736,137438961540,16])
def mn689 : Nat := mn688 - (memoNat [32768,2199025352706,4398050705536])
def mn690 : Nat := mn654 - (memoNat [71502615576641,2251799813685378,140737484423168])
def mn691 : Nat := memoNat [670600580907518547,3719033460121312553,8001434271622048194,4508]
def mn692 : Nat := mn496 - (memoNat [36028797054550080,2130437931006,7940])
def mn693 : Nat := memoNat [740406306444789363,8186604357114041705,12469005110295079362,4508]
def mn694 : Nat := mn500 - (memoNat [1125899974934528,2196875771902,7940])
def mn695 : Nat := mn461 - (memoNat [1190181789008692320,4569570385854588,4631142972260228])
def mn696 : Nat := mn489 - (memoNat [1190146637991773248,2324367648161856,4784937161072512])
def mn697 : Nat := memoNat [2974193920610256467,3574990837665469737,7857319358155667914,4516]
def mn698 : Nat := mn632 + (memoNat [18410715276689604544,18374686479537408001,255])
def mn699 : Nat := memoNat [2976374288677391924,3714602430408924393,8001293809011341770,4516]
def mn700 : Nat := Nat.xor mn576 (memoNat [35184405741568,2305843009219985486,256])
def mn701 : Nat := mn585 - (memoNat [1190182854161630304,76624965400526972,4631142972260224])
def mn702 : Nat := Nat.xor mn640 (memoNat [35218732974113,72057594037927950,256])
def mn703 : Nat := mn461 - (memoNat [37189881297863712,65970758483964,4490405483642752])
def mn704 : Nat := mn523 - (memoNat [1154082588885746720,63771737325564,4490405483642752])
def mn705 : Nat := mn636 + (memoNat [65536,2,432345564227567872])
def mn706 : Nat := mn653 - (memoNat [36318243487777,2249600788332672,136339437912064])
def mn707 : Nat := mn581 + (memoNat [2179234193737664,4294971264,287948901443174400])
def mn708 : Nat := mn582 + (memoNat [2179234193737664,4294971264,287948901443174400])
def mn709 : Nat := mn707 - (memoNat [36318243487777,2251799813685312,140737488486400])
def mn710 : Nat := mn564 + (memoNat [35991344904142878,68855926848,9223090566172901376])
def mn711 : Nat := mn533 - (memoNat [1099511595009,2303591140682563584])
def mn712 : Nat := mn590 + (memoNat [2180368066119617,69805798519213952,143974450855673856])
def mn713 : Nat := mn594 - (memoNat [1097364110335,69805792076759040])
def mn714 : Nat := Nat.xor mn595 (memoNat [8127659748886755,4294969792,433330727049625600])
def mn715 : Nat := mn663 + (memoNat [1152920405095251967,2251799813685246])
def mn716 : Nat := mn593 + (memoNat [2180368066119617,69805798519213952,143974450855673856])
def mn717 : Nat := mn594 + (memoNat [2180368066119617,69805798519213952,143974450855673856])
def mn718 : Nat := mn606 + (memoNat [2144015461843872,67551797534789440,143692975878832128])
def mn719 : Nat := mn599 - (memoNat [1015840,69805794224240704])
def mn720 : Nat := mn596 + (memoNat [2180368066119617,69805798519213952,143974450855673856])
def mn721 : Nat := mn668 + (memoNat [36028797018996704,2251799813685182])
def mn722 : Nat := mn669 - (memoNat [1154116639386534943,70368677068932,4362862134952064])
def mn723 : Nat := mn525 - (memoNat [71502649163809,2310344409817808958,136339442106368])
def mn724 : Nat := mn720 + (memoNat [1088483226518527,69805796371726336,287948901309087744])
def mn725 : Nat := mn671 + (memoNat [1125865547138047,2251799813685246])
def mn726 : Nat := mn673 - (memoNat [35219806617633,69805796371728386,288230376273346560])
def mn727 : Nat := mn615 - (memoNat [105553117380704,76561193665298624,393216])
def mn728 : Nat := mn602 + (memoNat [2180368066119617,69805798519213952,143974450855673856])
def mn729 : Nat := mn688 - (memoNat [70368744210496,4503599627370690,393088])
def mn730 : Nat := mn673 - (memoNat [37452114821154,66,281474964258816])
def mn731 : Nat := mn717 + (memoNat [35218731860000,2251799811588158,136339441975296])
def mn732 : Nat := Nat.xor mn717 ((memoNat [2251806256136199,64,28928]) * 2 ^ 35)
def mn733 : Nat := mn717 + (memoNat [2305915613488414786,4505798650757248,141012366524424])
def mn734 : Nat := mn475 + (memoNat [3495886227544998882,68169786064832,4499476467024004])
def mn735 : Nat := mn486 + (memoNat [65536,4760307005155966978,4398046511364,512])
def mn736 : Nat := mn735 - (memoNat [35184372121632,2253998839038018,4398046642176])
def mn737 : Nat := mn525 - ((memoNat [1073742849,70437463654400,4]) * 2 ^ 15)
def mn738 : Nat := mn737 - (memoNat [35184372121632,2253998839038018,4398046642176])
def mn739 : Nat := mn539 + ((memoNat [3298534885377,140806214123520,393216]) * 2 ^ 15)
def mn740 : Nat := mn739 - (memoNat [35184372121632,2253998839038018,4398046642176])
def mn741 : Nat := mn614 + (memoNat [1090716608496608,2147485632,134086656])
def mn742 : Nat := Nat.xor mn727 ((memoNat [70368945504263,12,904]) * 2 ^ 40)
def mn743 : Nat := mn728 + (memoNat [37417755115553,2251799813685312,281474976841728])
def mn744 : Nat := mn743 - (memoNat [35184372121632,2253998839038018,4398046642176])
def mn745 : Nat := mn655 - (2 ^ 70 + 2 ^ 115 + 2 ^ 145)
def mn746 : Nat := mn686 - (memoNat [35184372121632,2253998839038082,4398042578944])
def mn747 : Nat := mn673 + (2 ^ 15 + 2 ^ 115 + 2 ^ 150 + 2 ^ 151)
def mn748 : Nat := mn673 - (memoNat [35184372088864,2199025352770,4398034059264])
def mn749 : Nat := mn621 + (memoNat [1088483225502687,2147485632,287948901309087744])
def mn750 : Nat := mn570 - (memoNat [1099511595009,2303591140682563584])
def mn751 : Nat := mn623 + (memoNat [1088483225502687,2147485632,287948901309087744])
def mn752 : Nat := mn628 - (memoNat [1099511593985,69805792076759040])
def mn753 : Nat := mn567 + (memoNat [35991344904142878,68855926848,9223090566172901376])
def mn754 : Nat := mn626 + (memoNat [1088483225502687,2147485632,287948901309087744])
def mn755 : Nat := mn463 - (memoNat [36352603226145,2247401760882746,268280837308420])
def mn756 : Nat := mn514 - (memoNat [2302171676674,2199023255552,422212465074180])
def mn757 : Nat := mn629 + (memoNat [1088483225502687,2147485632,287948901309087744])
def mn758 : Nat := mn634 - (memoNat [1015840,69805794224240704])
def mn759 : Nat := mn631 + (memoNat [1088483225502687,2147485632,287948901309087744])
def mn760 : Nat := mn576 - (memoNat [18410750461096230880,2303591209267888127])
def mn761 : Nat := mn633 + (memoNat [1088483225502687,2147485632,287948901309087744])
def mn762 : Nat := mn634 + (memoNat [1088483225502687,2147485632,287948901309087744])
def mn763 : Nat := mn635 + (memoNat [1088483225502687,2147485632,287948901309087744])
def mn764 : Nat := mn640 - (memoNat [18445653358175845408,69805794224242687])
def mn765 : Nat := mn587 - (memoNat [37417756164129,74302796775555130,268280837308416])
def mn766 : Nat := mn574 + (memoNat [35991344904142878,68855926848,9223090566172901376])
def mn767 : Nat := mn656 - (memoNat [2267742732290,2245202737627196,268280837308416])
def mn768 : Nat := mn706 - (memoNat [3401614131203,2,422212465066240])
def mn769 : Nat := mn492 + (memoNat [34638848,2467516693610496,4096,24])
def mn770 : Nat := Nat.xor mn464 ((memoNat [2251806256136193,448,4352]) * 2 ^ 35)
def mn771 : Nat := Nat.xor mn456 (memoNat [1152958036524924961,4259916,994095950594048])
def mn772 : Nat := mn707 + (memoNat [18410750461062676512,2130305876033,4393751674880])
def mn773 : Nat := mn771 + (memoNat [1116892708661626880,145208549376000,133143986176,16])
def mn774 : Nat := mn527 + (memoNat [34635776,2380156801113915396,8796093026436,256])
def mn775 : Nat := mn645 + (memoNat [1087349354136542,2147485632,431923351896588288])
def mn776 : Nat := mn563 + (memoNat [1190072799918588925,74766859894724,4090183263584384])
def mn777 : Nat := mn638 + (2 ^ 15 + 2 ^ 115 + 2 ^ 185 + 2 ^ 186)
def mn778 : Nat := Nat.xor mn588 ((memoNat [70368945504257,12,136]) * 2 ^ 40)
def mn779 : Nat := Nat.xor mn582 (memoNat [7924222177319969,13209176115276,993958914293760])
def mn780 : Nat := mn688 - ((memoNat [33,72130230522740734,4503599623176192]) * 2 ^ 20)
def mn781 : Nat := mn654 + (memoNat [1190072799918523389,74766861991874,4090183255195520])
def mn782 : Nat := mn649 + (memoNat [1087349354136542,2147485632,431923351896588288])
def mn783 : Nat := memoNat [3050823352785227379,8479408632915727597,3398759850500111050,5012]
def mn784 : Nat := memoNat [3050787000148446834,8477156764451773677,8010164393950657226,5012]
def mn785 : Nat := memoNat [2976513887998495345,3723679854593412333,3254644653565889226,5020]
def mn786 : Nat := memoNat [1824683169795427923,3867724678152951019,3394256242274421322,5020]
def mn787 : Nat := memoNat [2978694256065630802,3863291447336866989,3398619104421563082,5020]
def mn788 : Nat := memoNat [1859585996105599601,8335295641717738795,7861827080947452490,5020]
def mn789 : Nat := memoNat [670600545542195794,8407282869091865897,7713208293382638026,5020]
def mn790 : Nat := memoNat [3048500013847661137,8330862410901654701,7866189943094594250,5020]
def mn791 : Nat := memoNat [3049659999689789041,8405171806900753645,7721934017664731850,5020]
def mn792 : Nat := memoNat [1860675648638013010,8474907234461195435,8005801531803126346,5020]
def mn793 : Nat := memoNat [670598313233992273,8477088665463594217,8001157194691725770,5020]
def mn794 : Nat := mn457 + (memoNat [33554432,4466770247686,13194139533312])
def mn795 : Nat := mn621 + (memoNat [68222976,4688249411118039042,4398046519560,512])
def mn796 : Nat := mn793 + (memoNat [1188952569368543234,2251799813685312,281474976841728])
def mn797 : Nat := mn784 + (memoNat [34604032,72638634393600,4096,8])
def mn798 : Nat := memoNat [3085726214394660466,10713048770822638829,3110529478509140682,4996]
def mn799 : Nat := memoNat [1859550882532279859,10785106364726351081,3389752655536134602,4996]
def mn800 : Nat := mn798 + (memoNat [1089582737096672,69805794224244672,287948901309087744])
def mn801 : Nat := memoNat [3048537398315730514,10641066080947307755,3250141204253981262,5012]
def mn802 : Nat := memoNat [1859551947752326707,10713053308321434857,3101522416689166798,5012]
def mn803 : Nat := memoNat [4237451416057792050,10636632850131223661,3254504066401123022,5012]
def mn804 : Nat := memoNat [4238611401899919954,10710942246130322605,3110248140971260622,5012]
def mn805 : Nat := mn801 + (memoNat [1089652532413409,139611592743456640,143974450855673856])
def mn806 : Nat := memoNat [1859549715444123186,10782859104693163177,3389471317998254542,5012]
def mn807 : Nat := mn712 + (memoNat [71502615576641,2253998839038080,140737488617472])
def mn808 : Nat := mn590 + (memoNat [34636800,2308099209225570308,8796093026436,256])
def mn809 : Nat := mn659 + (memoNat [34635776,2380156801116012546,8796093026436,256])
def mn810 : Nat := mn712 + (memoNat [34603040,2377905001302327364,8796093026436,256])
def mn811 : Nat := memoNat [3120629078289993395,12946979463405671789,12333901519524674250,5012]
def mn812 : Nat := mn605 + (memoNat [32768,2308026570593271814,18158526891697373316,247])
def mn813 : Nat := memoNat [3083474345929656946,10569151425635452141,2966414290164861642,5020]
def mn814 : Nat := mn788 - (memoNat [18411841174482452478,66572058623])
def mn815 : Nat := mn693 + (memoNat [35651584,2454463927218466688,9223376430606327816,511])
def mn816 : Nat := mn790 - (memoNat [32244759519,66572058560])
def mn817 : Nat := mn813 + (memoNat [1088483226518527,69805796371726336,287948901309087744])
def mn818 : Nat := memoNat [740406271079466610,12874853766084595049,12180779132055669194,5020]
def mn819 : Nat := Nat.xor mn812 (memoNat [37486709473315,2747061082521664,844424930291712,8])
def mn820 : Nat := memoNat [1930481374175283826,12942478131453924587,12473372370476157514,5020]
def mn821 : Nat := memoNat [740404038771263089,12944659562456323369,12468728033364756938,5020]
def mn822 : Nat := mn594 + (memoNat [70405252514882,4507999825559684,149533581639684])
def mn823 : Nat := mn459 + (memoNat [2148533250,4400200286214,13194139533312])
def mn824 : Nat := mn811 + (memoNat [33554400,72636417703872,13979173243358023680,7])
def mn825 : Nat := mn817 + (memoNat [37452114853890,2251799813752832,281474976841728])
def mn826 : Nat := mn821 + (memoNat [1154049672256422914,2251799813685312,281474976841728])
def mn827 : Nat := mn821 + (memoNat [2380188721308796961,140737622573060,9007199258935552])
def mn828 : Nat := mn625 + (memoNat [34668544,4688176774631129090,4398046515464,504])
def mn829 : Nat := memoNat [1894453744210921074,13018891780040596841,12324894320399948234,4996]
def mn830 : Nat := mn502 + (memoNat [1065118400512,4760232169645801474,4398046507268,504])
def mn831 : Nat := mn830 - (memoNat [1152922605226820609,72638634459136,137438957572,8])
def mn832 : Nat := memoNat [4200368151887267473,8263235709137227053,7578100441736231630,5012]
def mn833 : Nat := mn808 - (2 ^ 25 + 2 ^ 80 + 2 ^ 100 + 2 ^ 185 + 2 ^ 186)
def mn834 : Nat := mn801 + (memoNat [35368469537,16212958525459009600,4467570826190782463])
def mn835 : Nat := mn802 - (memoNat [18411841176629936064,66437840895])
def mn836 : Nat := memoNat [4202548519954402930,8402847301880681709,7722074892591905486,5012]
def mn837 : Nat := mn804 - (memoNat [34392243169,66572058560])
def mn838 : Nat := mn812 - (memoNat [36062882954249249,70370958704642,4503462196805756])
def mn839 : Nat := mn811 - (memoNat [1226174268859025473,140739769991172,297237437971693820])
def mn840 : Nat := mn812 - (memoNat [17293892938921739329,4503601774788735,140600049663996])
def mn841 : Nat := memoNat [4273514263578561169,12944727661444568365,12045389805835074254,5012]
def mn842 : Nat := mn828 - (memoNat [35217658118176,4503599627305088,140600049663996])
def mn843 : Nat := mn828 - (memoNat [1190112553062138913,2322168624906306,4784937161064572])
def mn844 : Nat := mn714 + (memoNat [71501541834816,2253998836940928,140737488617472])
def mn845 : Nat := Nat.xor mn591 (memoNat [6755605700152320,72128037944037376,268447744,24])
def mn846 : Nat := mn643 + (memoNat [32768,2308024371563724800,128,248])
def mn847 : Nat := Nat.xor mn488 (memoNat [1152929201188241408,65536,864691265894088704])
def mn848 : Nat := mn836 + (memoNat [71501575421984,4503668346847296,140737488617472])
def mn849 : Nat := mn848 - (memoNat [1108345857,72638634393600,144115188075859968,8])
def mn850 : Nat := memoNat [4238648819621481075,10713121409457032429,2966414427872242382,5004]
def mn851 : Nat := Nat.xor mn798 (memoNat [1152929201188241408,0,864691265894088708])
def mn852 : Nat := mn828 + (2 ^ 40 + 2 ^ 80 + 2 ^ 130 + 2 ^ 165)
def mn853 : Nat := mn852 - (memoNat [1108345857,72638634393600,144115188075859968,8])
def mn854 : Nat := mn835 - (memoNat [1047552,16140832896918089600,9367487220635668479,7])
def mn855 : Nat := Nat.xor mn829 (memoNat [7696581394432,65536,864691265894088708])
def mn856 : Nat := mn842 + (memoNat [1190076200458912768,70368811286530,4503599635759232])
def mn857 : Nat := mn830 - (memoNat [35152159866913,2251799813685312,143974450587631616])
def mn858 : Nat := mn830 - (2 ^ 40 + 2 ^ 185)
def mn859 : Nat := Nat.xor mn831 ((memoNat [1048577,13835060254305419328]) * 2 ^ 60)
def mn860 : Nat := memoNat [3048501184227298931,13091094651347314025,12613124696681691594,5012]
def mn861 : Nat := mn814 - (memoNat [17329851368270201858,2147481599])
def mn862 : Nat := memoNat [3048536333165939282,10713196247047509227,3106025878873393738,5020]
def mn863 : Nat := mn796 - (memoNat [33554432,68719542272,12582912])
def mn864 : Nat := mn792 - (memoNat [17293857753508380672,68719542207])
def mn865 : Nat := mn862 + (memoNat [1088483226518527,69805796371726336,287948901309087744])
def mn866 : Nat := mn826 - (memoNat [2148533250,2147483648,12582912])
def mn867 : Nat := mn820 - (memoNat [17293857721263621153,2147483647])
def mn868 : Nat := Nat.xor mn842 (memoNat [2200331878403,15835647499633088,985299858386948,8])
def mn869 : Nat := mn866 + (memoNat [1089652532413409,139611592743456640,143974450855673856])
def mn870 : Nat := Nat.xor mn489 (memoNat [34603008,496068722688,4096,8])
def mn871 : Nat := mn865 + (memoNat [37452114852866,2181431069573120,281474976841728])
def mn872 : Nat := mn828 + (memoNat [33554432,2267742732288,4096,8])
def mn873 : Nat := mn753 + (memoNat [1099580865537,4757984836598104066,4398046519560,512])
def mn874 : Nat := memoNat [3048465932174838355,13088770212899300649,12612843359147993550,5004]
def mn875 : Nat := mn829 + (memoNat [1089582737096672,69805794224244672,287948901309087744])
def mn876 : Nat := memoNat [2974192820024886866,8335293303040939305,7857323618763225550,5012]
def mn877 : Nat := mn802 + (memoNat [1151795604666450944,140668768815104])
def mn878 : Nat := mn784 - (memoNat [74413812056424511,2251868667379716,8866324331757820])
def mn879 : Nat := mn806 + (memoNat [1152886320201172992,140668768813120])
def mn880 : Nat := memoNat [3046178945874052658,12942475859349181673,12468868908291930574,5012]
def mn881 : Nat := mn843 + (memoNat [1152886354593416161,140735340871680])
def mn882 : Nat := mn716 + (memoNat [71502615576641,2253998836940930,140737488617472])
def mn883 : Nat := mn878 + (memoNat [36100299668127777,4503668346847296,140737488617472])
def mn884 : Nat := mn839 + (2 ^ 10 + 2 ^ 60 + 2 ^ 111 + 2 ^ 185 + 2 ^ 186)
def mn885 : Nat := mn860 - (memoNat [35217658118176,4503599627305088,140600045469692])
def mn886 : Nat := mn885 + (memoNat [74344542790254624,134152196,8866324331626748])
def mn887 : Nat := mn886 - (memoNat [36318243487777,2251799813685312,140737488486400])
def mn888 : Nat := Nat.xor mn816 (memoNat [1101660161059,2147489856])
def mn889 : Nat := mn813 + (memoNat [2181465430229952,139611590595972992,143974450855673856])
def mn890 : Nat := mn864 - (memoNat [1116891608076255263,64])
def mn891 : Nat := mn695 + (memoNat [35651584,2454463927218466688,9223376430606327816,511])
def mn892 : Nat := mn797 - (memoNat [105553149919296,6755468160598144,393216])
def mn893 : Nat := mn889 + (memoNat [1088483226518527,69805796371726336,287948901309087744])
def mn894 : Nat := mn867 - (1151794539548113920)
def mn895 : Nat := mn872 - (memoNat [2341977393708761184,4503599694479490,4644337111793792])
def mn896 : Nat := mn827 - (memoNat [105555264898145,6755401588539584,393216])
def mn897 : Nat := mn872 + (memoNat [37082060438832063,18440129411823959874,4081387170300031])
def mn898 : Nat := mn873 - (memoNat [1152991873351089216,6685030696878272,393216])
def mn899 : Nat := mn873 - (memoNat [2343069208755109953,4503599694479490,4644337111793792])
def mn900 : Nat := mn463 + (memoNat [1099511627777,4398052802566,13194139533312])
def mn901 : Nat := mn893 + (memoNat [37452114853922,2251799813750848,281474976841728])
def mn902 : Nat := mn872 + (memoNat [37119478193947616,18442381211637645186,4362862147141759])
def mn903 : Nat := mn873 - (memoNat [1190110252033409055,2251799880794178,4362862134952064])
def mn904 : Nat := mn832 + (memoNat [1089582737096672,69805794224244672,287948901309087744])
def mn905 : Nat := Nat.xor mn837 (memoNat [1099512677411,2147489856])
def mn906 : Nat := mn784 - (memoNat [1159983727150111,70437530763266,4503462196805756])
def mn907 : Nat := mn806 - (memoNat [18410749361584635871,68585324543])
def mn908 : Nat := mn836 + (memoNat [1089582737096672,69805794224244672,287948901309087744])
def mn909 : Nat := mn810 - (memoNat [2302136025090,68719542272,422212465065984])
def mn910 : Nat := mn880 + (memoNat [38350896857415743,2181431136616514,4362862134952064])
def mn911 : Nat := mn843 - (memoNat [18445652258664251423,2147483647])
def mn912 : Nat := memoNat [4273443860473529937,12940224059669714093,12477594632574024398,5012]
def mn913 : Nat := mn842 + (memoNat [1190073933788872703,70366663802882,4081387170693248])
def mn914 : Nat := mn886 - (memoNat [37191014095553569,2322168624906306,4644199685292156])
def mn915 : Nat := mn885 - (memoNat [1152923806709319682,140737488355328,422212465065984])
def mn916 : Nat := Nat.xor mn735 (memoNat [246531122790624,448,985162419404800])
def mn917 : Nat := mn845 + (memoNat [1088451013214177,69805794224244672,431923351896588288])
def mn918 : Nat := mn491 - (1 + 2 ^ 35 + 2 ^ 40 + 2 ^ 130 + 2 ^ 175)
def mn919 : Nat := mn491 - (memoNat [2267777336322,72638634393600,281474976714756,8])
def mn920 : Nat := mn784 + (memoNat [1152922605192216577,0,137438953476])
def mn921 : Nat := mn920 - (memoNat [1133905970177,72638634393600,140737488359424,8])
def mn922 : Nat := mn850 + (memoNat [1088448865730527,69805794224244672,431923351896588288])
def mn923 : Nat := Nat.xor mn800 (memoNat [1152924879377399811,0,281612415664132])
def mn924 : Nat := mn841 + (1 + 2 ^ 40 + 2 ^ 185 + 2 ^ 186)
def mn925 : Nat := mn924 - (memoNat [1133905970177,72638634393600,140737488359424,8])
def mn926 : Nat := mn830 - (2 ^ 40 + 2 ^ 175)
def mn927 : Nat := mn830 - (memoNat [2233417597953,72638634393600,281474976714752,8])
def mn928 : Nat := mn664 + (memoNat [34635776,2380156801116012546,8796093026436,256])
def mn929 : Nat := mn873 - (memoNat [33355203584,74908524544000,140600049410044,16])
def mn930 : Nat := mn874 - (1 + 2 ^ 35 + 2 ^ 40 + 2 ^ 60 + 2 ^ 175)
def mn931 : Nat := Nat.xor mn875 (memoNat [3374770552835,65536,281612415664132])
def mn932 : Nat := mn783 + ((memoNat [33521695,18374688680840267840,4290772995]) * 2 ^ 36)
def mn933 : Nat := mn932 - (memoNat [1125935341372417,72057596185413632,144115188210073600])
def mn934 : Nat := memoNat [4128276509498165843,3723682055697108203,3250141328808041042,5028]
def mn935 : Nat := memoNat [5282287595768368722,3719248824881024173,3254504190955182802,5028]
def mn936 : Nat := memoNat [2974193885244933714,8263240246636023081,7569093379916257746,5028]
def mn937 : Nat := memoNat [5353253339392526961,8261129184444910829,7577819104198351570,5028]
def mn938 : Nat := memoNat [4164268988340750930,8330864612005352619,7861686618336746066,5028]
def mn939 : Nat := memoNat [2974191652936730193,8333046043007751401,7857042281225345490,5028]
def mn940 : Nat := mn608 + ((memoNat [1090715534754815,2249600790429696]) * 2 ^ 55)
def mn941 : Nat := mn519 + (memoNat [0,6597073963014,13194139533312])
def mn942 : Nat := Nat.xor mn629 ((memoNat [35184372088839,2199023255552,8]) * 2 ^ 55)
def mn943 : Nat := mn824 - (memoNat [109212326465373185,6989586761265514496,13019119616])
def mn944 : Nat := mn904 + (memoNat [36352637830177,2251870680645696,281474976841728])
def mn945 : Nat := Nat.xor mn832 ((memoNat [7,2199023255616,8]) * 2 ^ 55)
def mn946 : Nat := mn938 + (memoNat [36282775404576,16073346999218337920,140733059432447])
def mn947 : Nat := mn939 + (memoNat [37156964668539906,2251799813685312,281474976841728])
def mn948 : Nat := Nat.xor mn936 ((memoNat [1,68719478784,8589934720]) * 2 ^ 25)
def mn949 : Nat := mn719 + (memoNat [18409589375710002176,4327183742979,8791663841412,256])
def mn950 : Nat := mn937 + (memoNat [1125935341372417,72057596185413632,288230376285929472])
def mn951 : Nat := mn950 - (memoNat [37154732393890817,2377900674118584320,4429185024])
def mn952 : Nat := mn666 + (memoNat [1081344,74313723182841858,8791798059140,256])
def mn953 : Nat := memoNat [4200334068202228306,10569153693311206635,2961910965407013458,5028]
def mn954 : Nat := memoNat [3011348617638824499,10641140920685333737,2813292177842198994,5028]
def mn955 : Nat := memoNat [5389248085944289842,10564720462495122541,2966273827554155218,5028]
def mn956 : Nat := memoNat [5390408071786417746,10639029858494221485,2822017902124292818,5028]
def mn957 : Nat := mn953 + (memoNat [1089652532413409,139611592743456640,143974450855673856])
def mn958 : Nat := memoNat [3011346385330620978,10710946717057062057,3101241079151286738,5028]
def mn959 : Nat := mn536 + (2 ^ 55 + 2 ^ 100 + 2 ^ 160)
def mn960 : Nat := mn850 + (memoNat [69208064,217845036288000,144115188075868160,24])
def mn961 : Nat := mn798 + (memoNat [69208064,217845036222464,12288,24])
def mn962 : Nat := mn666 + (memoNat [34635776,2380156801116012546,8796093026436,256])
def mn963 : Nat := mn720 + (memoNat [34603040,2377905001302327364,8796093026436,256])
def mn964 : Nat := mn653 + (memoNat [2097152,148623048310648704,9223380824357871624,511])
def mn965 : Nat := mn668 + (memoNat [1081344,74313723182841858,8791798059140,256])
def mn966 : Nat := memoNat [4130456877565301300,3863293648440562859,3394115779663714898,5028]
def mn967 : Nat := mn947 - (memoNat [0,2048,12582912])
def mn968 : Nat := mn938 - (memoNat [18410750426702970911,2047])
def mn969 : Nat := memoNat [4201422621189459539,8405174008004449515,7717430692906883666,5028]
def mn970 : Nat := memoNat [3012438270137683508,8474909435564891305,8001298207045278162,5028]
def mn971 : Nat := mn554 + (1 * 2 ^ 105 + (2 ^ 20 - 1) * 2 ^ 150)
def mn972 : Nat := mn537 + (memoNat [0,67648,4611686018418999296])
def mn973 : Nat := mn523 + (memoNat [36028797018963936,6597006852100,13194139533312])
def mn974 : Nat := mn973 - (memoNat [36028797052518432,2305843078000279552,4299161600])
def mn975 : Nat := mn792 + (memoNat [36318209933345,16145404595403686016,140733189455871])
def mn976 : Nat := mn786 + (memoNat [0,2099264,4611686018418999296])
def mn977 : Nat := mn495 + (memoNat [33619936,4760304874785079298,4398046511364,512])
def mn978 : Nat := mn977 - (memoNat [36028797052518432,2305843078000279552,4299161600])
def mn979 : Nat := mn946 + (memoNat [35434528769,72057596185411584,130023424])
def mn980 : Nat := mn934 + (memoNat [0,2162752,4611686018418999296])
def mn981 : Nat := mn631 + (memoNat [68222944,4688249411050930178,4398046519560,512])
def mn982 : Nat := mn981 - (memoNat [36028797052518432,2305843078000279552,4299161600])
def mn983 : Nat := mn668 + (memoNat [1081344,74313723182841794,8791793864836,256])
def mn984 : Nat := mn966 + (memoNat [0,2164736,4611686018418999296])
def mn985 : Nat := mn759 + (memoNat [69238784,4758055205275172866,4398046519560,512])
def mn986 : Nat := mn985 - (memoNat [36028797052518432,2305843078000279552,4299161600])
def mn987 : Nat := mn701 + (memoNat [35651584,2454463927218466688,9223376430606327816,511])
def mn988 : Nat := mn958 + (memoNat [35993647006580769,134215680])
def mn989 : Nat := Nat.xor mn964 ((memoNat [7,6917529508677629952,918400]) * 2 ^ 25)
def mn990 : Nat := mn722 + (memoNat [71502615576641,2251799815782530,140737488617472])
def mn991 : Nat := mn964 - (memoNat [1100551815169,16140900995776380928,133139791875])
def mn992 : Nat := Nat.xor mn871 (memoNat [3466892103773290528,67108866,4503599639954304])
def mn993 : Nat := mn954 + (2 ^ 6 + 2 ^ 55 + 2 ^ 91 + 2 ^ 185 + 2 ^ 186)
def mn994 : Nat := mn991 - (memoNat [35217658118176,4503599627370560,140600049663996])
def mn995 : Nat := memoNat [5356595926684784243,8475050173118190829,3398478650401053394,5028]
def mn996 : Nat := mn995 - (memoNat [36318243487777,2251799813685312,140737488486400])
def mn997 : Nat := mn968 + (memoNat [18411841142237692959,63])
def mn998 : Nat := mn981 - (memoNat [1225085785632505889,4573968371548226,4644337111793792])
def mn999 : Nat := mn950 - (memoNat [105553116364864,6755399441057920,393216])
def mn1000 : Nat := memoNat [5355433707459662418,8400740777188365485,7721793555054025426,5028]
def mn1001 : Nat := mn985 - (memoNat [36099165763207200,6755399373947008,393216])
def mn1002 : Nat := mn970 - (memoNat [36066249133817858,2251799813685248,281474964258816])
def mn1003 : Nat := mn538 - (memoNat [35184372088864,2097216,131072])
def mn1004 : Nat := mn538 - (memoNat [36099165796728896,2308094877748953216,4295229440])
def mn1005 : Nat := mn526 + (memoNat [32,6597073961030,13194139533312])
def mn1006 : Nat := mn1005 - (memoNat [36063981424640032,2308094877746856000,4295098368])
def mn1007 : Nat := memoNat [3014687868746027602,6166882725525560493,8010305127143787210,5020]
def mn1008 : Nat := Nat.xor mn892 ((memoNat [6442458115,137438959616,29360384]) * 2 ^ 25)
def mn1009 : Nat := mn908 + (memoNat [36352636780577,2251868533162048,281474976841728])
def mn1010 : Nat := mn1009 - (memoNat [36063981424640032,2308094877746856000,4295098368])
def mn1011 : Nat := mn951 + (memoNat [1056666108756961,67553996558041024,140737622310912])
def mn1012 : Nat := Nat.xor mn999 ((memoNat [3221340161,68719478784,14680192]) * 2 ^ 26)
def mn1013 : Nat := mn1000 + (memoNat [37417755115553,2251799813685312,281474976841728])
def mn1014 : Nat := mn1013 - (memoNat [36063981424640032,2308094877746856000,4295098368])
def mn1015 : Nat := mn668 + (memoNat [1081344,72061923369156546,8791797928068,256])
def mn1016 : Nat := Nat.xor mn984 (memoNat [105553116364800,4503599694479552,25427968])
def mn1017 : Nat := mn970 + (memoNat [32,64,12582912])
def mn1018 : Nat := mn970 - ((memoNat [1100585370625,70437465751552,130692]) * 2 ^ 15)
def mn1019 : Nat := mn987 + (memoNat [1155242504933672990,2322168490754178,4362862134952064])
def mn1020 : Nat := mn958 - (memoNat [18445653358174829568,1983])
def mn1021 : Nat := mn955 + (memoNat [1088483226518527,69805796371726336,287948901309087744])
def mn1022 : Nat := mn963 - (memoNat [3367254360066,2048,422212465065984])
def mn1023 : Nat := mn957 + (memoNat [1088483226518527,69805796371726336,287948901309087744])
def mn1024 : Nat := mn991 - (memoNat [36067416291180611,4503599761588288,562812514729980])
def mn1025 : Nat := mn996 + (memoNat [36100299668127777,2310344478537285694,136343737073664])
def mn1026 : Nat := Nat.xor mn739 (memoNat [254227704184871,64,985162419404800])
def mn1027 : Nat := mn800 + (memoNat [70257696,217847183704128,12288,24])
def mn1028 : Nat := mn956 + (memoNat [32,64,432345564227567616])
def mn1029 : Nat := mn669 + (memoNat [34635776,2380156801116012546,8796093026436,256])
def mn1030 : Nat := memoNat [3048503314598186611,12946983998757049705,12324894595139459538,5028]
def mn1031 : Nat := mn818 + (memoNat [2306971108177347584,72636487041024,274873716744,8])
def mn1032 : Nat := memoNat [4236291396998875730,12870493171755551979,12473372645219850834,5028]
def mn1033 : Nat := memoNat [4236325447499631217,12872744971569237291,12185001531579914834,5028]
def mn1034 : Nat := memoNat [3047341096447855186,12942480399129679081,12468869045718309330,5028]
def mn1035 : Nat := mn611 + ((memoNat [1048577,2097150]) * 2 ^ 85)
def mn1036 : Nat := mn585 + (memoNat [1125899906843648,6597076058116,13194139533312])
def mn1037 : Nat := mn635 + ((2 ^ 36 - 1) * 2 ^ 150)
def mn1038 : Nat := mn820 + (memoNat [36282808959008,18379190077151508608,140737350205439])
def mn1039 : Nat := mn910 + (memoNat [36352604275745,2251801961168960,281474976841728])
def mn1040 : Nat := mn1039 - (memoNat [1125935341372417,72057596185413632,138412032])
def mn1041 : Nat := mn946 + ((memoNat [1,16140901133215336448,127]) * 2 ^ 25)
def mn1042 : Nat := mn934 + (memoNat [73183494045434880,6917529233799512064,12884901888])
def mn1043 : Nat := mn953 + ((2 ^ 36 - 1) * 2 ^ 150)
def mn1044 : Nat := mn1032 - (2 ^ 150)
def mn1045 : Nat := mn910 + (memoNat [1152921540109535233,145277268852736,137438961668,16])
def mn1046 : Nat := mn1033 + ((2 ^ 36 - 1) * 2 ^ 150)
def mn1047 : Nat := mn1031 - (memoNat [1197368162714688,4503599627370624,140737484423168])
def mn1048 : Nat := Nat.xor mn1034 ((memoNat [7516192775,367236883691520,656256]) * 2 ^ 40)
def mn1049 : Nat := mn685 - (memoNat [1188985485997867040,68169785933824,4499201572470656])
def mn1050 : Nat := mn829 + (memoNat [1125900009604096,77176267341824,12288,24])
def mn1051 : Nat := mn998 + (memoNat [36100299634573345,4503599627370560,140737488617472])
def mn1052 : Nat := mn1030 - (memoNat [36282808959008,18379190077151508608,140737350205439])
def mn1053 : Nat := mn1030 + ((memoNat [1125898867736575,68171868403776,3968]) * 2 ^ 41)
def mn1054 : Nat := mn1031 + ((memoNat [1125898867736575,68171868403776,3968]) * 2 ^ 41)
def mn1055 : Nat := mn1053 - (memoNat [36318243487777,2251799813685312,140737488486400])
def mn1056 : Nat := mn1054 - (memoNat [36318243487777,2251799813685312,140737488486400])
def mn1057 : Nat := mn1045 - (memoNat [1196268651086912,6755399441055936,393216])
def mn1058 : Nat := mn1034 - (memoNat [1163317661959201,2251799813685312,281474964258816])
def mn1059 : Nat := mn614 + (memoNat [18446708889337462752,2199025352641,4398046380032])
def mn1060 : Nat := mn741 + (memoNat [35218732908577,74315990927671366,13194139664384])
def mn1061 : Nat := mn1059 + (2 ^ 66 + 2 ^ 86 + 2 ^ 106 + 2 ^ 171)
def mn1062 : Nat := mn587 + (memoNat [34359738369,6597076058118,13194139533312])
def mn1063 : Nat := mn1062 - (memoNat [1161119713494049,74309395999098944,134348800])
def mn1064 : Nat := mn867 + (memoNat [36028763732968449,18372505048669222850,4503599501410431])
def mn1065 : Nat := mn1060 + (memoNat [0,2305770372726784000,132,248])
def mn1066 : Nat := mn1061 + (memoNat [0,2305770372726784000,132,248])
def mn1067 : Nat := mn880 + (memoNat [1227301267203753024,2281701380,9007199258935552])
def mn1068 : Nat := mn1067 - (memoNat [1161119713494049,74309395999098944,134348800])
def mn1069 : Nat := mn542 + (memoNat [18445582953997138943,4395901124611,8795958677636,256])
def mn1070 : Nat := mn1053 - ((memoNat [1162183790559231,0,4063104]) * 2 ^ 40)
def mn1071 : Nat := mn1069 + (2 ^ 26 + 2 ^ 56 + 2 ^ 101 + 2 ^ 126 + 2 ^ 161)
def mn1072 : Nat := mn1021 + (memoNat [37452114853922,2251799813687360,281474976841728])
def mn1073 : Nat := Nat.xor mn955 (2 ^ 15 + 2 ^ 45 + 2 ^ 115 + 2 ^ 145 + 2 ^ 186)
def mn1074 : Nat := mn1032 - (2 ^ 70 + 2 ^ 115 + 2 ^ 145)
def mn1075 : Nat := mn1074 + (memoNat [1161119713494049,74309395999098944,142737408])
def mn1076 : Nat := mn1074 + (2 ^ 151)
def mn1077 : Nat := mn1034 + (1 + 2 ^ 35 + 2 ^ 150 + 2 ^ 151)
def mn1078 : Nat := Nat.xor mn1047 (2 ^ 70 + 2 ^ 115 + 2 ^ 145 + 2 ^ 186)
def mn1079 : Nat := mn1030 + (memoNat [1188911785433858015,65372565555644226,4081387296129152])
def mn1080 : Nat := mn1052 - (memoNat [1129267161203714,0,422212465065984])
def mn1081 : Nat := Nat.xor mn743 (memoNat [253987186016480,448,985162419404800])
def mn1082 : Nat := Nat.xor mn743 (memoNat [252922034127073,448,144959613006905344])
def mn1083 : Nat := Nat.xor mn766 (memoNat [249692218720483,448,144537400541839360])
def mn1084 : Nat := mn1083 - (1 + 2 ^ 35 + 2 ^ 40 + 2 ^ 175 + 2 ^ 185)
def mn1085 : Nat := mn831 + (memoNat [34462500865,217913755697152,12288,24])
def mn1086 : Nat := mn818 + (memoNat [2381311288322066463,142004128032231364,8584987062173952])
def mn1087 : Nat := mn926 + ((memoNat [1,2251799815849984,4393751543808]) * 2 ^ 25)
def mn1088 : Nat := mn927 + (memoNat [68158464,145275121303552,18158513697557848064,15])
def mn1089 : Nat := mn543 + (memoNat [1081344,74313791900221444,8796093026436,256])
def mn1090 : Nat := mn1089 - (1 + 2 ^ 35 + 2 ^ 40 + 2 ^ 175 + 2 ^ 185)
def mn1091 : Nat := mn956 + (memoNat [1124801470006272,72057596185411584,143974450721718272])
def mn1092 : Nat := mn1091 - (1 + 2 ^ 35 + 2 ^ 40 + 2 ^ 175 + 2 ^ 185)
def mn1093 : Nat := mn1079 + (memoNat [36318243487777,4503599627370624,140737488617472])
def mn1094 : Nat := mn1093 - (1 + 2 ^ 35 + 2 ^ 40 + 2 ^ 175 + 2 ^ 185)
def mn1095 : Nat := mn1031 - (memoNat [38480757424160,18304880681152409664,422212192567295])
def mn1096 : Nat := mn1095 - (1 + 2 ^ 35 + 2 ^ 40 + 2 ^ 175 + 2 ^ 185)
def mn1097 : Nat := mn1052 + (memoNat [34085935284256,72057596185413632,288089638793379840])
def mn1098 : Nat := mn1097 - (memoNat [36318243487777,2251799813685312,140737488486400])
def mn1099 : Nat := mn745 + ((memoNat [1048577,2097150]) * 2 ^ 85)
def mn1100 : Nat := Nat.xor mn686 (memoNat [105553116364896,6770792610136192,13194169155584])
def mn1101 : Nat := mn656 + (memoNat [35184372121632,6597076058116,13194139533312])
def mn1102 : Nat := mn656 + (memoNat [0,18444498870971924420,13194135207935])
def mn1103 : Nat := mn820 + (memoNat [2216684162089952,141863390409658304,144115188339965952])
def mn1104 : Nat := mn1103 - (memoNat [35184372121632,2251799813685312,4325376])
def mn1105 : Nat := mn1104 + (memoNat [2305915579128676418,4503599627501696,274886557704])
def mn1106 : Nat := mn1103 + (memoNat [2305845210384433154,131072,274877906952])
def mn1107 : Nat := mn928 + (memoNat [34359738368,18444492273895866304,140737488224255])
def mn1108 : Nat := mn886 - (memoNat [37189845864449056,2322168624906306,4362724712775804])
def mn1109 : Nat := mn984 + (memoNat [36028797086072864,4609434356119764992,8593997824])
def mn1110 : Nat := mn1109 - (memoNat [35184372121632,2251799813685312,4325376])
def mn1111 : Nat := mn1023 + (memoNat [37452114853922,2251799813685312,281474976841728])
def mn1112 : Nat := mn1023 + (memoNat [2267742732290,0,281474972516352])
def mn1113 : Nat := mn1074 + (memoNat [1074790400,72057596185413632,130023424])
def mn1114 : Nat := mn1113 - (memoNat [35184372121632,2251799813685312,4325376])
def mn1115 : Nat := Nat.xor mn1093 ((memoNat [7516192775,15393162803200,896]) * 2 ^ 40)
def mn1116 : Nat := mn1079 + (memoNat [2233382993921,0,281474972516352])
def mn1117 : Nat := mn1097 - (memoNat [0,18444494472921219008,4398042185727])
def mn1118 : Nat := mn655 - (memoNat [1190042151031931873,68169785933760,4639939064889472])
def mn1119 : Nat := mn874 + (memoNat [35184475931680,77178414825472,12288,24])
def mn1120 : Nat := mn875 + (memoNat [35184475931680,77178414825472,12288,24])
def mn1121 : Nat := mn1097 - (memoNat [33554432,2303591278119485376,4290641920])
def mn1122 : Nat := mn793 + (memoNat [2341874007404446722,72569914982400,274877911048,8])
def mn1123 : Nat := mn1095 + (memoNat [1162218150331425,0,432486301715922944])
def mn1124 : Nat := mn1048 + (2 ^ 5 + 2 ^ 15 + 2 ^ 45 + 2 ^ 185 + 2 ^ 186)
def mn1125 : Nat := mn655 + (memoNat [1190145436405498943,72567836639298,4367260194046080])
def mn1126 : Nat := mn1125 - (memoNat [36318243487777,2251799813685312,140737488486400])
def mn1127 : Nat := mn707 + (memoNat [1133871366145,2199025352706,145135534866432])
def mn1128 : Nat := Nat.xor mn707 (memoNat [35184372121632,2253998839038018,4398046642176])
def mn1129 : Nat := mn873 + (memoNat [37190980809558049,140737555464194,4503599635759232])
def mn1130 : Nat := mn1104 + (memoNat [1190146501557421120,4573968438657154,4222124667699328])
def mn1131 : Nat := mn886 + (memoNat [1152921540040327168,65536,140874927308804])
def mn1132 : Nat := mn886 + (memoNat [1152885221796839391,18444492273895931840,137438822403])
def mn1133 : Nat := mn995 + (memoNat [35184372121600,2251799882958848,4611686018427518976])
def mn1134 : Nat := mn1133 - (memoNat [36318243487777,2251799813685312,140737488486400])
def mn1135 : Nat := mn739 + (memoNat [34603040,2377905001300230212,8796093026436,256])
def mn1136 : Nat := mn995 + (memoNat [35993612680396768,2303591278119485376,4294836224])
def mn1137 : Nat := mn827 + (memoNat [2305844143118614529,72636487041024,274877911048,8])
def mn1138 : Nat := Nat.xor mn1053 (memoNat [1133871366145,0,432486301715922944])
def mn1139 : Nat := mn743 + (memoNat [34603008,2377905001302327300,8796093026436,256])
def mn1140 : Nat := mn1053 + (memoNat [1090682249774047,69805796371728320,134086656])
def mn1141 : Nat := mn688 + (memoNat [34635776,2380156801116012546,8796093026564,256])
def mn1142 : Nat := mn1097 + (memoNat [1190039883289166815,70368811286530,4362862139015296])
def mn1143 : Nat := mn1097 + (1 + 2 ^ 35 + 2 ^ 40 + 2 ^ 150 + 2 ^ 175)
def mn1144 : Nat := Nat.xor mn1097 (memoNat [35184372121632,2251799813685312,12713984])
def mn1145 : Nat := mn1125 - (memoNat [72636486975554,4503599627370624,281474976972800])
def mn1146 : Nat := mn707 - (memoNat [71502615609409,4501400602017918,136339442106368])
def mn1147 : Nat := mn1103 + (memoNat [1190074998941811711,70368811286530,4081387174887552])
def mn1148 : Nat := mn886 - (memoNat [17293895170156200002,4503599627305087,140600049663996])
def mn1149 : Nat := mn1134 - (memoNat [36318243487777,2251799813685312,140737488486400])
def mn1150 : Nat := mn996 + (memoNat [35993612680396768,2303591278119485376,4294836224])
def mn1151 : Nat := Nat.xor mn1055 (memoNat [3401614098435,0,432767776692633600])
def mn1152 : Nat := mn1055 + (memoNat [1090682249774047,69805796371728320,134086656])
def mn1153 : Nat := mn1093 + (memoNat [1053264494658494,67553996558043008,287948901308956672])
def mn1154 : Nat := mn1097 - (memoNat [71502615609409,4503599627370624,140737484423168])
def mn1155 : Nat := mn1118 + (memoNat [2267742765058,2251799813685314,281474976841856])
def mn1156 : Nat := mn656 + (memoNat [71502615609409,2258396889743492,153931628150912])
def mn1157 : Nat := Nat.xor mn653 (memoNat [32768,2199025352718,4398050705536])
def mn1158 : Nat := mn860 + (memoNat [34603008,2269890215936,4198400,8])
def mn1159 : Nat := mn511 + (memoNat [66560,4760375174876889090,4398046511364,512])
def mn1160 : Nat := mn915 + (memoNat [38620345959459,4573968371548288,562949945294848])
def mn1161 : Nat := mn964 + (memoNat [0,2164800,4611686018431582208])
def mn1162 : Nat := mn1029 + (memoNat [37452114853922,2251799880794112,281474976841728])
def mn1163 : Nat := Nat.xor mn991 (memoNat [252202679718117409,67108864,412325249052])
def mn1164 : Nat := mn1030 + (2 ^ 150 + 2 ^ 185)
def mn1165 : Nat := mn1093 + (memoNat [37417755115553,2251799813685312,281474976841728])
def mn1166 : Nat := mn1080 + (memoNat [39685497847843,4503599627370624,562949945294848])
def mn1167 : Nat := mn1119 + (memoNat [18446708890411171808,65535,137430564868])
def mn1168 : Nat := mn743 + (memoNat [71502615576641,2251799813685376,140737488617472])
def mn1169 : Nat := mn602 + (memoNat [1163353095439394,2251801961171008,281475111059456])
def mn1170 : Nat := mn581 + (memoNat [0,2199025352706,144119586122366976])
def mn1171 : Nat := mn583 + (memoNat [0,2199025352706,144119586122366976])
def mn1172 : Nat := mn478 + (memoNat [1141932033,2380154602092756996,8796093030528,256])
def mn1173 : Nat := Nat.xor mn824 (memoNat [1074791457,2229272640,14123288431433875456])
def mn1174 : Nat := mn811 + (memoNat [1152922604118474752,65536,144115325514809348])
def mn1175 : Nat := mn812 + (memoNat [1152922604118474752,65536,144115325514809348])
def mn1176 : Nat := mn552 + (memoNat [1081344,74313791900221444,8796093026436,256])
def mn1177 : Nat := mn932 + (memoNat [32,69269568,4467570830351532032])
def mn1178 : Nat := mn932 + ((memoNat [1073741825,68719478784,4294967424]) * 2 ^ 25)
def mn1179 : Nat := mn933 + ((memoNat [1073741825,68719478784,4294967424]) * 2 ^ 25)
def mn1180 : Nat := mn1033 + (memoNat [37453189644322,74309395999098944,281475111059456])
def mn1181 : Nat := mn1031 + (2 ^ 150 + 2 ^ 185)
def mn1182 : Nat := Nat.xor mn1138 ((memoNat [3,0,131456]) * 2 ^ 41)
def mn1183 : Nat := mn1053 - (memoNat [1090750969250785,69805796371728320,134086656])
def mn1184 : Nat := mn1169 - (memoNat [1125935341372417,72057596185413632,144115188210073600])
def mn1185 : Nat := mn896 - (memoNat [984062907777920,63050396930672384,432064089384550400])
def mn1186 : Nat := mn933 + (memoNat [32,69269568,4467570830351532032])
def mn1187 : Nat := mn1180 - (memoNat [1125935341372417,72057596185413632,144115188210073600])
def mn1188 : Nat := Nat.xor mn1054 (memoNat [7799660609539,0,1009791478949478400])
def mn1189 : Nat := mn739 + (memoNat [71502615576609,2251799815782464,140737488617472])
def mn1190 : Nat := mn517 + (memoNat [32,2199090432066,4611690416473899008])
def mn1191 : Nat := mn762 + (memoNat [18374761383901298724,2251662374731839,562941363748864])
def mn1192 : Nat := mn477 + (memoNat [35684352,2380154602090725380,8796093030528,256])
def mn1193 : Nat := mn548 + (memoNat [34635776,74311661596442628,8796093026436,256])
def mn1194 : Nat := mn783 + (memoNat [1116893808139698177,16140900995776315392,133143986179])
def mn1195 : Nat := mn932 - (memoNat [34902861711145983,2233785481747761152,4160749568])
def mn1196 : Nat := mn964 - (memoNat [36028797052518432,2305843078000279552,4290772992])
def mn1197 : Nat := mn1136 - ((memoNat [1098437886975,70300026798080,131068]) * 2 ^ 16)
def mn1198 : Nat := mn735 + (memoNat [71502650179649,2253998836940928,140737488621568])
def mn1199 : Nat := mn456 + (memoNat [64512,4760234366521573378,4398046511360,504])
def mn1200 : Nat := mn769 + (memoNat [36352637796385,64,281474976845828])
def mn1201 : Nat := mn457 + (memoNat [33617920,2454323254163144712,17592186044676,496])
def mn1202 : Nat := mn1173 - ((memoNat [1,2251799815849984,4393751543808]) * 2 ^ 26)
def mn1203 : Nat := mn461 + (memoNat [64512,4760236494684160006,17592186044676,496])
def mn1204 : Nat := mn463 + (memoNat [30720,4757914326126297096,17592186044676,496])
def mn1205 : Nat := mn1199 - (memoNat [63488,4760163926908338176,256,496])
def mn1206 : Nat := mn514 + (memoNat [71502580973633,2249600786235516,131941395591164])
def mn1207 : Nat := mn518 + (memoNat [32,2199090432066,4611690416473899008])
def mn1208 : Nat := mn762 + (memoNat [74904229675044,2247401767174204,554153860661248])
def mn1209 : Nat := mn582 + (memoNat [0,2199025352706,144119586122366976])
def mn1210 : Nat := mn766 + (memoNat [74869869936707,2247401762979964,554153860661248])
def mn1211 : Nat := mn781 + (memoNat [38585986220067,18446741874684198974,417814418686079])
def mn1212 : Nat := mn1157 - ((memoNat [1048577,2097150]) * 2 ^ 86)
def mn1213 : Nat := mn582 + (memoNat [2180368065103809,2203320323970,288094036978040832])
def mn1214 : Nat := mn707 - (memoNat [18446708889337495520,2253998839037889,4398046380032])
def mn1215 : Nat := mn486 + (memoNat [71502580973633,2251799811588222,136339442102268])
def mn1216 : Nat := mn1189 - (memoNat [69271552,4760309204181319684,8796093030664,512])
def mn1217 : Nat := mn1210 - (memoNat [34635776,2380154602090659842,4398046515332,256])
def mn1218 : Nat := mn654 - (memoNat [32768,2199025352706,4398042316928])
def mn1219 : Nat := mn1125 - (memoNat [69271552,4760309204181319684,8796093030664,512])
def mw2 : WireKey := (mn6,mn7,mn8,mn9,3)
def mw3 : WireKey := (mn10,mn11,mn12,mn13,3)
def mw4 : WireKey := (mn14,mn15,mn16,mn17,3)
def mw5 : WireKey := (mn18,mn19,mn20,mn21,3)
def mw6 : WireKey := (mn22,mn23,mn24,mn25,3)
def mw7 : WireKey := (mn26,mn27,mn28,mn29,3)
def memoOp (d : Bool) (x y : WireKey) : WireKey :=
  let (s,a,b,c,r) := x
  let (ss,aa,bb,cc,rr) := y
  let w := opW d ⟨s,a,b,c,r⟩ ⟨ss,aa,bb,cc,rr⟩
  (w.s,w.a,w.b,w.c,w.r)
def memoNot (x : WireKey) : WireKey :=
  let (s,a,b,c,r) := x
  (s ^^^ mz 0,b,a,c,0)
def mw227 : WireKey := memoNot mw2
def mw215 : WireKey := memoNot mw3
def mw205 : WireKey := memoNot mw4
def mw193 : WireKey := memoNot mw5
def mw248 : WireKey := memoNot mw6
def mw237 : WireKey := memoNot mw7
def mw16 : WireKey := memoOp false mw2 mw3
def mw17 : WireKey := memoOp true mw2 mw3
def mw18 : WireKey := memoOp false mw2 mw4
def mw19 : WireKey := memoOp true mw2 mw4
def mw20 : WireKey := memoOp false mw2 mw5
def mw21 : WireKey := memoOp true mw2 mw5
def mw8 : WireKey := memoOp false mw2 mw6
def mw9 : WireKey := memoOp true mw2 mw6
def mw45 : WireKey := memoOp false mw2 mw7
def mw32 : WireKey := memoOp true mw2 mw7
def mw22 : WireKey := memoOp false mw3 mw4
def mw23 : WireKey := memoOp true mw3 mw4
def mw24 : WireKey := memoOp false mw3 mw5
def mw25 : WireKey := memoOp true mw3 mw5
def mw10 : WireKey := memoOp false mw3 mw6
def mw11 : WireKey := memoOp true mw3 mw6
def mw46 : WireKey := memoOp false mw3 mw7
def mw33 : WireKey := memoOp true mw3 mw7
def mw26 : WireKey := memoOp false mw4 mw5
def mw27 : WireKey := memoOp true mw4 mw5
def mw12 : WireKey := memoOp false mw4 mw6
def mw13 : WireKey := memoOp true mw4 mw6
def mw34 : WireKey := memoOp false mw4 mw7
def mw35 : WireKey := memoOp true mw4 mw7
def mw14 : WireKey := memoOp false mw5 mw6
def mw15 : WireKey := memoOp true mw5 mw6
def mw47 : WireKey := memoOp false mw5 mw7
def mw36 : WireKey := memoOp true mw5 mw7
def mw1 : WireKey := memoOp false mw6 mw7
def mw0 : WireKey := memoOp true mw6 mw7
def mw103 : WireKey := memoOp false mw0 mw11
def mw40 : WireKey := memoOp true mw0 mw11
def mw114 : WireKey := memoOp false mw0 mw13
def mw42 : WireKey := memoOp true mw0 mw13
def mw122 : WireKey := memoOp false mw0 mw15
def mw44 : WireKey := memoOp true mw0 mw15
def mw37 : WireKey := memoOp false mw0 mw2
def mw38 : WireKey := memoOp true mw0 mw2
def mw39 : WireKey := memoOp false mw0 mw3
def mw49 : WireKey := memoOp false mw0 mw32
def mw61 : WireKey := memoOp false mw0 mw33
def mw75 : WireKey := memoOp false mw0 mw35
def mw85 : WireKey := memoOp false mw0 mw36
def mw41 : WireKey := memoOp false mw0 mw4
def mw43 : WireKey := memoOp false mw0 mw5
def mw95 : WireKey := memoOp false mw0 mw9
def mw60 : WireKey := memoOp false mw1 mw10
def mw107 : WireKey := memoOp true mw1 mw10
def mw74 : WireKey := memoOp false mw1 mw12
def mw118 : WireKey := memoOp true mw1 mw12
def mw84 : WireKey := memoOp false mw1 mw14
def mw126 : WireKey := memoOp true mw1 mw14
def mw48 : WireKey := memoOp false mw1 mw2
def mw28 : WireKey := memoOp true mw1 mw2
def mw29 : WireKey := memoOp true mw1 mw3
def mw80 : WireKey := memoOp true mw1 mw34
def mw30 : WireKey := memoOp true mw1 mw4
def mw56 : WireKey := memoOp true mw1 mw45
def mw67 : WireKey := memoOp true mw1 mw46
def mw89 : WireKey := memoOp true mw1 mw47
def mw31 : WireKey := memoOp true mw1 mw5
def mw99 : WireKey := memoOp true mw1 mw8
def mw63 : WireKey := memoOp false mw10 mw12
def mw168 : WireKey := memoOp true mw10 mw12
def mw65 : WireKey := memoOp false mw10 mw14
def mw177 : WireKey := memoOp true mw10 mw14
def mw50 : WireKey := memoOp false mw10 mw16
def mw57 : WireKey := memoOp true mw10 mw16
def mw62 : WireKey := memoOp true mw10 mw2
def mw82 : WireKey := memoOp true mw10 mw22
def mw92 : WireKey := memoOp true mw10 mw24
def mw64 : WireKey := memoOp true mw10 mw4
def mw66 : WireKey := memoOp true mw10 mw5
def mw139 : WireKey := memoOp true mw10 mw8
def mw162 : WireKey := memoOp false mw11 mw13
def mw71 : WireKey := memoOp true mw11 mw13
def mw172 : WireKey := memoOp false mw11 mw15
def mw73 : WireKey := memoOp true mw11 mw15
def mw51 : WireKey := memoOp false mw11 mw17
def mw69 : WireKey := memoOp true mw11 mw17
def mw68 : WireKey := memoOp false mw11 mw2
def mw77 : WireKey := memoOp false mw11 mw23
def mw87 : WireKey := memoOp false mw11 mw25
def mw70 : WireKey := memoOp false mw11 mw4
def mw72 : WireKey := memoOp false mw11 mw5
def mw132 : WireKey := memoOp false mw11 mw9
def mw78 : WireKey := memoOp false mw12 mw14
def mw188 : WireKey := memoOp true mw12 mw14
def mw52 : WireKey := memoOp false mw12 mw18
def mw58 : WireKey := memoOp true mw12 mw18
def mw76 : WireKey := memoOp true mw12 mw2
def mw93 : WireKey := memoOp true mw12 mw26
def mw79 : WireKey := memoOp true mw12 mw5
def mw149 : WireKey := memoOp true mw12 mw8
def mw183 : WireKey := memoOp false mw13 mw15
def mw94 : WireKey := memoOp true mw13 mw15
def mw53 : WireKey := memoOp false mw13 mw19
def mw81 : WireKey := memoOp false mw13 mw2
def mw88 : WireKey := memoOp false mw13 mw27
def mw83 : WireKey := memoOp false mw13 mw5
def mw143 : WireKey := memoOp false mw13 mw9
def mw54 : WireKey := memoOp false mw14 mw2
def mw86 : WireKey := memoOp true mw14 mw2
def mw59 : WireKey := memoOp true mw14 mw20
def mw158 : WireKey := memoOp true mw14 mw8
def mw90 : WireKey := memoOp false mw15 mw2
def mw91 : WireKey := memoOp true mw15 mw2
def mw55 : WireKey := memoOp false mw15 mw21
def mw153 : WireKey := memoOp false mw15 mw9
def mw135 : WireKey := memoOp false mw16 mw18
def mw170 : WireKey := memoOp true mw16 mw18
def mw137 : WireKey := memoOp false mw16 mw20
def mw179 : WireKey := memoOp true mw16 mw20
def mw151 : WireKey := memoOp true mw16 mw22
def mw160 : WireKey := memoOp true mw16 mw24
def mw136 : WireKey := memoOp true mw16 mw4
def mw133 : WireKey := memoOp false mw16 mw45
def mw108 : WireKey := memoOp true mw16 mw45
def mw100 : WireKey := memoOp true mw16 mw46
def mw138 : WireKey := memoOp true mw16 mw5
def mw134 : WireKey := memoOp true mw16 mw7
def mw165 : WireKey := memoOp false mw17 mw19
def mw175 : WireKey := memoOp false mw17 mw21
def mw180 : WireKey := memoOp true mw17 mw21
def mw146 : WireKey := memoOp false mw17 mw23
def mw156 : WireKey := memoOp false mw17 mw25
def mw104 : WireKey := memoOp false mw17 mw32
def mw109 : WireKey := memoOp true mw17 mw32
def mw96 : WireKey := memoOp false mw17 mw33
def mw141 : WireKey := memoOp false mw17 mw4
def mw142 : WireKey := memoOp false mw17 mw5
def mw140 : WireKey := memoOp false mw17 mw7
def mw147 : WireKey := memoOp false mw18 mw20
def mw190 : WireKey := memoOp true mw18 mw20
def mw161 : WireKey := memoOp true mw18 mw26
def mw144 : WireKey := memoOp false mw18 mw34
def mw101 : WireKey := memoOp true mw18 mw34
def mw119 : WireKey := memoOp true mw18 mw45
def mw148 : WireKey := memoOp true mw18 mw5
def mw145 : WireKey := memoOp true mw18 mw7
def mw186 : WireKey := memoOp false mw19 mw21
def mw157 : WireKey := memoOp false mw19 mw27
def mw115 : WireKey := memoOp false mw19 mw32
def mw97 : WireKey := memoOp false mw19 mw35
def mw152 : WireKey := memoOp false mw19 mw5
def mw150 : WireKey := memoOp false mw19 mw7
def mw197 : WireKey := memoOp false mw193 mw2
def mw198 : WireKey := memoOp true mw193 mw2
def mw199 : WireKey := memoOp false mw193 mw3
def mw200 : WireKey := memoOp true mw193 mw3
def mw201 : WireKey := memoOp false mw193 mw4
def mw202 : WireKey := memoOp true mw193 mw4
def mw192 : WireKey := memoOp false mw193 mw6
def mw194 : WireKey := memoOp true mw193 mw6
def mw195 : WireKey := memoOp false mw193 mw7
def mw196 : WireKey := memoOp true mw193 mw7
def mw208 : WireKey := memoOp false mw2 mw205
def mw209 : WireKey := memoOp true mw2 mw205
def mw219 : WireKey := memoOp false mw2 mw215
def mw220 : WireKey := memoOp true mw2 mw215
def mw239 : WireKey := memoOp false mw2 mw237
def mw240 : WireKey := memoOp true mw2 mw237
def mw250 : WireKey := memoOp false mw2 mw248
def mw251 : WireKey := memoOp true mw2 mw248
def mw127 : WireKey := memoOp false mw2 mw36
def mw128 : WireKey := memoOp true mw2 mw36
def mw154 : WireKey := memoOp false mw2 mw47
def mw123 : WireKey := memoOp true mw2 mw47
def mw102 : WireKey := memoOp true mw20 mw47
def mw155 : WireKey := memoOp true mw20 mw7
def mw210 : WireKey := memoOp false mw205 mw3
def mw211 : WireKey := memoOp true mw205 mw3
def mw212 : WireKey := memoOp false mw205 mw5
def mw213 : WireKey := memoOp true mw205 mw5
def mw203 : WireKey := memoOp false mw205 mw6
def mw204 : WireKey := memoOp true mw205 mw6
def mw206 : WireKey := memoOp false mw205 mw7
def mw207 : WireKey := memoOp true mw205 mw7
def mw98 : WireKey := memoOp false mw21 mw36
def mw159 : WireKey := memoOp false mw21 mw7
def mw221 : WireKey := memoOp false mw215 mw4
def mw222 : WireKey := memoOp true mw215 mw4
def mw223 : WireKey := memoOp false mw215 mw5
def mw224 : WireKey := memoOp true mw215 mw5
def mw214 : WireKey := memoOp false mw215 mw6
def mw216 : WireKey := memoOp true mw215 mw6
def mw217 : WireKey := memoOp false mw215 mw7
def mw218 : WireKey := memoOp true mw215 mw7
def mw166 : WireKey := memoOp false mw22 mw24
def mw191 : WireKey := memoOp true mw22 mw24
def mw181 : WireKey := memoOp true mw22 mw26
def mw163 : WireKey := memoOp false mw22 mw34
def mw110 : WireKey := memoOp true mw22 mw34
def mw120 : WireKey := memoOp true mw22 mw46
def mw167 : WireKey := memoOp true mw22 mw5
def mw164 : WireKey := memoOp true mw22 mw7
def mw230 : WireKey := memoOp false mw227 mw3
def mw231 : WireKey := memoOp true mw227 mw3
def mw232 : WireKey := memoOp false mw227 mw4
def mw233 : WireKey := memoOp true mw227 mw4
def mw234 : WireKey := memoOp false mw227 mw5
def mw235 : WireKey := memoOp true mw227 mw5
def mw225 : WireKey := memoOp false mw227 mw6
def mw226 : WireKey := memoOp true mw227 mw6
def mw228 : WireKey := memoOp false mw227 mw7
def mw229 : WireKey := memoOp true mw227 mw7
def mw187 : WireKey := memoOp false mw23 mw25
def mw182 : WireKey := memoOp true mw23 mw25
def mw176 : WireKey := memoOp false mw23 mw27
def mw116 : WireKey := memoOp false mw23 mw33
def mw111 : WireKey := memoOp true mw23 mw33
def mw105 : WireKey := memoOp false mw23 mw35
def mw171 : WireKey := memoOp false mw23 mw5
def mw169 : WireKey := memoOp false mw23 mw7
def mw241 : WireKey := memoOp false mw237 mw3
def mw242 : WireKey := memoOp true mw237 mw3
def mw243 : WireKey := memoOp false mw237 mw4
def mw244 : WireKey := memoOp true mw237 mw4
def mw245 : WireKey := memoOp false mw237 mw5
def mw246 : WireKey := memoOp true mw237 mw5
def mw236 : WireKey := memoOp false mw237 mw6
def mw238 : WireKey := memoOp true mw237 mw6
def mw173 : WireKey := memoOp false mw24 mw46
def mw129 : WireKey := memoOp true mw24 mw46
def mw112 : WireKey := memoOp true mw24 mw47
def mw174 : WireKey := memoOp true mw24 mw7
def mw252 : WireKey := memoOp false mw248 mw3
def mw253 : WireKey := memoOp true mw248 mw3
def mw254 : WireKey := memoOp false mw248 mw4
def mw255 : WireKey := memoOp true mw248 mw4
def mw256 : WireKey := memoOp false mw248 mw5
def mw257 : WireKey := memoOp true mw248 mw5
def mw247 : WireKey := memoOp false mw248 mw7
def mw249 : WireKey := memoOp true mw248 mw7
def mw124 : WireKey := memoOp false mw25 mw33
def mw113 : WireKey := memoOp true mw25 mw33
def mw106 : WireKey := memoOp false mw25 mw36
def mw178 : WireKey := memoOp false mw25 mw7
def mw184 : WireKey := memoOp false mw26 mw34
def mw130 : WireKey := memoOp true mw26 mw34
def mw121 : WireKey := memoOp true mw26 mw47
def mw185 : WireKey := memoOp true mw26 mw7
def mw125 : WireKey := memoOp false mw27 mw35
def mw131 : WireKey := memoOp true mw27 mw35
def mw117 : WireKey := memoOp false mw27 mw36
def mw189 : WireKey := memoOp false mw27 mw7
def originalC : Nat → Runner := lookC I.NN I.AA I.HX I.HY (lz 0) (mz 0) (pL (rt.map (fun _ => 16)))
def originalS : Nat → Runner := look1C I.NN I.AA I.HX I.HY (lz 0) (mz 0) (pL (rt.map (fun _ => 16))) 12
def mcC0 : List MemoKey := [(12,10,1,mn477,[mw6,mw28,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn478,[mw6,mw29,mw7,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC0p : mcC0.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC1 : List MemoKey := [(12,10,1,mn479,[mw6,mw30,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn480,[mw6,mw31,mw7,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC1p : mcC1.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC2 : List MemoKey := [(12,10,1,mn505,[mw6,mw7,mw2,mw37,mw3,mw4,mw5]),(12,10,1,mn506,[mw0,mw6,mw7,mw2,mw37,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC2p : mcC2.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC3 : List MemoKey := [(12,10,1,mn507,[mw38,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn508,[mw6,mw7,mw2,mw3,mw39,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC3p : mcC3.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC4 : List MemoKey := [(12,10,1,mn509,[mw0,mw6,mw7,mw2,mw3,mw39,mw4,mw5]),(12,10,1,mn510,[mw40,mw6,mw7,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC4p : mcC4.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC5 : List MemoKey := [(12,10,1,mn511,[mw6,mw7,mw2,mw3,mw4,mw41,mw5]),(12,10,1,mn512,[mw0,mw6,mw7,mw2,mw3,mw4,mw41,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC5p : mcC5.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC6 : List MemoKey := [(12,10,1,mn513,[mw42,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn514,[mw6,mw7,mw2,mw3,mw4,mw5,mw43])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC6p : mcC6.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC7 : List MemoKey := [(12,10,1,mn515,[mw0,mw6,mw7,mw2,mw3,mw4,mw5,mw43]),(12,10,1,mn516,[mw44,mw6,mw7,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC7p : mcC7.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC8 : List MemoKey := [(12,10,1,mn546,[mw6,mw7,mw2,mw48,mw3,mw4,mw5]),(12,10,1,mn547,[mw6,mw7,mw2,mw8,mw48,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC8p : mcC8.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC9 : List MemoKey := [(12,10,1,mn548,[mw6,mw49,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn549,[mw6,mw49,mw7,mw2,mw8,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC9p : mcC9.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC10 : List MemoKey := [(12,10,1,mn550,[mw6,mw7,mw2,mw3,mw50,mw4,mw5]),(12,10,1,mn551,[mw6,mw7,mw2,mw8,mw3,mw50,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC10p : mcC10.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC11 : List MemoKey := [(12,10,1,mn552,[mw6,mw7,mw51,mw2,mw3,mw4,mw5]),(12,10,1,mn553,[mw6,mw7,mw51,mw2,mw8,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC11p : mcC11.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC12 : List MemoKey := [(12,10,1,mn554,[mw6,mw7,mw2,mw3,mw4,mw5,mw52]),(12,10,1,mn555,[mw6,mw7,mw2,mw8,mw3,mw4,mw5,mw52])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC12p : mcC12.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC13 : List MemoKey := [(12,10,1,mn556,[mw6,mw7,mw53,mw2,mw3,mw4,mw5]),(12,10,1,mn557,[mw6,mw7,mw53,mw2,mw8,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC13p : mcC13.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC14 : List MemoKey := [(12,10,1,mn558,[mw6,mw7,mw2,mw3,mw4,mw5,mw54]),(12,10,1,mn559,[mw6,mw7,mw2,mw8,mw3,mw4,mw5,mw54])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC14p : mcC14.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC15 : List MemoKey := [(12,10,1,mn560,[mw6,mw7,mw55,mw2,mw3,mw4,mw5]),(12,10,1,mn561,[mw6,mw7,mw55,mw2,mw8,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC15p : mcC15.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC16 : List MemoKey := [(12,10,1,mn577,[mw6,mw7,mw56,mw2,mw3,mw4,mw5]),(12,10,1,mn578,[mw6,mw7,mw2,mw3,mw57,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC16p : mcC16.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC17 : List MemoKey := [(12,10,1,mn579,[mw6,mw7,mw2,mw3,mw4,mw58,mw5]),(12,10,1,mn580,[mw6,mw7,mw2,mw3,mw4,mw5,mw59])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC17p : mcC17.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC18 : List MemoKey := [(12,10,1,mn605,[mw6,mw7,mw2,mw3,mw60,mw4,mw5]),(12,10,1,mn606,[mw6,mw61,mw7,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC18p : mcC18.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC19 : List MemoKey := [(12,10,1,mn607,[mw6,mw61,mw7,mw2,mw3,mw10,mw4,mw5]),(12,10,1,mn608,[mw6,mw7,mw2,mw3,mw50,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC19p : mcC19.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC20 : List MemoKey := [(12,10,1,mn609,[mw6,mw7,mw62,mw2,mw3,mw4,mw5]),(12,10,1,mn610,[mw6,mw7,mw62,mw2,mw3,mw10,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC20p : mcC20.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC21 : List MemoKey := [(12,10,1,mn611,[mw6,mw7,mw2,mw3,mw4,mw5,mw63]),(12,10,1,mn612,[mw6,mw7,mw2,mw64,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC21p : mcC21.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC22 : List MemoKey := [(12,10,1,mn613,[mw6,mw7,mw2,mw64,mw3,mw10,mw4,mw5]),(12,10,1,mn614,[mw6,mw7,mw2,mw3,mw4,mw5,mw65])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC22p : mcC22.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC23 : List MemoKey := [(12,10,1,mn615,[mw6,mw7,mw2,mw66,mw3,mw4,mw5]),(12,10,1,mn616,[mw6,mw7,mw2,mw66,mw3,mw10,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC23p : mcC23.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC24 : List MemoKey := [(12,10,1,mn641,[mw6,mw7,mw67,mw2,mw3,mw4,mw5]),(12,10,1,mn642,[mw11,mw6,mw7,mw67,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC24p : mcC24.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC25 : List MemoKey := [(12,10,1,mn643,[mw40,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn644,[mw6,mw7,mw2,mw68,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC25p : mcC25.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC26 : List MemoKey := [(12,10,1,mn645,[mw11,mw6,mw7,mw2,mw68,mw3,mw4,mw5]),(12,10,1,mn646,[mw69,mw6,mw7,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC26p : mcC26.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC27 : List MemoKey := [(12,10,1,mn647,[mw6,mw7,mw2,mw3,mw4,mw70,mw5]),(12,10,1,mn648,[mw11,mw6,mw7,mw2,mw3,mw4,mw70,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC27p : mcC27.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC28 : List MemoKey := [(12,10,1,mn649,[mw71,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn650,[mw6,mw7,mw2,mw3,mw4,mw5,mw72])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC28p : mcC28.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC29 : List MemoKey := [(12,10,1,mn651,[mw11,mw6,mw7,mw2,mw3,mw4,mw5,mw72]),(12,10,1,mn652,[mw73,mw6,mw7,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC29p : mcC29.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC30 : List MemoKey := [(12,10,1,mn674,[mw6,mw7,mw2,mw3,mw4,mw74,mw5]),(12,10,1,mn675,[mw6,mw7,mw2,mw3,mw4,mw12,mw74,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC30p : mcC30.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC31 : List MemoKey := [(12,10,1,mn676,[mw6,mw75,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn677,[mw6,mw75,mw7,mw2,mw3,mw4,mw12,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC31p : mcC31.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC32 : List MemoKey := [(12,10,1,mn678,[mw6,mw7,mw2,mw3,mw4,mw5,mw52]),(12,10,1,mn679,[mw6,mw7,mw2,mw3,mw4,mw12,mw5,mw52])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC32p : mcC32.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC33 : List MemoKey := [(12,10,1,mn680,[mw6,mw7,mw76,mw2,mw3,mw4,mw5]),(12,10,1,mn681,[mw6,mw7,mw76,mw2,mw3,mw4,mw12,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC33p : mcC33.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC34 : List MemoKey := [(12,10,1,mn682,[mw6,mw7,mw2,mw3,mw4,mw5,mw63]),(12,10,1,mn683,[mw6,mw7,mw2,mw3,mw4,mw12,mw5,mw63])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC34p : mcC34.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC35 : List MemoKey := [(12,10,1,mn684,[mw6,mw7,mw2,mw77,mw3,mw4,mw5]),(12,10,1,mn685,[mw6,mw7,mw2,mw77,mw3,mw4,mw12,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC35p : mcC35.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC36 : List MemoKey := [(12,10,1,mn686,[mw6,mw7,mw2,mw3,mw4,mw5,mw78]),(12,10,1,mn687,[mw6,mw7,mw2,mw3,mw4,mw12,mw5,mw78])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC36p : mcC36.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC37 : List MemoKey := [(12,10,1,mn688,[mw6,mw7,mw2,mw3,mw79,mw4,mw5]),(12,10,1,mn689,[mw6,mw7,mw2,mw3,mw79,mw4,mw12,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC37p : mcC37.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC38 : List MemoKey := [(12,10,1,mn703,[mw6,mw7,mw80,mw2,mw3,mw4,mw5]),(12,10,1,mn704,[mw6,mw7,mw2,mw81,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC38p : mcC38.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC39 : List MemoKey := [(12,10,1,mn705,[mw6,mw7,mw2,mw3,mw82,mw4,mw5]),(12,10,1,mn706,[mw6,mw7,mw2,mw3,mw4,mw5,mw83])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC39p : mcC39.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC40 : List MemoKey := [(12,10,1,mn731,[mw6,mw7,mw2,mw3,mw4,mw5,mw84]),(12,10,1,mn732,[mw6,mw7,mw2,mw3,mw4,mw5,mw14,mw84])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC40p : mcC40.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC41 : List MemoKey := [(12,10,1,mn733,[mw6,mw85,mw2,mw3,mw4,mw5]),(12,10,1,mn734,[mw6,mw85,mw2,mw3,mw4,mw5,mw14])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC41p : mcC41.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC42 : List MemoKey := [(12,10,1,mn735,[mw6,mw85,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn736,[mw6,mw85,mw7,mw2,mw3,mw4,mw5,mw14])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC42p : mcC42.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC43 : List MemoKey := [(12,10,1,mn737,[mw6,mw7,mw2,mw3,mw4,mw5,mw54]),(12,10,1,mn738,[mw6,mw7,mw2,mw3,mw4,mw5,mw14,mw54])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC43p : mcC43.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC44 : List MemoKey := [(12,10,1,mn739,[mw6,mw7,mw86,mw2,mw3,mw4,mw5]),(12,10,1,mn740,[mw6,mw7,mw86,mw2,mw3,mw4,mw5,mw14])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC44p : mcC44.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC45 : List MemoKey := [(12,10,1,mn741,[mw6,mw7,mw2,mw3,mw4,mw5,mw65]),(12,10,1,mn742,[mw6,mw7,mw2,mw3,mw4,mw5,mw14,mw65])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC45p : mcC45.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC46 : List MemoKey := [(12,10,1,mn743,[mw6,mw7,mw2,mw87,mw3,mw4,mw5]),(12,10,1,mn744,[mw6,mw7,mw2,mw87,mw3,mw4,mw5,mw14])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC46p : mcC46.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC47 : List MemoKey := [(12,10,1,mn745,[mw6,mw7,mw2,mw3,mw4,mw5,mw78]),(12,10,1,mn746,[mw6,mw7,mw2,mw3,mw4,mw5,mw14,mw78])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC47p : mcC47.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC48 : List MemoKey := [(12,10,1,mn747,[mw6,mw7,mw2,mw3,mw88,mw4,mw5]),(12,10,1,mn748,[mw6,mw7,mw2,mw3,mw88,mw4,mw5,mw14])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC48p : mcC48.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC49 : List MemoKey := [(12,10,1,mn769,[mw6,mw7,mw89,mw2,mw3,mw4,mw5]),(12,10,1,mn770,[mw15,mw6,mw7,mw89,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC49p : mcC49.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC50 : List MemoKey := [(12,10,1,mn771,[mw44,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn772,[mw6,mw7,mw90,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC50p : mcC50.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC51 : List MemoKey := [(12,10,1,mn773,[mw15,mw6,mw7,mw90,mw3,mw4,mw5]),(12,10,1,mn774,[mw6,mw7,mw2,mw90,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC51p : mcC51.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC52 : List MemoKey := [(12,10,1,mn775,[mw15,mw6,mw7,mw2,mw90,mw3,mw4,mw5]),(12,10,1,mn776,[mw91,mw6,mw7,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC52p : mcC52.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC53 : List MemoKey := [(12,10,1,mn777,[mw6,mw7,mw2,mw3,mw92,mw4,mw5]),(12,10,1,mn778,[mw15,mw6,mw7,mw2,mw3,mw92,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC53p : mcC53.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC54 : List MemoKey := [(12,10,1,mn779,[mw73,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn780,[mw6,mw7,mw2,mw3,mw4,mw93,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC54p : mcC54.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC55 : List MemoKey := [(12,10,1,mn781,[mw15,mw6,mw7,mw2,mw3,mw4,mw93,mw5]),(12,10,1,mn782,[mw94,mw6,mw7,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC55p : mcC55.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC56 : List MemoKey := [(12,10,1,mn794,[mw95,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn795,[mw6,mw7,mw96,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC56p : mcC56.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC57 : List MemoKey := [(12,10,1,mn796,[mw6,mw7,mw97,mw2,mw3,mw4,mw5]),(12,10,1,mn797,[mw6,mw7,mw98,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC57p : mcC57.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC58 : List MemoKey := [(12,10,1,mn807,[mw6,mw99,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn808,[mw6,mw7,mw2,mw3,mw100,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC58p : mcC58.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC59 : List MemoKey := [(12,10,1,mn809,[mw6,mw7,mw2,mw3,mw4,mw101,mw5]),(12,10,1,mn810,[mw6,mw7,mw2,mw3,mw4,mw5,mw102])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC59p : mcC59.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC60 : List MemoKey := [(12,10,1,mn822,[mw103,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn823,[mw103,mw6,mw7,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC60p : mcC60.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC61 : List MemoKey := [(12,10,1,mn824,[mw6,mw7,mw104,mw3,mw4,mw5]),(12,10,1,mn825,[mw6,mw7,mw104,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC61p : mcC61.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC62 : List MemoKey := [(12,10,1,mn826,[mw6,mw7,mw2,mw105,mw3,mw4,mw5]),(12,10,1,mn827,[mw6,mw7,mw2,mw106,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC62p : mcC62.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC63 : List MemoKey := [(12,10,1,mn844,[mw6,mw107,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn845,[mw6,mw33,mw107,mw7,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC63p : mcC63.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC64 : List MemoKey := [(12,10,1,mn846,[mw40,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn847,[mw40,mw6,mw33,mw7,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC64p : mcC64.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC65 : List MemoKey := [(12,10,1,mn848,[mw6,mw7,mw2,mw108,mw3,mw4,mw5]),(12,10,1,mn849,[mw6,mw33,mw7,mw2,mw108,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC65p : mcC65.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC66 : List MemoKey := [(12,10,1,mn850,[mw6,mw109,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn851,[mw6,mw109,mw33,mw7,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC66p : mcC66.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC67 : List MemoKey := [(12,10,1,mn852,[mw6,mw7,mw2,mw3,mw4,mw110,mw5]),(12,10,1,mn853,[mw6,mw33,mw7,mw2,mw3,mw4,mw110,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC67p : mcC67.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC68 : List MemoKey := [(12,10,1,mn854,[mw6,mw111,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn855,[mw6,mw111,mw33,mw7,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC68p : mcC68.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC69 : List MemoKey := [(12,10,1,mn856,[mw6,mw7,mw2,mw3,mw4,mw5,mw112]),(12,10,1,mn857,[mw6,mw33,mw7,mw2,mw3,mw4,mw5,mw112])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC69p : mcC69.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC70 : List MemoKey := [(12,10,1,mn858,[mw6,mw113,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn859,[mw6,mw113,mw33,mw7,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC70p : mcC70.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC71 : List MemoKey := [(12,10,1,mn870,[mw114,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn871,[mw6,mw7,mw115,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC71p : mcC71.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC72 : List MemoKey := [(12,10,1,mn872,[mw6,mw7,mw2,mw116,mw3,mw4,mw5]),(12,10,1,mn873,[mw6,mw7,mw2,mw3,mw117,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC72p : mcC72.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC73 : List MemoKey := [(12,10,1,mn882,[mw6,mw118,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn883,[mw6,mw7,mw2,mw119,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC73p : mcC73.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC74 : List MemoKey := [(12,10,1,mn884,[mw6,mw7,mw2,mw3,mw120,mw4,mw5]),(12,10,1,mn885,[mw6,mw7,mw2,mw3,mw4,mw5,mw121])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC74p : mcC74.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC75 : List MemoKey := [(12,10,1,mn900,[mw122,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn901,[mw6,mw7,mw123,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC75p : mcC75.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC76 : List MemoKey := [(12,10,1,mn902,[mw6,mw7,mw2,mw124,mw3,mw4,mw5]),(12,10,1,mn903,[mw6,mw7,mw2,mw3,mw125,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC76p : mcC76.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC77 : List MemoKey := [(12,10,1,mn916,[mw6,mw126,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn917,[mw6,mw36,mw126,mw7,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC77p : mcC77.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC78 : List MemoKey := [(12,10,1,mn918,[mw44,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn919,[mw44,mw6,mw36,mw7,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC78p : mcC78.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC79 : List MemoKey := [(12,10,1,mn920,[mw6,mw7,mw2,mw127,mw3,mw4,mw5]),(12,10,1,mn921,[mw6,mw36,mw7,mw2,mw127,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC79p : mcC79.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC80 : List MemoKey := [(12,10,1,mn922,[mw6,mw128,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn923,[mw6,mw128,mw36,mw7,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC80p : mcC80.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC81 : List MemoKey := [(12,10,1,mn924,[mw6,mw7,mw2,mw3,mw129,mw4,mw5]),(12,10,1,mn925,[mw6,mw36,mw7,mw2,mw3,mw129,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC81p : mcC81.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC82 : List MemoKey := [(12,10,1,mn926,[mw6,mw113,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn927,[mw6,mw113,mw36,mw7,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC82p : mcC82.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC83 : List MemoKey := [(12,10,1,mn928,[mw6,mw7,mw2,mw3,mw4,mw130,mw5]),(12,10,1,mn929,[mw6,mw36,mw7,mw2,mw3,mw4,mw130,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC83p : mcC83.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC84 : List MemoKey := [(12,10,1,mn930,[mw6,mw131,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn931,[mw6,mw131,mw36,mw7,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC84p : mcC84.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC85 : List MemoKey := [(12,10,1,mn940,[mw6,mw7,mw2,mw3,mw50,mw4,mw5]),(12,10,1,mn941,[mw132,mw6,mw7,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC85p : mcC85.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC86 : List MemoKey := [(12,10,1,mn942,[mw132,mw6,mw7,mw2,mw3,mw16,mw4,mw5]),(12,10,1,mn943,[mw6,mw7,mw2,mw3,mw133,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC86p : mcC86.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC87 : List MemoKey := [(12,10,1,mn944,[mw6,mw134,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn945,[mw6,mw134,mw7,mw2,mw3,mw16,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC87p : mcC87.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC88 : List MemoKey := [(12,10,1,mn946,[mw6,mw7,mw2,mw3,mw4,mw5,mw135]),(12,10,1,mn947,[mw6,mw7,mw2,mw3,mw136,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC88p : mcC88.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC89 : List MemoKey := [(12,10,1,mn948,[mw6,mw7,mw2,mw3,mw136,mw16,mw4,mw5]),(12,10,1,mn949,[mw6,mw7,mw2,mw3,mw4,mw5,mw137])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC89p : mcC89.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC90 : List MemoKey := [(12,10,1,mn950,[mw6,mw7,mw2,mw3,mw138,mw4,mw5]),(12,10,1,mn951,[mw6,mw7,mw2,mw3,mw138,mw16,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC90p : mcC90.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC91 : List MemoKey := [(12,10,1,mn959,[mw6,mw7,mw139,mw2,mw3,mw4,mw5]),(12,10,1,mn960,[mw6,mw140,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC91p : mcC91.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC92 : List MemoKey := [(12,10,1,mn961,[mw6,mw7,mw140,mw2,mw3,mw4,mw5]),(12,10,1,mn962,[mw6,mw7,mw2,mw3,mw4,mw5,mw141])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC92p : mcC92.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC93 : List MemoKey := [(12,10,1,mn963,[mw6,mw7,mw2,mw3,mw4,mw5,mw142]),(12,10,1,mn971,[mw6,mw7,mw2,mw3,mw4,mw5,mw52])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC93p : mcC93.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC94 : List MemoKey := [(12,10,1,mn972,[mw6,mw7,mw2,mw3,mw4,mw5,mw18,mw52]),(12,10,1,mn973,[mw143,mw6,mw7,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC94p : mcC94.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC95 : List MemoKey := [(12,10,1,mn974,[mw143,mw6,mw7,mw2,mw3,mw4,mw5,mw18]),(12,10,1,mn975,[mw6,mw7,mw2,mw3,mw4,mw5,mw144])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC95p : mcC95.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC96 : List MemoKey := [(12,10,1,mn976,[mw6,mw7,mw2,mw3,mw4,mw5,mw18,mw144]),(12,10,1,mn977,[mw6,mw145,mw7,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC96p : mcC96.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC97 : List MemoKey := [(12,10,1,mn978,[mw6,mw145,mw7,mw2,mw3,mw4,mw5,mw18]),(12,10,1,mn979,[mw6,mw7,mw2,mw3,mw4,mw5,mw135])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC97p : mcC97.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC98 : List MemoKey := [(12,10,1,mn980,[mw6,mw7,mw2,mw3,mw4,mw5,mw18,mw135]),(12,10,1,mn981,[mw6,mw7,mw2,mw146,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC98p : mcC98.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC99 : List MemoKey := [(12,10,1,mn982,[mw6,mw7,mw2,mw146,mw3,mw4,mw5,mw18]),(12,10,1,mn983,[mw6,mw7,mw2,mw3,mw4,mw5,mw147])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC99p : mcC99.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC100 : List MemoKey := [(12,10,1,mn984,[mw6,mw7,mw2,mw3,mw4,mw5,mw18,mw147]),(12,10,1,mn985,[mw6,mw7,mw2,mw3,mw4,mw148,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC100p : mcC100.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC101 : List MemoKey := [(12,10,1,mn986,[mw6,mw7,mw2,mw3,mw4,mw148,mw5,mw18]),(12,10,1,mn989,[mw7,mw149,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC101p : mcC101.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC102 : List MemoKey := [(12,10,1,mn990,[mw6,mw7,mw149,mw2,mw3,mw4,mw5]),(12,10,1,mn991,[mw6,mw150,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC102p : mcC102.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC103 : List MemoKey := [(12,10,1,mn992,[mw6,mw7,mw150,mw2,mw3,mw4,mw5]),(12,10,1,mn993,[mw6,mw7,mw2,mw3,mw151,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC103p : mcC103.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC104 : List MemoKey := [(12,10,1,mn994,[mw6,mw7,mw2,mw3,mw4,mw5,mw152]),(12,10,1,mn1003,[mw6,mw7,mw2,mw3,mw4,mw5,mw54])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC104p : mcC104.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC105 : List MemoKey := [(12,10,1,mn1004,[mw6,mw7,mw2,mw3,mw4,mw5,mw20,mw54]),(12,10,1,mn1005,[mw153,mw6,mw7,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC105p : mcC105.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC106 : List MemoKey := [(12,10,1,mn1006,[mw153,mw6,mw7,mw2,mw3,mw4,mw5,mw20]),(12,10,1,mn1007,[mw6,mw7,mw2,mw3,mw4,mw5,mw154])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC106p : mcC106.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC107 : List MemoKey := [(12,10,1,mn1008,[mw6,mw7,mw2,mw3,mw4,mw5,mw20,mw154]),(12,10,1,mn1009,[mw6,mw155,mw7,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC107p : mcC107.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC108 : List MemoKey := [(12,10,1,mn1010,[mw6,mw155,mw7,mw2,mw3,mw4,mw5,mw20]),(12,10,1,mn1011,[mw6,mw7,mw2,mw3,mw4,mw5,mw137])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC108p : mcC108.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC109 : List MemoKey := [(12,10,1,mn1012,[mw6,mw7,mw2,mw3,mw4,mw5,mw20,mw137]),(12,10,1,mn1013,[mw6,mw7,mw2,mw156,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC109p : mcC109.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC110 : List MemoKey := [(12,10,1,mn1014,[mw6,mw7,mw2,mw156,mw3,mw4,mw5,mw20]),(12,10,1,mn1015,[mw6,mw7,mw2,mw3,mw4,mw5,mw147])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC110p : mcC110.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC111 : List MemoKey := [(12,10,1,mn1016,[mw6,mw7,mw2,mw3,mw4,mw5,mw20,mw147]),(12,10,1,mn1017,[mw6,mw7,mw2,mw3,mw157,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC111p : mcC111.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC112 : List MemoKey := [(12,10,1,mn1018,[mw6,mw7,mw2,mw3,mw157,mw4,mw5,mw20]),(12,10,1,mn1025,[mw7,mw158,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC112p : mcC112.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC113 : List MemoKey := [(12,10,1,mn1026,[mw6,mw7,mw158,mw2,mw3,mw4,mw5]),(12,10,1,mn1027,[mw6,mw7,mw159,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC113p : mcC113.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC114 : List MemoKey := [(12,10,1,mn1028,[mw6,mw7,mw2,mw3,mw160,mw4,mw5]),(12,10,1,mn1029,[mw6,mw7,mw2,mw3,mw4,mw5,mw161])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC114p : mcC114.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC115 : List MemoKey := [(12,10,1,mn1035,[mw6,mw7,mw2,mw3,mw4,mw5,mw63]),(12,10,1,mn1036,[mw162,mw6,mw7,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC115p : mcC115.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC116 : List MemoKey := [(12,10,1,mn1037,[mw162,mw6,mw7,mw2,mw3,mw4,mw5,mw22]),(12,10,1,mn1038,[mw6,mw7,mw2,mw3,mw4,mw5,mw163])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC116p : mcC116.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC117 : List MemoKey := [(12,10,1,mn1039,[mw6,mw164,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn1040,[mw6,mw164,mw7,mw2,mw3,mw4,mw5,mw22])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC117p : mcC117.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC118 : List MemoKey := [(12,10,1,mn1041,[mw6,mw7,mw2,mw3,mw4,mw5,mw135]),(12,10,1,mn1042,[mw6,mw7,mw165,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC118p : mcC118.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC119 : List MemoKey := [(12,10,1,mn1043,[mw6,mw7,mw165,mw2,mw3,mw4,mw5,mw22]),(12,10,1,mn1044,[mw6,mw7,mw2,mw3,mw4,mw5,mw166])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC119p : mcC119.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC120 : List MemoKey := [(12,10,1,mn1045,[mw6,mw7,mw2,mw3,mw4,mw167,mw5]),(12,10,1,mn1046,[mw6,mw7,mw2,mw3,mw4,mw167,mw5,mw22])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC120p : mcC120.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC121 : List MemoKey := [(12,10,1,mn1049,[mw6,mw7,mw2,mw168,mw3,mw4,mw5]),(12,10,1,mn1050,[mw6,mw7,mw2,mw169,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC121p : mcC121.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC122 : List MemoKey := [(12,10,1,mn1051,[mw6,mw7,mw2,mw3,mw170,mw4,mw5]),(12,10,1,mn1052,[mw6,mw7,mw2,mw3,mw4,mw5,mw171])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC122p : mcC122.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC123 : List MemoKey := [(12,10,1,mn1059,[mw6,mw7,mw2,mw3,mw4,mw5,mw65]),(12,10,1,mn1060,[mw172,mw7,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC123p : mcC123.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC124 : List MemoKey := [(12,10,1,mn1061,[mw172,mw7,mw2,mw3,mw4,mw5,mw24]),(12,10,1,mn1062,[mw172,mw6,mw7,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC124p : mcC124.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC125 : List MemoKey := [(12,10,1,mn1063,[mw172,mw6,mw7,mw2,mw3,mw4,mw5,mw24]),(12,10,1,mn1064,[mw6,mw7,mw2,mw3,mw4,mw5,mw173])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC125p : mcC125.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC126 : List MemoKey := [(12,10,1,mn1065,[mw6,mw174,mw2,mw3,mw4,mw5]),(12,10,1,mn1066,[mw6,mw174,mw2,mw3,mw4,mw5,mw24])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC126p : mcC126.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC127 : List MemoKey := [(12,10,1,mn1067,[mw6,mw174,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn1068,[mw6,mw174,mw7,mw2,mw3,mw4,mw5,mw24])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC127p : mcC127.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC128 : List MemoKey := [(12,10,1,mn1069,[mw6,mw7,mw2,mw3,mw4,mw5,mw137]),(12,10,1,mn1070,[mw6,mw7,mw175,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC128p : mcC128.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC129 : List MemoKey := [(12,10,1,mn1071,[mw6,mw7,mw175,mw3,mw4,mw5,mw24]),(12,10,1,mn1072,[mw6,mw7,mw175,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC129p : mcC129.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC130 : List MemoKey := [(12,10,1,mn1073,[mw6,mw7,mw175,mw2,mw3,mw4,mw5,mw24]),(12,10,1,mn1074,[mw6,mw7,mw2,mw3,mw4,mw5,mw166])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC130p : mcC130.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC131 : List MemoKey := [(12,10,1,mn1075,[mw6,mw7,mw2,mw3,mw176,mw5]),(12,10,1,mn1076,[mw6,mw7,mw2,mw3,mw176,mw5,mw24])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC131p : mcC131.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC132 : List MemoKey := [(12,10,1,mn1077,[mw6,mw7,mw2,mw3,mw176,mw4,mw5]),(12,10,1,mn1078,[mw6,mw7,mw2,mw3,mw176,mw4,mw5,mw24])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC132p : mcC132.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC133 : List MemoKey := [(12,10,1,mn1081,[mw6,mw7,mw2,mw177,mw3,mw4,mw5]),(12,10,1,mn1082,[mw6,mw7,mw2,mw25,mw177,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC133p : mcC133.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC134 : List MemoKey := [(12,10,1,mn1083,[mw73,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn1084,[mw73,mw6,mw7,mw2,mw25,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC134p : mcC134.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC135 : List MemoKey := [(12,10,1,mn1085,[mw6,mw7,mw2,mw178,mw3,mw4,mw5]),(12,10,1,mn1086,[mw6,mw7,mw2,mw25,mw178,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC135p : mcC135.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC136 : List MemoKey := [(12,10,1,mn1087,[mw6,mw113,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn1088,[mw6,mw113,mw7,mw2,mw25,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC136p : mcC136.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC137 : List MemoKey := [(12,10,1,mn1089,[mw6,mw7,mw2,mw3,mw179,mw4,mw5]),(12,10,1,mn1090,[mw6,mw7,mw2,mw25,mw3,mw179,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC137p : mcC137.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC138 : List MemoKey := [(12,10,1,mn1091,[mw6,mw7,mw180,mw2,mw3,mw4,mw5]),(12,10,1,mn1092,[mw6,mw7,mw180,mw2,mw25,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC138p : mcC138.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC139 : List MemoKey := [(12,10,1,mn1093,[mw6,mw7,mw2,mw3,mw4,mw5,mw181]),(12,10,1,mn1094,[mw6,mw7,mw2,mw25,mw3,mw4,mw5,mw181])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC139p : mcC139.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC140 : List MemoKey := [(12,10,1,mn1095,[mw6,mw7,mw2,mw182,mw3,mw4,mw5]),(12,10,1,mn1096,[mw6,mw7,mw2,mw182,mw25,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC140p : mcC140.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC141 : List MemoKey := [(12,10,1,mn1099,[mw6,mw7,mw2,mw3,mw4,mw5,mw78]),(12,10,1,mn1100,[mw6,mw7,mw2,mw3,mw4,mw5,mw26,mw78])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC141p : mcC141.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC142 : List MemoKey := [(12,10,1,mn1101,[mw183,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn1102,[mw183,mw6,mw7,mw2,mw3,mw4,mw5,mw26])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC142p : mcC142.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC143 : List MemoKey := [(12,10,1,mn1103,[mw6,mw7,mw2,mw3,mw4,mw5,mw184]),(12,10,1,mn1104,[mw6,mw7,mw2,mw3,mw4,mw5,mw26,mw184])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC143p : mcC143.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC144 : List MemoKey := [(12,10,1,mn1105,[mw6,mw185,mw2,mw3,mw4,mw5]),(12,10,1,mn1106,[mw6,mw185,mw2,mw3,mw4,mw5,mw26])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC144p : mcC144.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC145 : List MemoKey := [(12,10,1,mn1107,[mw6,mw185,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn1108,[mw6,mw185,mw7,mw2,mw3,mw4,mw5,mw26])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC145p : mcC145.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC146 : List MemoKey := [(12,10,1,mn1109,[mw6,mw7,mw2,mw3,mw4,mw5,mw147]),(12,10,1,mn1110,[mw6,mw7,mw2,mw3,mw4,mw5,mw26,mw147])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC146p : mcC146.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC147 : List MemoKey := [(12,10,1,mn1111,[mw6,mw7,mw186,mw2,mw3,mw4,mw5]),(12,10,1,mn1112,[mw6,mw7,mw186,mw2,mw3,mw4,mw5,mw26])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC147p : mcC147.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC148 : List MemoKey := [(12,10,1,mn1113,[mw6,mw7,mw2,mw3,mw4,mw5,mw166]),(12,10,1,mn1114,[mw6,mw7,mw2,mw3,mw4,mw5,mw26,mw166])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC148p : mcC148.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC149 : List MemoKey := [(12,10,1,mn1115,[mw6,mw7,mw2,mw187,mw3,mw4,mw5]),(12,10,1,mn1116,[mw6,mw7,mw2,mw187,mw3,mw4,mw5,mw26])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC149p : mcC149.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC150 : List MemoKey := [(12,10,1,mn1117,[mw7,mw2,mw3,mw188,mw4,mw5]),(12,10,1,mn1118,[mw6,mw7,mw2,mw3,mw188,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC150p : mcC150.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC151 : List MemoKey := [(12,10,1,mn1119,[mw6,mw2,mw3,mw189,mw4,mw5]),(12,10,1,mn1120,[mw6,mw7,mw2,mw3,mw189,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC151p : mcC151.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC152 : List MemoKey := [(12,10,1,mn1121,[mw6,mw7,mw3,mw4,mw5,mw190]),(12,10,1,mn1122,[mw6,mw7,mw2,mw3,mw4,mw5,mw190])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC152p : mcC152.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC153 : List MemoKey := [(12,10,1,mn1123,[mw6,mw7,mw2,mw4,mw5,mw191]),(12,10,1,mn1124,[mw6,mw7,mw2,mw3,mw4,mw5,mw191])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC153p : mcC153.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC154 : List MemoKey := [(12,10,0,mn1125,[mw6,mw7,mw192,mw2,mw3,mw4]),(12,10,0,mn1126,[mw6,mw7,mw193,mw192,mw2,mw3,mw4])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC154p : mcC154.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC155 : List MemoKey := [(12,10,0,mn1127,[mw194,mw6,mw7,mw2,mw3,mw4]),(12,10,0,mn1128,[mw194,mw6,mw7,mw193,mw2,mw3,mw4])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC155p : mcC155.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC156 : List MemoKey := [(12,10,0,mn1129,[mw6,mw7,mw195,mw2,mw3,mw4]),(12,10,0,mn1130,[mw6,mw7,mw193,mw195,mw2,mw3,mw4])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC156p : mcC156.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC157 : List MemoKey := [(12,10,0,mn1131,[mw6,mw196,mw7,mw2,mw3,mw4]),(12,10,0,mn1132,[mw6,mw196,mw7,mw193,mw2,mw3,mw4])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC157p : mcC157.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC158 : List MemoKey := [(12,10,0,mn1133,[mw6,mw7,mw2,mw197,mw3,mw4]),(12,10,0,mn1134,[mw6,mw7,mw193,mw2,mw197,mw3,mw4])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC158p : mcC158.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC159 : List MemoKey := [(12,10,0,mn1135,[mw6,mw7,mw198,mw2,mw3,mw4]),(12,10,0,mn1136,[mw6,mw7,mw198,mw193,mw2,mw3,mw4])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC159p : mcC159.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC160 : List MemoKey := [(12,10,0,mn1137,[mw6,mw7,mw2,mw3,mw199,mw4]),(12,10,0,mn1138,[mw6,mw7,mw193,mw2,mw3,mw199,mw4])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC160p : mcC160.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC161 : List MemoKey := [(12,10,0,mn1139,[mw6,mw7,mw200,mw2,mw3,mw4]),(12,10,0,mn1140,[mw6,mw7,mw200,mw193,mw2,mw3,mw4])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC161p : mcC161.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC162 : List MemoKey := [(12,10,0,mn1141,[mw6,mw7,mw2,mw3,mw4,mw201]),(12,10,0,mn1142,[mw6,mw7,mw193,mw2,mw3,mw4,mw201])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC162p : mcC162.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC163 : List MemoKey := [(12,10,0,mn1143,[mw6,mw7,mw202,mw2,mw3,mw4]),(12,10,0,mn1144,[mw6,mw7,mw202,mw193,mw2,mw3,mw4])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC163p : mcC163.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC164 : List MemoKey := [(12,10,0,mn1126,[mw6,mw7,mw192,mw2,mw3,mw4,mw5]),(12,10,0,mn1145,[mw6,mw7,mw193,mw192,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC164p : mcC164.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC165 : List MemoKey := [(12,10,0,mn1128,[mw194,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,0,mn1146,[mw194,mw6,mw7,mw193,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC165p : mcC165.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC166 : List MemoKey := [(12,10,0,mn1130,[mw6,mw7,mw195,mw2,mw3,mw4,mw5]),(12,10,0,mn1147,[mw6,mw7,mw193,mw195,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC166p : mcC166.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC167 : List MemoKey := [(12,10,0,mn1132,[mw6,mw196,mw7,mw2,mw3,mw4,mw5]),(12,10,0,mn1148,[mw6,mw196,mw7,mw193,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC167p : mcC167.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC168 : List MemoKey := [(12,10,0,mn1134,[mw6,mw7,mw2,mw197,mw3,mw4,mw5]),(12,10,0,mn1149,[mw6,mw7,mw193,mw2,mw197,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC168p : mcC168.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC169 : List MemoKey := [(12,10,0,mn1136,[mw6,mw7,mw198,mw2,mw3,mw4,mw5]),(12,10,0,mn1150,[mw6,mw7,mw198,mw193,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC169p : mcC169.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC170 : List MemoKey := [(12,10,0,mn1138,[mw6,mw7,mw2,mw3,mw199,mw4,mw5]),(12,10,0,mn1151,[mw6,mw7,mw193,mw2,mw3,mw199,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC170p : mcC170.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC171 : List MemoKey := [(12,10,0,mn1140,[mw6,mw7,mw200,mw2,mw3,mw4,mw5]),(12,10,0,mn1152,[mw6,mw7,mw200,mw193,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC171p : mcC171.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC172 : List MemoKey := [(12,10,0,mn1142,[mw6,mw7,mw2,mw3,mw4,mw201,mw5]),(12,10,0,mn1153,[mw6,mw7,mw193,mw2,mw3,mw4,mw201,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC172p : mcC172.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC173 : List MemoKey := [(12,10,0,mn1144,[mw6,mw7,mw202,mw2,mw3,mw4,mw5]),(12,10,0,mn1154,[mw6,mw7,mw202,mw193,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC173p : mcC173.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC174 : List MemoKey := [(12,10,0,mn1155,[mw6,mw7,mw203,mw2,mw3,mw5]),(12,10,0,mn1156,[mw204,mw6,mw7,mw2,mw3,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC174p : mcC174.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC175 : List MemoKey := [(12,10,0,mn1157,[mw204,mw6,mw7,mw205,mw2,mw3,mw5]),(12,10,0,mn1158,[mw6,mw7,mw206,mw2,mw3,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC175p : mcC175.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC176 : List MemoKey := [(12,10,0,mn1159,[mw6,mw207,mw7,mw2,mw3,mw5]),(12,10,0,mn1160,[mw6,mw207,mw7,mw205,mw2,mw3,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC176p : mcC176.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC177 : List MemoKey := [(12,10,0,mn1161,[mw6,mw7,mw2,mw208,mw3,mw5]),(12,10,0,mn1162,[mw6,mw7,mw209,mw2,mw3,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC177p : mcC177.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC178 : List MemoKey := [(12,10,0,mn1163,[mw6,mw7,mw209,mw205,mw2,mw3,mw5]),(12,10,0,mn1164,[mw6,mw7,mw2,mw3,mw210,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC178p : mcC178.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC179 : List MemoKey := [(12,10,0,mn1165,[mw6,mw7,mw211,mw2,mw3,mw5]),(12,10,0,mn1166,[mw6,mw7,mw211,mw205,mw2,mw3,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC179p : mcC179.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC180 : List MemoKey := [(12,10,0,mn1143,[mw6,mw7,mw2,mw3,mw5,mw212]),(12,10,0,mn1141,[mw6,mw7,mw213,mw2,mw3,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC180p : mcC180.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC181 : List MemoKey := [(12,10,0,mn1167,[mw6,mw7,mw213,mw205,mw2,mw3,mw5]),(12,10,0,mn1157,[mw204,mw6,mw7,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC181p : mcC181.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC182 : List MemoKey := [(12,10,0,mn1160,[mw6,mw207,mw7,mw2,mw3,mw4,mw5]),(12,10,0,mn1163,[mw6,mw7,mw209,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC182p : mcC182.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC183 : List MemoKey := [(12,10,0,mn1166,[mw6,mw7,mw211,mw2,mw3,mw4,mw5]),(12,10,0,mn1167,[mw6,mw7,mw213,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC183p : mcC183.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC184 : List MemoKey := [(12,10,0,mn1168,[mw6,mw7,mw2,mw214,mw4,mw5]),(12,10,0,mn1169,[mw6,mw7,mw2,mw215,mw214,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC184p : mcC184.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC185 : List MemoKey := [(12,10,0,mn1170,[mw216,mw6,mw7,mw2,mw4,mw5]),(12,10,0,mn1171,[mw216,mw6,mw7,mw2,mw215,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC185p : mcC185.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC186 : List MemoKey := [(12,10,0,mn1172,[mw6,mw7,mw2,mw217,mw4,mw5]),(12,10,0,mn1173,[mw6,mw7,mw2,mw215,mw217,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC186p : mcC186.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC187 : List MemoKey := [(12,10,0,mn1174,[mw6,mw218,mw7,mw2,mw4,mw5]),(12,10,0,mn1175,[mw6,mw218,mw7,mw2,mw215,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC187p : mcC187.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC188 : List MemoKey := [(12,10,0,mn1176,[mw6,mw7,mw2,mw219,mw4,mw5]),(12,10,0,mn1177,[mw6,mw7,mw2,mw215,mw219,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC188p : mcC188.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC189 : List MemoKey := [(12,10,0,mn1178,[mw6,mw7,mw220,mw2,mw4,mw5]),(12,10,0,mn1179,[mw6,mw7,mw220,mw2,mw215,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC189p : mcC189.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC190 : List MemoKey := [(12,10,0,mn1165,[mw6,mw7,mw2,mw4,mw221,mw5]),(12,10,0,mn1180,[mw6,mw7,mw2,mw215,mw4,mw221,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC190p : mcC190.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC191 : List MemoKey := [(12,10,0,mn1164,[mw6,mw7,mw2,mw222,mw4,mw5]),(12,10,0,mn1181,[mw6,mw7,mw2,mw222,mw215,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC191p : mcC191.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC192 : List MemoKey := [(12,10,0,mn1139,[mw6,mw7,mw2,mw4,mw5,mw223]),(12,10,0,mn1182,[mw6,mw7,mw2,mw215,mw4,mw5,mw223])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC192p : mcC192.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC193 : List MemoKey := [(12,10,0,mn1137,[mw6,mw7,mw2,mw224,mw4,mw5]),(12,10,0,mn1183,[mw6,mw7,mw2,mw224,mw215,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC193p : mcC193.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC194 : List MemoKey := [(12,10,0,mn1169,[mw6,mw7,mw2,mw3,mw214,mw4,mw5]),(12,10,0,mn1184,[mw6,mw7,mw2,mw3,mw215,mw214,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC194p : mcC194.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC195 : List MemoKey := [(12,10,0,mn1171,[mw216,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,0,mn1173,[mw6,mw7,mw2,mw3,mw217,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC195p : mcC195.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC196 : List MemoKey := [(12,10,0,mn1185,[mw6,mw7,mw2,mw3,mw215,mw217,mw4,mw5]),(12,10,0,mn1175,[mw6,mw218,mw7,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC196p : mcC196.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC197 : List MemoKey := [(12,10,0,mn1177,[mw6,mw7,mw2,mw3,mw219,mw4,mw5]),(12,10,0,mn1186,[mw6,mw7,mw2,mw3,mw215,mw219,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC197p : mcC197.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC198 : List MemoKey := [(12,10,0,mn1179,[mw6,mw7,mw220,mw2,mw3,mw4,mw5]),(12,10,0,mn1180,[mw6,mw7,mw2,mw3,mw4,mw221,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC198p : mcC198.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC199 : List MemoKey := [(12,10,0,mn1187,[mw6,mw7,mw2,mw3,mw215,mw4,mw221,mw5]),(12,10,0,mn1181,[mw6,mw7,mw2,mw3,mw222,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC199p : mcC199.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC200 : List MemoKey := [(12,10,0,mn1182,[mw6,mw7,mw2,mw3,mw4,mw5,mw223]),(12,10,0,mn1188,[mw6,mw7,mw2,mw3,mw215,mw4,mw5,mw223])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC200p : mcC200.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC201 : List MemoKey := [(12,10,0,mn1183,[mw6,mw7,mw2,mw3,mw224,mw4,mw5]),(12,10,0,mn1189,[mw6,mw7,mw3,mw225,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC201p : mcC201.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC202 : List MemoKey := [(12,10,0,mn1190,[mw226,mw6,mw7,mw3,mw4,mw5]),(12,10,0,mn1191,[mw226,mw6,mw7,mw3,mw227,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC202p : mcC202.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC203 : List MemoKey := [(12,10,0,mn1192,[mw6,mw7,mw3,mw228,mw4,mw5]),(12,10,0,mn1193,[mw6,mw229,mw7,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC203p : mcC203.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC204 : List MemoKey := [(12,10,0,mn1194,[mw6,mw229,mw7,mw3,mw227,mw4,mw5]),(12,10,0,mn1178,[mw6,mw7,mw3,mw230,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC204p : mcC204.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC205 : List MemoKey := [(12,10,0,mn1176,[mw6,mw7,mw231,mw3,mw4,mw5]),(12,10,0,mn1195,[mw6,mw7,mw231,mw3,mw227,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC205p : mcC205.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC206 : List MemoKey := [(12,10,0,mn1162,[mw6,mw7,mw3,mw4,mw232,mw5]),(12,10,0,mn1161,[mw6,mw7,mw3,mw233,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC206p : mcC206.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC207 : List MemoKey := [(12,10,0,mn1196,[mw6,mw7,mw3,mw233,mw227,mw4,mw5]),(12,10,0,mn1135,[mw6,mw7,mw3,mw4,mw5,mw234])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC207p : mcC207.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC208 : List MemoKey := [(12,10,0,mn1133,[mw6,mw7,mw3,mw235,mw4,mw5]),(12,10,0,mn1197,[mw6,mw7,mw3,mw235,mw227,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC208p : mcC208.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC209 : List MemoKey := [(12,10,0,mn1191,[mw226,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,0,mn1194,[mw6,mw229,mw7,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC209p : mcC209.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC210 : List MemoKey := [(12,10,0,mn1195,[mw6,mw7,mw2,mw231,mw3,mw4,mw5]),(12,10,0,mn1196,[mw6,mw7,mw2,mw3,mw233,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC210p : mcC210.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC211 : List MemoKey := [(12,10,0,mn1197,[mw6,mw7,mw2,mw3,mw235,mw4,mw5]),(12,10,0,mn1198,[mw6,mw2,mw3,mw4,mw5,mw236])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC211p : mcC211.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC212 : List MemoKey := [(12,10,0,mn1199,[mw6,mw2,mw3,mw4,mw5,mw237,mw236]),(12,10,0,mn1200,[mw238,mw6,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC212p : mcC212.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC213 : List MemoKey := [(12,10,0,mn1193,[mw6,mw2,mw3,mw4,mw5,mw239]),(12,10,0,mn1201,[mw6,mw2,mw3,mw4,mw5,mw237,mw239])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC213p : mcC213.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC214 : List MemoKey := [(12,10,0,mn1192,[mw6,mw240,mw2,mw3,mw4,mw5]),(12,10,0,mn1174,[mw6,mw2,mw3,mw4,mw5,mw241])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC214p : mcC214.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC215 : List MemoKey := [(12,10,0,mn1202,[mw6,mw2,mw3,mw4,mw5,mw237,mw241]),(12,10,0,mn1172,[mw6,mw2,mw242,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC215p : mcC215.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC216 : List MemoKey := [(12,10,0,mn1159,[mw6,mw2,mw3,mw4,mw5,mw243]),(12,10,0,mn1203,[mw6,mw2,mw3,mw4,mw5,mw237,mw243])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC216p : mcC216.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC217 : List MemoKey := [(12,10,0,mn1158,[mw6,mw2,mw3,mw244,mw4,mw5]),(12,10,0,mn1131,[mw6,mw2,mw3,mw4,mw5,mw245])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC217p : mcC217.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC218 : List MemoKey := [(12,10,0,mn1204,[mw6,mw2,mw3,mw4,mw5,mw237,mw245]),(12,10,0,mn1129,[mw6,mw2,mw3,mw4,mw246,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC218p : mcC218.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC219 : List MemoKey := [(12,10,0,mn1199,[mw6,mw7,mw2,mw3,mw4,mw5,mw236]),(12,10,0,mn1201,[mw6,mw7,mw2,mw3,mw4,mw5,mw239])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC219p : mcC219.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC220 : List MemoKey := [(12,10,0,mn1202,[mw6,mw7,mw2,mw3,mw4,mw5,mw241]),(12,10,0,mn1203,[mw6,mw7,mw2,mw3,mw4,mw5,mw243])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC220p : mcC220.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC221 : List MemoKey := [(12,10,0,mn1204,[mw6,mw7,mw2,mw3,mw4,mw5,mw245]),(12,10,0,mn1200,[mw7,mw2,mw3,mw4,mw5,mw247])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC221p : mcC221.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC222 : List MemoKey := [(12,10,0,mn1205,[mw7,mw2,mw3,mw4,mw5,mw248,mw247]),(12,10,0,mn1198,[mw249,mw7,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC222p : mcC222.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC223 : List MemoKey := [(12,10,0,mn1206,[mw249,mw7,mw2,mw3,mw4,mw5,mw248]),(12,10,0,mn1190,[mw7,mw2,mw3,mw4,mw5,mw250])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC223p : mcC223.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC224 : List MemoKey := [(12,10,0,mn1207,[mw7,mw2,mw3,mw4,mw5,mw248,mw250]),(12,10,0,mn1189,[mw7,mw251,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC224p : mcC224.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC225 : List MemoKey := [(12,10,0,mn1208,[mw7,mw251,mw2,mw3,mw4,mw5,mw248]),(12,10,0,mn1170,[mw7,mw2,mw3,mw4,mw5,mw252])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC225p : mcC225.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC226 : List MemoKey := [(12,10,0,mn1209,[mw7,mw2,mw3,mw4,mw5,mw248,mw252]),(12,10,0,mn1168,[mw7,mw2,mw253,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC226p : mcC226.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC227 : List MemoKey := [(12,10,0,mn1210,[mw7,mw2,mw253,mw3,mw4,mw5,mw248]),(12,10,0,mn1156,[mw7,mw2,mw3,mw4,mw5,mw254])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC227p : mcC227.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC228 : List MemoKey := [(12,10,0,mn1211,[mw7,mw2,mw3,mw4,mw5,mw248,mw254]),(12,10,0,mn1155,[mw7,mw2,mw3,mw255,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC228p : mcC228.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC229 : List MemoKey := [(12,10,0,mn1212,[mw7,mw2,mw3,mw255,mw4,mw5,mw248]),(12,10,0,mn1127,[mw7,mw2,mw3,mw4,mw5,mw256])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC229p : mcC229.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC230 : List MemoKey := [(12,10,0,mn1213,[mw7,mw2,mw3,mw4,mw5,mw248,mw256]),(12,10,0,mn1125,[mw7,mw2,mw3,mw4,mw257,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC230p : mcC230.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC231 : List MemoKey := [(12,10,0,mn1214,[mw7,mw2,mw3,mw4,mw257,mw5,mw248]),(12,10,0,mn1205,[mw6,mw7,mw2,mw3,mw4,mw5,mw247])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC231p : mcC231.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC232 : List MemoKey := [(12,10,0,mn1206,[mw6,mw249,mw7,mw2,mw3,mw4,mw5]),(12,10,0,mn1215,[mw6,mw249,mw7,mw2,mw3,mw4,mw5,mw248])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC232p : mcC232.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC233 : List MemoKey := [(12,10,0,mn1207,[mw6,mw7,mw2,mw3,mw4,mw5,mw250]),(12,10,0,mn1208,[mw6,mw7,mw251,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC233p : mcC233.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC234 : List MemoKey := [(12,10,0,mn1216,[mw6,mw7,mw251,mw2,mw3,mw4,mw5,mw248]),(12,10,0,mn1209,[mw6,mw7,mw2,mw3,mw4,mw5,mw252])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC234p : mcC234.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC235 : List MemoKey := [(12,10,0,mn1210,[mw6,mw7,mw2,mw253,mw3,mw4,mw5]),(12,10,0,mn1217,[mw6,mw7,mw2,mw253,mw3,mw4,mw5,mw248])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC235p : mcC235.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC236 : List MemoKey := [(12,10,0,mn1211,[mw6,mw7,mw2,mw3,mw4,mw5,mw254]),(12,10,0,mn1212,[mw6,mw7,mw2,mw3,mw255,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC236p : mcC236.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC237 : List MemoKey := [(12,10,0,mn1218,[mw6,mw7,mw2,mw3,mw255,mw4,mw5,mw248]),(12,10,0,mn1213,[mw6,mw7,mw2,mw3,mw4,mw5,mw256])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC237p : mcC237.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC238 : List MemoKey := [(12,10,0,mn1214,[mw6,mw7,mw2,mw3,mw4,mw257,mw5]),(12,10,0,mn1219,[mw6,mw7,mw2,mw3,mw4,mw257,mw5,mw248])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC238p : mcC238.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def memoChunksC : List {xs : List MemoKey // xs.all (fun e => !(keyRun originalC e)) = true} := [⟨mcC0,mcC0p⟩,⟨mcC1,mcC1p⟩,⟨mcC2,mcC2p⟩,⟨mcC3,mcC3p⟩,⟨mcC4,mcC4p⟩,⟨mcC5,mcC5p⟩,⟨mcC6,mcC6p⟩,⟨mcC7,mcC7p⟩,⟨mcC8,mcC8p⟩,⟨mcC9,mcC9p⟩,⟨mcC10,mcC10p⟩,⟨mcC11,mcC11p⟩,⟨mcC12,mcC12p⟩,⟨mcC13,mcC13p⟩,⟨mcC14,mcC14p⟩,⟨mcC15,mcC15p⟩,⟨mcC16,mcC16p⟩,⟨mcC17,mcC17p⟩,⟨mcC18,mcC18p⟩,⟨mcC19,mcC19p⟩,⟨mcC20,mcC20p⟩,⟨mcC21,mcC21p⟩,⟨mcC22,mcC22p⟩,⟨mcC23,mcC23p⟩,⟨mcC24,mcC24p⟩,⟨mcC25,mcC25p⟩,⟨mcC26,mcC26p⟩,⟨mcC27,mcC27p⟩,⟨mcC28,mcC28p⟩,⟨mcC29,mcC29p⟩,⟨mcC30,mcC30p⟩,⟨mcC31,mcC31p⟩,⟨mcC32,mcC32p⟩,⟨mcC33,mcC33p⟩,⟨mcC34,mcC34p⟩,⟨mcC35,mcC35p⟩,⟨mcC36,mcC36p⟩,⟨mcC37,mcC37p⟩,⟨mcC38,mcC38p⟩,⟨mcC39,mcC39p⟩,⟨mcC40,mcC40p⟩,⟨mcC41,mcC41p⟩,⟨mcC42,mcC42p⟩,⟨mcC43,mcC43p⟩,⟨mcC44,mcC44p⟩,⟨mcC45,mcC45p⟩,⟨mcC46,mcC46p⟩,⟨mcC47,mcC47p⟩,⟨mcC48,mcC48p⟩,⟨mcC49,mcC49p⟩,⟨mcC50,mcC50p⟩,⟨mcC51,mcC51p⟩,⟨mcC52,mcC52p⟩,⟨mcC53,mcC53p⟩,⟨mcC54,mcC54p⟩,⟨mcC55,mcC55p⟩,⟨mcC56,mcC56p⟩,⟨mcC57,mcC57p⟩,⟨mcC58,mcC58p⟩,⟨mcC59,mcC59p⟩,⟨mcC60,mcC60p⟩,⟨mcC61,mcC61p⟩,⟨mcC62,mcC62p⟩,⟨mcC63,mcC63p⟩,⟨mcC64,mcC64p⟩,⟨mcC65,mcC65p⟩,⟨mcC66,mcC66p⟩,⟨mcC67,mcC67p⟩,⟨mcC68,mcC68p⟩,⟨mcC69,mcC69p⟩,⟨mcC70,mcC70p⟩,⟨mcC71,mcC71p⟩,⟨mcC72,mcC72p⟩,⟨mcC73,mcC73p⟩,⟨mcC74,mcC74p⟩,⟨mcC75,mcC75p⟩,⟨mcC76,mcC76p⟩,⟨mcC77,mcC77p⟩,⟨mcC78,mcC78p⟩,⟨mcC79,mcC79p⟩,⟨mcC80,mcC80p⟩,⟨mcC81,mcC81p⟩,⟨mcC82,mcC82p⟩,⟨mcC83,mcC83p⟩,⟨mcC84,mcC84p⟩,⟨mcC85,mcC85p⟩,⟨mcC86,mcC86p⟩,⟨mcC87,mcC87p⟩,⟨mcC88,mcC88p⟩,⟨mcC89,mcC89p⟩,⟨mcC90,mcC90p⟩,⟨mcC91,mcC91p⟩,⟨mcC92,mcC92p⟩,⟨mcC93,mcC93p⟩,⟨mcC94,mcC94p⟩,⟨mcC95,mcC95p⟩,⟨mcC96,mcC96p⟩,⟨mcC97,mcC97p⟩,⟨mcC98,mcC98p⟩,⟨mcC99,mcC99p⟩,⟨mcC100,mcC100p⟩,⟨mcC101,mcC101p⟩,⟨mcC102,mcC102p⟩,⟨mcC103,mcC103p⟩,⟨mcC104,mcC104p⟩,⟨mcC105,mcC105p⟩,⟨mcC106,mcC106p⟩,⟨mcC107,mcC107p⟩,⟨mcC108,mcC108p⟩,⟨mcC109,mcC109p⟩,⟨mcC110,mcC110p⟩,⟨mcC111,mcC111p⟩,⟨mcC112,mcC112p⟩,⟨mcC113,mcC113p⟩,⟨mcC114,mcC114p⟩,⟨mcC115,mcC115p⟩,⟨mcC116,mcC116p⟩,⟨mcC117,mcC117p⟩,⟨mcC118,mcC118p⟩,⟨mcC119,mcC119p⟩,⟨mcC120,mcC120p⟩,⟨mcC121,mcC121p⟩,⟨mcC122,mcC122p⟩,⟨mcC123,mcC123p⟩,⟨mcC124,mcC124p⟩,⟨mcC125,mcC125p⟩,⟨mcC126,mcC126p⟩,⟨mcC127,mcC127p⟩,⟨mcC128,mcC128p⟩,⟨mcC129,mcC129p⟩,⟨mcC130,mcC130p⟩,⟨mcC131,mcC131p⟩,⟨mcC132,mcC132p⟩,⟨mcC133,mcC133p⟩,⟨mcC134,mcC134p⟩,⟨mcC135,mcC135p⟩,⟨mcC136,mcC136p⟩,⟨mcC137,mcC137p⟩,⟨mcC138,mcC138p⟩,⟨mcC139,mcC139p⟩,⟨mcC140,mcC140p⟩,⟨mcC141,mcC141p⟩,⟨mcC142,mcC142p⟩,⟨mcC143,mcC143p⟩,⟨mcC144,mcC144p⟩,⟨mcC145,mcC145p⟩,⟨mcC146,mcC146p⟩,⟨mcC147,mcC147p⟩,⟨mcC148,mcC148p⟩,⟨mcC149,mcC149p⟩,⟨mcC150,mcC150p⟩,⟨mcC151,mcC151p⟩,⟨mcC152,mcC152p⟩,⟨mcC153,mcC153p⟩,⟨mcC154,mcC154p⟩,⟨mcC155,mcC155p⟩,⟨mcC156,mcC156p⟩,⟨mcC157,mcC157p⟩,⟨mcC158,mcC158p⟩,⟨mcC159,mcC159p⟩,⟨mcC160,mcC160p⟩,⟨mcC161,mcC161p⟩,⟨mcC162,mcC162p⟩,⟨mcC163,mcC163p⟩,⟨mcC164,mcC164p⟩,⟨mcC165,mcC165p⟩,⟨mcC166,mcC166p⟩,⟨mcC167,mcC167p⟩,⟨mcC168,mcC168p⟩,⟨mcC169,mcC169p⟩,⟨mcC170,mcC170p⟩,⟨mcC171,mcC171p⟩,⟨mcC172,mcC172p⟩,⟨mcC173,mcC173p⟩,⟨mcC174,mcC174p⟩,⟨mcC175,mcC175p⟩,⟨mcC176,mcC176p⟩,⟨mcC177,mcC177p⟩,⟨mcC178,mcC178p⟩,⟨mcC179,mcC179p⟩,⟨mcC180,mcC180p⟩,⟨mcC181,mcC181p⟩,⟨mcC182,mcC182p⟩,⟨mcC183,mcC183p⟩,⟨mcC184,mcC184p⟩,⟨mcC185,mcC185p⟩,⟨mcC186,mcC186p⟩,⟨mcC187,mcC187p⟩,⟨mcC188,mcC188p⟩,⟨mcC189,mcC189p⟩,⟨mcC190,mcC190p⟩,⟨mcC191,mcC191p⟩,⟨mcC192,mcC192p⟩,⟨mcC193,mcC193p⟩,⟨mcC194,mcC194p⟩,⟨mcC195,mcC195p⟩,⟨mcC196,mcC196p⟩,⟨mcC197,mcC197p⟩,⟨mcC198,mcC198p⟩,⟨mcC199,mcC199p⟩,⟨mcC200,mcC200p⟩,⟨mcC201,mcC201p⟩,⟨mcC202,mcC202p⟩,⟨mcC203,mcC203p⟩,⟨mcC204,mcC204p⟩,⟨mcC205,mcC205p⟩,⟨mcC206,mcC206p⟩,⟨mcC207,mcC207p⟩,⟨mcC208,mcC208p⟩,⟨mcC209,mcC209p⟩,⟨mcC210,mcC210p⟩,⟨mcC211,mcC211p⟩,⟨mcC212,mcC212p⟩,⟨mcC213,mcC213p⟩,⟨mcC214,mcC214p⟩,⟨mcC215,mcC215p⟩,⟨mcC216,mcC216p⟩,⟨mcC217,mcC217p⟩,⟨mcC218,mcC218p⟩,⟨mcC219,mcC219p⟩,⟨mcC220,mcC220p⟩,⟨mcC221,mcC221p⟩,⟨mcC222,mcC222p⟩,⟨mcC223,mcC223p⟩,⟨mcC224,mcC224p⟩,⟨mcC225,mcC225p⟩,⟨mcC226,mcC226p⟩,⟨mcC227,mcC227p⟩,⟨mcC228,mcC228p⟩,⟨mcC229,mcC229p⟩,⟨mcC230,mcC230p⟩,⟨mcC231,mcC231p⟩,⟨mcC232,mcC232p⟩,⟨mcC233,mcC233p⟩,⟨mcC234,mcC234p⟩,⟨mcC235,mcC235p⟩,⟨mcC236,mcC236p⟩,⟨mcC237,mcC237p⟩,⟨mcC238,mcC238p⟩]
def memoKeysC : List MemoKey := (memoChunksC.map Subtype.val).flatten
lemma memoKeysC_sound : ∀ e ∈ memoKeysC, keyRun originalC e = false := checkedChunks_sound (keyRun originalC) memoChunksC
def mcS0 : List MemoKey := [(11,10,1,mn455,[mw0,mw1,mw2,mw3,mw4,mw5]),(11,10,1,mn456,[mw0,mw6,mw1,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS0p : mcS0.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS1 : List MemoKey := [(11,10,1,mn457,[mw6,mw7,mw1,mw2,mw8,mw3,mw4,mw5]),(11,10,1,mn458,[mw9,mw6,mw7,mw1,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS1p : mcS1.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS2 : List MemoKey := [(11,10,1,mn459,[mw6,mw7,mw1,mw2,mw3,mw10,mw4,mw5]),(11,10,1,mn460,[mw11,mw6,mw7,mw1,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS2p : mcS2.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS3 : List MemoKey := [(11,10,1,mn461,[mw6,mw7,mw1,mw2,mw3,mw4,mw12,mw5]),(11,10,1,mn462,[mw13,mw6,mw7,mw1,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS3p : mcS3.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS4 : List MemoKey := [(11,10,1,mn463,[mw6,mw7,mw1,mw2,mw3,mw4,mw5,mw14]),(11,10,1,mn464,[mw15,mw6,mw7,mw1,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS4p : mcS4.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS5 : List MemoKey := [(11,10,1,mn465,[mw6,mw7,mw1,mw2,mw3,mw16,mw4,mw5]),(11,10,1,mn466,[mw6,mw7,mw1,mw17,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS5p : mcS5.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS6 : List MemoKey := [(11,10,1,mn467,[mw6,mw7,mw1,mw2,mw3,mw4,mw5,mw18]),(11,10,1,mn468,[mw6,mw7,mw1,mw19,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS6p : mcS6.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS7 : List MemoKey := [(11,10,1,mn469,[mw6,mw7,mw1,mw2,mw3,mw4,mw5,mw20]),(11,10,1,mn470,[mw6,mw7,mw1,mw21,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS7p : mcS7.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS8 : List MemoKey := [(11,10,1,mn471,[mw6,mw7,mw1,mw2,mw3,mw4,mw5,mw22]),(11,10,1,mn472,[mw6,mw7,mw1,mw2,mw23,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS8p : mcS8.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS9 : List MemoKey := [(11,10,1,mn473,[mw6,mw7,mw1,mw2,mw3,mw4,mw5,mw24]),(11,10,1,mn474,[mw6,mw7,mw1,mw2,mw25,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS9p : mcS9.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS10 : List MemoKey := [(11,10,1,mn475,[mw6,mw7,mw1,mw2,mw3,mw4,mw5,mw26]),(11,10,1,mn476,[mw6,mw7,mw1,mw2,mw3,mw27,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS10p : mcS10.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS11 : List MemoKey := [(11,10,1,mn481,[mw0,mw6,mw7,mw2,mw8,mw3,mw4,mw5]),(11,10,1,mn482,[mw0,mw6,mw7,mw2,mw3,mw10,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS11p : mcS11.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS12 : List MemoKey := [(11,10,1,mn483,[mw0,mw11,mw7,mw2,mw3,mw4,mw5]),(11,10,1,mn484,[mw0,mw7,mw2,mw3,mw4,mw12,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS12p : mcS12.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS13 : List MemoKey := [(11,10,1,mn485,[mw0,mw6,mw7,mw2,mw3,mw4,mw12,mw5]),(11,10,1,mn486,[mw0,mw6,mw7,mw2,mw3,mw4,mw5,mw14])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS13p : mcS13.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS14 : List MemoKey := [(11,10,1,mn487,[mw0,mw6,mw32,mw7,mw2,mw3,mw4,mw5]),(11,10,1,mn488,[mw0,mw6,mw33,mw7,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS14p : mcS14.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS15 : List MemoKey := [(11,10,1,mn489,[mw0,mw6,mw2,mw3,mw4,mw34,mw5]),(11,10,1,mn490,[mw0,mw6,mw35,mw7,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS15p : mcS15.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS16 : List MemoKey := [(11,10,1,mn491,[mw0,mw6,mw36,mw2,mw3,mw4,mw5]),(11,10,1,mn492,[mw0,mw6,mw36,mw7,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS16p : mcS16.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS17 : List MemoKey := [(11,10,1,mn493,[mw0,mw6,mw7,mw2,mw3,mw16,mw4,mw5]),(11,10,1,mn494,[mw0,mw6,mw7,mw17,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS17p : mcS17.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS18 : List MemoKey := [(11,10,1,mn495,[mw0,mw6,mw7,mw2,mw3,mw4,mw5,mw18]),(11,10,1,mn496,[mw0,mw6,mw7,mw19,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS18p : mcS18.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS19 : List MemoKey := [(11,10,1,mn497,[mw0,mw6,mw7,mw2,mw3,mw4,mw5,mw20]),(11,10,1,mn498,[mw0,mw6,mw7,mw21,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS19p : mcS19.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS20 : List MemoKey := [(11,10,1,mn499,[mw0,mw6,mw7,mw2,mw3,mw4,mw5,mw22]),(11,10,1,mn500,[mw0,mw6,mw7,mw2,mw23,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS20p : mcS20.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS21 : List MemoKey := [(11,10,1,mn501,[mw0,mw6,mw7,mw2,mw3,mw4,mw5,mw24]),(11,10,1,mn502,[mw0,mw6,mw7,mw2,mw25,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS21p : mcS21.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS22 : List MemoKey := [(11,10,1,mn503,[mw0,mw6,mw7,mw2,mw3,mw4,mw5,mw26]),(11,10,1,mn504,[mw0,mw6,mw7,mw2,mw3,mw27,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS22p : mcS22.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS23 : List MemoKey := [(11,10,1,mn517,[mw9,mw7,mw8,mw3,mw4,mw5]),(11,10,1,mn518,[mw9,mw6,mw7,mw8,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS23p : mcS23.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS24 : List MemoKey := [(11,10,1,mn519,[mw6,mw7,mw2,mw8,mw3,mw10,mw4,mw5]),(11,10,1,mn520,[mw11,mw7,mw2,mw8,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS24p : mcS24.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS25 : List MemoKey := [(11,10,1,mn521,[mw11,mw6,mw7,mw2,mw8,mw3,mw4,mw5]),(11,10,1,mn522,[mw7,mw2,mw8,mw3,mw4,mw12,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS25p : mcS25.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS26 : List MemoKey := [(11,10,1,mn523,[mw6,mw7,mw2,mw8,mw3,mw4,mw12,mw5]),(11,10,1,mn524,[mw13,mw6,mw7,mw2,mw8,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS26p : mcS26.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS27 : List MemoKey := [(11,10,1,mn525,[mw7,mw2,mw8,mw3,mw4,mw5,mw14]),(11,10,1,mn526,[mw6,mw7,mw2,mw8,mw3,mw4,mw5,mw14])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS27p : mcS27.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS28 : List MemoKey := [(11,10,1,mn527,[mw15,mw6,mw7,mw2,mw8,mw3,mw4,mw5]),(11,10,1,mn528,[mw6,mw7,mw2,mw8,mw45,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS28p : mcS28.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS29 : List MemoKey := [(11,10,1,mn529,[mw6,mw7,mw2,mw8,mw3,mw46,mw4,mw5]),(11,10,1,mn530,[mw6,mw33,mw7,mw2,mw8,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS29p : mcS29.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS30 : List MemoKey := [(11,10,1,mn531,[mw6,mw7,mw2,mw8,mw3,mw4,mw34,mw5]),(11,10,1,mn532,[mw6,mw35,mw7,mw2,mw8,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS30p : mcS30.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS31 : List MemoKey := [(11,10,1,mn533,[mw6,mw7,mw2,mw8,mw3,mw4,mw5,mw47]),(11,10,1,mn534,[mw6,mw36,mw7,mw2,mw8,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS31p : mcS31.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS32 : List MemoKey := [(11,10,1,mn535,[mw6,mw7,mw2,mw8,mw3,mw16,mw4,mw5]),(11,10,1,mn536,[mw6,mw7,mw17,mw8,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS32p : mcS32.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS33 : List MemoKey := [(11,10,1,mn537,[mw6,mw7,mw2,mw8,mw3,mw4,mw5,mw18]),(11,10,1,mn538,[mw6,mw7,mw8,mw3,mw4,mw5,mw20])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS33p : mcS33.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS34 : List MemoKey := [(11,10,1,mn539,[mw6,mw7,mw2,mw8,mw3,mw4,mw5,mw20]),(11,10,1,mn540,[mw6,mw7,mw2,mw8,mw3,mw4,mw5,mw22])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS34p : mcS34.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS35 : List MemoKey := [(11,10,1,mn541,[mw6,mw7,mw2,mw8,mw23,mw3,mw4,mw5]),(11,10,1,mn542,[mw6,mw7,mw2,mw8,mw3,mw4,mw5,mw24])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS35p : mcS35.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS36 : List MemoKey := [(11,10,1,mn543,[mw6,mw7,mw2,mw8,mw25,mw3,mw4,mw5]),(11,10,1,mn544,[mw6,mw7,mw2,mw8,mw3,mw4,mw5,mw26])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS36p : mcS36.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS37 : List MemoKey := [(11,10,1,mn545,[mw6,mw7,mw2,mw8,mw3,mw27,mw4,mw5]),(11,10,1,mn562,[mw9,mw6,mw7,mw2,mw3,mw10,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS37p : mcS37.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS38 : List MemoKey := [(11,10,1,mn563,[mw9,mw6,mw7,mw2,mw3,mw4,mw12,mw5]),(11,10,1,mn564,[mw9,mw6,mw7,mw2,mw3,mw4,mw5,mw14])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS38p : mcS38.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS39 : List MemoKey := [(11,10,1,mn565,[mw9,mw6,mw7,mw2,mw3,mw46,mw4,mw5]),(11,10,1,mn566,[mw9,mw6,mw33,mw7,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS39p : mcS39.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS40 : List MemoKey := [(11,10,1,mn567,[mw9,mw6,mw7,mw2,mw3,mw4,mw34,mw5]),(11,10,1,mn568,[mw9,mw6,mw35,mw7,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS40p : mcS40.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS41 : List MemoKey := [(11,10,1,mn569,[mw9,mw6,mw7,mw2,mw3,mw4,mw5,mw47]),(11,10,1,mn570,[mw9,mw6,mw36,mw7,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS41p : mcS41.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS42 : List MemoKey := [(11,10,1,mn571,[mw9,mw6,mw7,mw2,mw3,mw4,mw5,mw22]),(11,10,1,mn572,[mw9,mw6,mw7,mw2,mw23,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS42p : mcS42.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS43 : List MemoKey := [(11,10,1,mn573,[mw9,mw6,mw7,mw2,mw3,mw4,mw5,mw24]),(11,10,1,mn574,[mw9,mw6,mw7,mw2,mw25,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS43p : mcS43.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS44 : List MemoKey := [(11,10,1,mn575,[mw9,mw6,mw7,mw2,mw3,mw4,mw5,mw26]),(11,10,1,mn576,[mw9,mw6,mw7,mw2,mw3,mw27,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS44p : mcS44.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS45 : List MemoKey := [(11,10,1,mn581,[mw11,mw7,mw2,mw10,mw4,mw5]),(11,10,1,mn582,[mw11,mw6,mw7,mw2,mw10,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS45p : mcS45.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS46 : List MemoKey := [(11,10,1,mn583,[mw11,mw7,mw2,mw3,mw10,mw4,mw5]),(11,10,1,mn584,[mw11,mw6,mw7,mw2,mw3,mw10,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS46p : mcS46.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS47 : List MemoKey := [(11,10,1,mn585,[mw6,mw7,mw2,mw3,mw10,mw4,mw12,mw5]),(11,10,1,mn586,[mw13,mw6,mw7,mw2,mw3,mw10,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS47p : mcS47.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS48 : List MemoKey := [(11,10,1,mn587,[mw6,mw7,mw2,mw3,mw10,mw4,mw5,mw14]),(11,10,1,mn588,[mw15,mw6,mw7,mw2,mw3,mw10,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS48p : mcS48.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS49 : List MemoKey := [(11,10,1,mn589,[mw6,mw7,mw2,mw45,mw3,mw10,mw4,mw5]),(11,10,1,mn590,[mw6,mw32,mw7,mw2,mw3,mw10,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS49p : mcS49.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS50 : List MemoKey := [(11,10,1,mn591,[mw6,mw33,mw7,mw2,mw3,mw10,mw4,mw5]),(11,10,1,mn592,[mw6,mw7,mw2,mw3,mw10,mw4,mw34,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS50p : mcS50.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS51 : List MemoKey := [(11,10,1,mn593,[mw6,mw35,mw7,mw2,mw3,mw10,mw4,mw5]),(11,10,1,mn594,[mw6,mw7,mw2,mw3,mw10,mw4,mw5,mw47])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS51p : mcS51.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS52 : List MemoKey := [(11,10,1,mn595,[mw6,mw36,mw7,mw2,mw3,mw10,mw4,mw5]),(11,10,1,mn596,[mw6,mw7,mw17,mw2,mw3,mw10,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS52p : mcS52.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS53 : List MemoKey := [(11,10,1,mn597,[mw6,mw7,mw2,mw3,mw10,mw4,mw5,mw18]),(11,10,1,mn598,[mw6,mw7,mw19,mw2,mw3,mw10,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS53p : mcS53.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS54 : List MemoKey := [(11,10,1,mn599,[mw6,mw7,mw2,mw3,mw10,mw4,mw5,mw20]),(11,10,1,mn600,[mw6,mw7,mw21,mw2,mw3,mw10,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS54p : mcS54.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS55 : List MemoKey := [(11,10,1,mn601,[mw6,mw7,mw2,mw23,mw3,mw10,mw4,mw5]),(11,10,1,mn602,[mw6,mw7,mw2,mw25,mw3,mw10,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS55p : mcS55.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS56 : List MemoKey := [(11,10,1,mn603,[mw6,mw7,mw2,mw3,mw10,mw4,mw5,mw26]),(11,10,1,mn604,[mw6,mw7,mw2,mw3,mw10,mw27,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS56p : mcS56.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS57 : List MemoKey := [(11,10,1,mn617,[mw11,mw7,mw2,mw3,mw4,mw12,mw5]),(11,10,1,mn618,[mw11,mw6,mw7,mw2,mw3,mw4,mw12,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS57p : mcS57.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS58 : List MemoKey := [(11,10,1,mn619,[mw11,mw6,mw7,mw2,mw3,mw4,mw5,mw14]),(11,10,1,mn620,[mw11,mw15,mw7,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS58p : mcS58.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS59 : List MemoKey := [(11,10,1,mn621,[mw11,mw6,mw7,mw2,mw45,mw3,mw4,mw5]),(11,10,1,mn622,[mw11,mw6,mw32,mw7,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS59p : mcS59.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS60 : List MemoKey := [(11,10,1,mn623,[mw11,mw6,mw7,mw2,mw3,mw46,mw4,mw5]),(11,10,1,mn624,[mw11,mw6,mw33,mw7,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS60p : mcS60.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS61 : List MemoKey := [(11,10,1,mn625,[mw11,mw6,mw7,mw2,mw3,mw4,mw34,mw5]),(11,10,1,mn626,[mw11,mw6,mw35,mw7,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS61p : mcS61.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS62 : List MemoKey := [(11,10,1,mn627,[mw11,mw6,mw7,mw2,mw3,mw4,mw5,mw47]),(11,10,1,mn628,[mw11,mw6,mw36,mw7,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS62p : mcS62.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS63 : List MemoKey := [(11,10,1,mn629,[mw11,mw6,mw7,mw2,mw3,mw16,mw4,mw5]),(11,10,1,mn630,[mw11,mw6,mw7,mw17,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS63p : mcS63.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS64 : List MemoKey := [(11,10,1,mn631,[mw11,mw6,mw7,mw2,mw3,mw4,mw5,mw18]),(11,10,1,mn632,[mw11,mw6,mw7,mw19,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS64p : mcS64.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS65 : List MemoKey := [(11,10,1,mn633,[mw11,mw6,mw7,mw2,mw3,mw4,mw5,mw20]),(11,10,1,mn634,[mw11,mw6,mw7,mw21,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS65p : mcS65.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS66 : List MemoKey := [(11,10,1,mn635,[mw11,mw6,mw7,mw2,mw3,mw4,mw5,mw22]),(11,10,1,mn636,[mw11,mw6,mw7,mw2,mw23,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS66p : mcS66.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS67 : List MemoKey := [(11,10,1,mn637,[mw11,mw6,mw7,mw2,mw3,mw4,mw5,mw24]),(11,10,1,mn638,[mw11,mw6,mw7,mw2,mw25,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS67p : mcS67.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS68 : List MemoKey := [(11,10,1,mn639,[mw11,mw6,mw7,mw2,mw3,mw4,mw5,mw26]),(11,10,1,mn640,[mw11,mw6,mw7,mw2,mw3,mw27,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS68p : mcS68.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS69 : List MemoKey := [(11,10,1,mn653,[mw13,mw7,mw2,mw3,mw12,mw5]),(11,10,1,mn654,[mw13,mw6,mw7,mw2,mw3,mw12,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS69p : mcS69.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS70 : List MemoKey := [(11,10,1,mn655,[mw7,mw2,mw3,mw4,mw12,mw5,mw14]),(11,10,1,mn656,[mw6,mw7,mw2,mw3,mw4,mw12,mw5,mw14])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS70p : mcS70.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS71 : List MemoKey := [(11,10,1,mn657,[mw15,mw6,mw7,mw2,mw3,mw4,mw12,mw5]),(11,10,1,mn658,[mw6,mw7,mw2,mw45,mw3,mw4,mw12,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS71p : mcS71.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS72 : List MemoKey := [(11,10,1,mn659,[mw6,mw32,mw7,mw2,mw3,mw4,mw12,mw5]),(11,10,1,mn660,[mw6,mw7,mw2,mw3,mw46,mw4,mw12,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS72p : mcS72.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS73 : List MemoKey := [(11,10,1,mn661,[mw6,mw33,mw7,mw2,mw3,mw4,mw12,mw5]),(11,10,1,mn662,[mw6,mw7,mw2,mw3,mw4,mw12,mw34,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS73p : mcS73.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS74 : List MemoKey := [(11,10,1,mn663,[mw6,mw7,mw2,mw3,mw4,mw12,mw5,mw47]),(11,10,1,mn664,[mw6,mw36,mw7,mw2,mw3,mw4,mw12,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS74p : mcS74.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS75 : List MemoKey := [(11,10,1,mn665,[mw6,mw7,mw2,mw3,mw16,mw4,mw12,mw5]),(11,10,1,mn666,[mw6,mw7,mw17,mw2,mw3,mw4,mw12,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS75p : mcS75.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS76 : List MemoKey := [(11,10,1,mn667,[mw6,mw7,mw2,mw3,mw4,mw12,mw5,mw18]),(11,10,1,mn668,[mw6,mw7,mw2,mw3,mw4,mw12,mw5,mw20])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS76p : mcS76.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS77 : List MemoKey := [(11,10,1,mn669,[mw6,mw7,mw21,mw2,mw3,mw4,mw12,mw5]),(11,10,1,mn670,[mw6,mw7,mw2,mw3,mw4,mw12,mw5,mw22])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS77p : mcS77.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS78 : List MemoKey := [(11,10,1,mn671,[mw6,mw7,mw2,mw3,mw4,mw12,mw5,mw24]),(11,10,1,mn672,[mw6,mw7,mw2,mw25,mw3,mw4,mw12,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS78p : mcS78.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS79 : List MemoKey := [(11,10,1,mn673,[mw6,mw7,mw2,mw3,mw4,mw12,mw5,mw26]),(11,10,1,mn690,[mw13,mw6,mw7,mw2,mw3,mw4,mw5,mw14])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS79p : mcS79.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS80 : List MemoKey := [(11,10,1,mn691,[mw13,mw6,mw7,mw2,mw45,mw3,mw4,mw5]),(11,10,1,mn692,[mw13,mw6,mw32,mw7,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS80p : mcS80.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS81 : List MemoKey := [(11,10,1,mn693,[mw13,mw6,mw7,mw2,mw3,mw46,mw4,mw5]),(11,10,1,mn694,[mw13,mw6,mw33,mw7,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS81p : mcS81.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS82 : List MemoKey := [(11,10,1,mn695,[mw13,mw6,mw7,mw2,mw3,mw4,mw5,mw47]),(11,10,1,mn696,[mw13,mw6,mw36,mw7,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS82p : mcS82.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS83 : List MemoKey := [(11,10,1,mn697,[mw13,mw6,mw7,mw2,mw3,mw16,mw4,mw5]),(11,10,1,mn698,[mw13,mw6,mw7,mw17,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS83p : mcS83.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS84 : List MemoKey := [(11,10,1,mn699,[mw13,mw6,mw7,mw2,mw3,mw4,mw5,mw20]),(11,10,1,mn700,[mw13,mw6,mw7,mw21,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS84p : mcS84.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS85 : List MemoKey := [(11,10,1,mn701,[mw13,mw6,mw7,mw2,mw3,mw4,mw5,mw24]),(11,10,1,mn702,[mw13,mw6,mw7,mw2,mw25,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS85p : mcS85.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS86 : List MemoKey := [(11,10,1,mn707,[mw15,mw7,mw2,mw3,mw4,mw14]),(11,10,1,mn708,[mw15,mw6,mw7,mw2,mw3,mw4,mw14])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS86p : mcS86.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS87 : List MemoKey := [(11,10,1,mn709,[mw15,mw7,mw2,mw3,mw4,mw5,mw14]),(11,10,1,mn710,[mw15,mw6,mw7,mw2,mw3,mw4,mw5,mw14])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS87p : mcS87.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS88 : List MemoKey := [(11,10,1,mn711,[mw6,mw7,mw2,mw45,mw3,mw4,mw5,mw14]),(11,10,1,mn712,[mw6,mw32,mw7,mw2,mw3,mw4,mw5,mw14])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS88p : mcS88.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS89 : List MemoKey := [(11,10,1,mn713,[mw6,mw7,mw2,mw3,mw46,mw4,mw5,mw14]),(11,10,1,mn714,[mw6,mw33,mw7,mw2,mw3,mw4,mw5,mw14])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS89p : mcS89.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS90 : List MemoKey := [(11,10,1,mn715,[mw6,mw7,mw2,mw3,mw4,mw34,mw5,mw14]),(11,10,1,mn716,[mw6,mw35,mw7,mw2,mw3,mw4,mw5,mw14])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS90p : mcS90.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS91 : List MemoKey := [(11,10,1,mn717,[mw6,mw7,mw2,mw3,mw4,mw5,mw14,mw47]),(11,10,1,mn718,[mw6,mw36,mw7,mw2,mw3,mw4,mw5,mw14])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS91p : mcS91.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS92 : List MemoKey := [(11,10,1,mn719,[mw6,mw7,mw2,mw3,mw16,mw4,mw5,mw14]),(11,10,1,mn720,[mw6,mw7,mw17,mw2,mw3,mw4,mw5,mw14])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS92p : mcS92.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS93 : List MemoKey := [(11,10,1,mn721,[mw6,mw7,mw2,mw3,mw4,mw5,mw14,mw18]),(11,10,1,mn722,[mw6,mw7,mw19,mw2,mw3,mw4,mw5,mw14])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS93p : mcS93.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS94 : List MemoKey := [(11,10,1,mn723,[mw6,mw7,mw2,mw3,mw4,mw5,mw14,mw20]),(11,10,1,mn724,[mw6,mw7,mw21,mw2,mw3,mw4,mw5,mw14])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS94p : mcS94.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS95 : List MemoKey := [(11,10,1,mn725,[mw6,mw7,mw2,mw3,mw4,mw5,mw14,mw22]),(11,10,1,mn726,[mw6,mw7,mw2,mw23,mw3,mw4,mw5,mw14])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS95p : mcS95.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS96 : List MemoKey := [(11,10,1,mn727,[mw6,mw7,mw2,mw3,mw4,mw5,mw14,mw24]),(11,10,1,mn728,[mw6,mw7,mw2,mw25,mw3,mw4,mw5,mw14])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS96p : mcS96.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS97 : List MemoKey := [(11,10,1,mn729,[mw6,mw7,mw2,mw3,mw4,mw5,mw14,mw26]),(11,10,1,mn730,[mw6,mw7,mw2,mw3,mw27,mw4,mw5,mw14])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS97p : mcS97.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS98 : List MemoKey := [(11,10,1,mn749,[mw15,mw6,mw7,mw2,mw45,mw3,mw4,mw5]),(11,10,1,mn750,[mw15,mw6,mw32,mw7,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS98p : mcS98.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS99 : List MemoKey := [(11,10,1,mn751,[mw15,mw6,mw7,mw2,mw3,mw46,mw4,mw5]),(11,10,1,mn752,[mw15,mw6,mw33,mw7,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS99p : mcS99.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS100 : List MemoKey := [(11,10,1,mn753,[mw15,mw6,mw7,mw2,mw3,mw4,mw34,mw5]),(11,10,1,mn754,[mw15,mw6,mw35,mw7,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS100p : mcS100.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS101 : List MemoKey := [(11,10,1,mn755,[mw15,mw6,mw7,mw2,mw3,mw4,mw5,mw47]),(11,10,1,mn756,[mw15,mw6,mw36,mw7,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS101p : mcS101.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS102 : List MemoKey := [(11,10,1,mn757,[mw15,mw6,mw7,mw2,mw3,mw16,mw4,mw5]),(11,10,1,mn758,[mw15,mw6,mw7,mw17,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS102p : mcS102.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS103 : List MemoKey := [(11,10,1,mn759,[mw15,mw6,mw7,mw2,mw3,mw4,mw5,mw18]),(11,10,1,mn760,[mw15,mw6,mw7,mw19,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS103p : mcS103.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS104 : List MemoKey := [(11,10,1,mn761,[mw15,mw6,mw7,mw2,mw3,mw4,mw5,mw20]),(11,10,1,mn762,[mw15,mw6,mw7,mw21,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS104p : mcS104.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS105 : List MemoKey := [(11,10,1,mn763,[mw15,mw6,mw7,mw2,mw3,mw4,mw5,mw22]),(11,10,1,mn764,[mw15,mw6,mw7,mw2,mw23,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS105p : mcS105.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS106 : List MemoKey := [(11,10,1,mn765,[mw15,mw6,mw7,mw2,mw3,mw4,mw5,mw24]),(11,10,1,mn766,[mw15,mw6,mw7,mw2,mw25,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS106p : mcS106.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS107 : List MemoKey := [(11,10,1,mn767,[mw15,mw6,mw7,mw2,mw3,mw4,mw5,mw26]),(11,10,1,mn768,[mw15,mw6,mw7,mw2,mw3,mw27,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS107p : mcS107.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS108 : List MemoKey := [(11,10,1,mn783,[mw6,mw32,mw45,mw3,mw4,mw5]),(11,10,1,mn784,[mw6,mw36,mw2,mw45,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS108p : mcS108.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS109 : List MemoKey := [(11,10,1,mn785,[mw6,mw7,mw2,mw45,mw3,mw16,mw4,mw5]),(11,10,1,mn786,[mw6,mw7,mw2,mw45,mw3,mw4,mw5,mw18])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS109p : mcS109.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS110 : List MemoKey := [(11,10,1,mn787,[mw6,mw7,mw2,mw45,mw3,mw4,mw5,mw20]),(11,10,1,mn788,[mw6,mw7,mw2,mw45,mw3,mw4,mw5,mw22])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS110p : mcS110.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS111 : List MemoKey := [(11,10,1,mn789,[mw6,mw7,mw2,mw45,mw23,mw3,mw4,mw5]),(11,10,1,mn790,[mw6,mw7,mw2,mw45,mw3,mw4,mw5,mw24])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS111p : mcS111.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS112 : List MemoKey := [(11,10,1,mn791,[mw6,mw7,mw2,mw45,mw25,mw3,mw4,mw5]),(11,10,1,mn792,[mw6,mw7,mw2,mw45,mw3,mw4,mw5,mw26])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS112p : mcS112.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS113 : List MemoKey := [(11,10,1,mn793,[mw6,mw7,mw2,mw45,mw3,mw27,mw4,mw5]),(11,10,1,mn798,[mw6,mw32,mw33,mw7,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS113p : mcS113.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS114 : List MemoKey := [(11,10,1,mn799,[mw6,mw32,mw35,mw7,mw2,mw3,mw4,mw5]),(11,10,1,mn800,[mw6,mw32,mw36,mw7,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS114p : mcS114.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS115 : List MemoKey := [(11,10,1,mn801,[mw6,mw32,mw7,mw2,mw3,mw4,mw5,mw22]),(11,10,1,mn802,[mw6,mw32,mw7,mw2,mw23,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS115p : mcS115.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS116 : List MemoKey := [(11,10,1,mn803,[mw6,mw32,mw7,mw2,mw3,mw4,mw5,mw24]),(11,10,1,mn804,[mw6,mw32,mw7,mw2,mw25,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS116p : mcS116.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS117 : List MemoKey := [(11,10,1,mn805,[mw6,mw32,mw7,mw2,mw3,mw4,mw5,mw26]),(11,10,1,mn806,[mw6,mw32,mw7,mw2,mw3,mw27,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS117p : mcS117.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS118 : List MemoKey := [(11,10,1,mn811,[mw6,mw33,mw2,mw46,mw4,mw5]),(11,10,1,mn812,[mw6,mw33,mw2,mw3,mw46,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS118p : mcS118.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS119 : List MemoKey := [(11,10,1,mn813,[mw6,mw7,mw17,mw2,mw3,mw46,mw4,mw5]),(11,10,1,mn814,[mw6,mw7,mw2,mw3,mw46,mw4,mw5,mw18])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS119p : mcS119.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS120 : List MemoKey := [(11,10,1,mn815,[mw6,mw7,mw19,mw2,mw3,mw46,mw4,mw5]),(11,10,1,mn816,[mw6,mw7,mw2,mw3,mw46,mw4,mw5,mw20])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS120p : mcS120.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS121 : List MemoKey := [(11,10,1,mn817,[mw6,mw7,mw21,mw2,mw3,mw46,mw4,mw5]),(11,10,1,mn818,[mw6,mw7,mw2,mw23,mw3,mw46,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS121p : mcS121.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS122 : List MemoKey := [(11,10,1,mn819,[mw6,mw7,mw2,mw25,mw3,mw46,mw4,mw5]),(11,10,1,mn820,[mw6,mw7,mw2,mw3,mw46,mw4,mw5,mw26])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS122p : mcS122.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS123 : List MemoKey := [(11,10,1,mn821,[mw6,mw7,mw2,mw3,mw46,mw27,mw4,mw5]),(11,10,1,mn828,[mw6,mw33,mw2,mw3,mw4,mw34,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS123p : mcS123.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS124 : List MemoKey := [(11,10,1,mn829,[mw6,mw33,mw35,mw7,mw2,mw3,mw4,mw5]),(11,10,1,mn830,[mw6,mw33,mw36,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS124p : mcS124.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS125 : List MemoKey := [(11,10,1,mn831,[mw6,mw33,mw36,mw7,mw2,mw3,mw4,mw5]),(11,10,1,mn832,[mw6,mw33,mw7,mw2,mw3,mw16,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS125p : mcS125.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS126 : List MemoKey := [(11,10,1,mn833,[mw6,mw33,mw7,mw17,mw2,mw3,mw4,mw5]),(11,10,1,mn834,[mw6,mw33,mw7,mw2,mw3,mw4,mw5,mw18])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS126p : mcS126.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS127 : List MemoKey := [(11,10,1,mn835,[mw6,mw33,mw7,mw19,mw2,mw3,mw4,mw5]),(11,10,1,mn836,[mw6,mw33,mw7,mw2,mw3,mw4,mw5,mw20])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS127p : mcS127.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS128 : List MemoKey := [(11,10,1,mn837,[mw6,mw33,mw7,mw21,mw2,mw3,mw4,mw5]),(11,10,1,mn838,[mw6,mw33,mw7,mw2,mw3,mw4,mw5,mw22])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS128p : mcS128.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS129 : List MemoKey := [(11,10,1,mn839,[mw6,mw33,mw7,mw2,mw23,mw3,mw4,mw5]),(11,10,1,mn840,[mw6,mw33,mw7,mw2,mw3,mw4,mw5,mw24])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS129p : mcS129.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS130 : List MemoKey := [(11,10,1,mn841,[mw6,mw33,mw7,mw2,mw25,mw3,mw4,mw5]),(11,10,1,mn842,[mw6,mw33,mw7,mw2,mw3,mw4,mw5,mw26])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS130p : mcS130.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS131 : List MemoKey := [(11,10,1,mn843,[mw6,mw33,mw7,mw2,mw3,mw27,mw4,mw5]),(11,10,1,mn860,[mw6,mw35,mw2,mw3,mw34,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS131p : mcS131.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS132 : List MemoKey := [(11,10,1,mn861,[mw6,mw7,mw2,mw3,mw16,mw4,mw34,mw5]),(11,10,1,mn862,[mw6,mw7,mw17,mw2,mw3,mw4,mw34,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS132p : mcS132.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS133 : List MemoKey := [(11,10,1,mn863,[mw6,mw7,mw2,mw3,mw4,mw34,mw5,mw18]),(11,10,1,mn864,[mw6,mw7,mw2,mw3,mw4,mw34,mw5,mw20])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS133p : mcS133.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS134 : List MemoKey := [(11,10,1,mn865,[mw6,mw7,mw21,mw2,mw3,mw4,mw34,mw5]),(11,10,1,mn866,[mw6,mw7,mw2,mw3,mw4,mw34,mw5,mw22])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS134p : mcS134.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS135 : List MemoKey := [(11,10,1,mn867,[mw6,mw7,mw2,mw3,mw4,mw34,mw5,mw24]),(11,10,1,mn868,[mw6,mw7,mw2,mw25,mw3,mw4,mw34,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS135p : mcS135.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS136 : List MemoKey := [(11,10,1,mn869,[mw6,mw7,mw2,mw3,mw4,mw34,mw5,mw26]),(11,10,1,mn874,[mw6,mw35,mw36,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS136p : mcS136.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS137 : List MemoKey := [(11,10,1,mn875,[mw6,mw35,mw36,mw7,mw2,mw3,mw4,mw5]),(11,10,1,mn876,[mw6,mw35,mw7,mw2,mw3,mw16,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS137p : mcS137.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS138 : List MemoKey := [(11,10,1,mn877,[mw6,mw35,mw7,mw17,mw2,mw3,mw4,mw5]),(11,10,1,mn878,[mw6,mw35,mw7,mw2,mw3,mw4,mw5,mw20])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS138p : mcS138.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS139 : List MemoKey := [(11,10,1,mn879,[mw6,mw35,mw7,mw21,mw2,mw3,mw4,mw5]),(11,10,1,mn880,[mw6,mw35,mw7,mw2,mw3,mw4,mw5,mw24])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS139p : mcS139.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS140 : List MemoKey := [(11,10,1,mn881,[mw6,mw35,mw7,mw2,mw25,mw3,mw4,mw5]),(11,10,1,mn886,[mw6,mw36,mw2,mw3,mw4,mw47])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS140p : mcS140.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS141 : List MemoKey := [(11,10,1,mn887,[mw6,mw36,mw2,mw3,mw4,mw5,mw47]),(11,10,1,mn888,[mw6,mw7,mw2,mw3,mw16,mw4,mw5,mw47])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS141p : mcS141.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS142 : List MemoKey := [(11,10,1,mn889,[mw6,mw7,mw17,mw2,mw3,mw4,mw5,mw47]),(11,10,1,mn890,[mw6,mw7,mw2,mw3,mw4,mw5,mw47,mw18])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS142p : mcS142.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS143 : List MemoKey := [(11,10,1,mn891,[mw6,mw7,mw19,mw2,mw3,mw4,mw5,mw47]),(11,10,1,mn892,[mw6,mw7,mw2,mw3,mw4,mw5,mw47,mw20])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS143p : mcS143.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS144 : List MemoKey := [(11,10,1,mn893,[mw6,mw7,mw21,mw2,mw3,mw4,mw5,mw47]),(11,10,1,mn894,[mw6,mw7,mw2,mw3,mw4,mw5,mw47,mw22])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS144p : mcS144.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS145 : List MemoKey := [(11,10,1,mn895,[mw6,mw7,mw2,mw23,mw3,mw4,mw5,mw47]),(11,10,1,mn896,[mw6,mw7,mw2,mw3,mw4,mw5,mw47,mw24])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS145p : mcS145.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS146 : List MemoKey := [(11,10,1,mn897,[mw6,mw7,mw2,mw25,mw3,mw4,mw5,mw47]),(11,10,1,mn898,[mw6,mw7,mw2,mw3,mw4,mw5,mw47,mw26])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS146p : mcS146.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS147 : List MemoKey := [(11,10,1,mn899,[mw6,mw7,mw2,mw3,mw27,mw4,mw5,mw47]),(11,10,1,mn904,[mw6,mw36,mw7,mw2,mw3,mw16,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS147p : mcS147.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS148 : List MemoKey := [(11,10,1,mn905,[mw6,mw36,mw7,mw17,mw2,mw3,mw4,mw5]),(11,10,1,mn906,[mw6,mw36,mw7,mw2,mw3,mw4,mw5,mw18])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS148p : mcS148.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS149 : List MemoKey := [(11,10,1,mn907,[mw6,mw36,mw7,mw19,mw2,mw3,mw4,mw5]),(11,10,1,mn908,[mw6,mw36,mw7,mw2,mw3,mw4,mw5,mw20])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS149p : mcS149.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS150 : List MemoKey := [(11,10,1,mn909,[mw6,mw36,mw7,mw21,mw2,mw3,mw4,mw5]),(11,10,1,mn910,[mw6,mw36,mw7,mw2,mw3,mw4,mw5,mw22])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS150p : mcS150.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS151 : List MemoKey := [(11,10,1,mn911,[mw6,mw36,mw7,mw2,mw23,mw3,mw4,mw5]),(11,10,1,mn912,[mw6,mw36,mw7,mw2,mw3,mw4,mw5,mw24])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS151p : mcS151.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS152 : List MemoKey := [(11,10,1,mn913,[mw6,mw36,mw7,mw2,mw25,mw3,mw4,mw5]),(11,10,1,mn914,[mw6,mw36,mw7,mw2,mw3,mw4,mw5,mw26])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS152p : mcS152.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS153 : List MemoKey := [(11,10,1,mn915,[mw6,mw36,mw7,mw2,mw3,mw27,mw4,mw5]),(11,10,1,mn932,[mw6,mw7,mw17,mw16,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS153p : mcS153.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS154 : List MemoKey := [(11,10,1,mn933,[mw6,mw7,mw17,mw3,mw16,mw4,mw5]),(11,10,1,mn934,[mw6,mw7,mw2,mw3,mw16,mw4,mw5,mw18])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS154p : mcS154.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS155 : List MemoKey := [(11,10,1,mn935,[mw6,mw7,mw2,mw3,mw16,mw4,mw5,mw20]),(11,10,1,mn936,[mw6,mw7,mw2,mw23,mw3,mw16,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS155p : mcS155.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS156 : List MemoKey := [(11,10,1,mn937,[mw6,mw7,mw2,mw25,mw3,mw16,mw4,mw5]),(11,10,1,mn938,[mw6,mw7,mw2,mw3,mw16,mw4,mw5,mw26])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS156p : mcS156.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS157 : List MemoKey := [(11,10,1,mn939,[mw6,mw7,mw2,mw3,mw16,mw27,mw4,mw5]),(11,10,1,mn952,[mw6,mw7,mw17,mw3,mw4,mw5,mw18])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS157p : mcS157.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS158 : List MemoKey := [(11,10,1,mn953,[mw6,mw7,mw17,mw2,mw3,mw4,mw5,mw22]),(11,10,1,mn954,[mw6,mw7,mw17,mw2,mw23,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS158p : mcS158.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS159 : List MemoKey := [(11,10,1,mn955,[mw6,mw7,mw17,mw2,mw3,mw4,mw5,mw24]),(11,10,1,mn956,[mw6,mw7,mw17,mw2,mw25,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS159p : mcS159.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS160 : List MemoKey := [(11,10,1,mn957,[mw6,mw7,mw17,mw2,mw3,mw4,mw5,mw26]),(11,10,1,mn958,[mw6,mw7,mw17,mw2,mw3,mw27,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS160p : mcS160.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS161 : List MemoKey := [(11,10,1,mn964,[mw6,mw7,mw19,mw3,mw5,mw18]),(11,10,1,mn965,[mw6,mw7,mw3,mw4,mw5,mw18,mw20])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS161p : mcS161.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS162 : List MemoKey := [(11,10,1,mn966,[mw6,mw7,mw2,mw3,mw4,mw5,mw18,mw20]),(11,10,1,mn967,[mw6,mw7,mw2,mw3,mw4,mw5,mw18,mw22])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS162p : mcS162.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS163 : List MemoKey := [(11,10,1,mn968,[mw6,mw7,mw2,mw3,mw4,mw5,mw18,mw24]),(11,10,1,mn969,[mw6,mw7,mw2,mw25,mw3,mw4,mw5,mw18])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS163p : mcS163.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS164 : List MemoKey := [(11,10,1,mn970,[mw6,mw7,mw2,mw3,mw4,mw5,mw18,mw26]),(11,10,1,mn987,[mw6,mw7,mw19,mw2,mw3,mw4,mw5,mw24])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS164p : mcS164.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS165 : List MemoKey := [(11,10,1,mn988,[mw6,mw7,mw19,mw2,mw25,mw3,mw4,mw5]),(11,10,1,mn995,[mw6,mw7,mw21,mw3,mw4,mw20])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS165p : mcS165.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS166 : List MemoKey := [(11,10,1,mn996,[mw6,mw7,mw21,mw3,mw4,mw5,mw20]),(11,10,1,mn997,[mw6,mw7,mw2,mw3,mw4,mw5,mw22,mw20])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS166p : mcS166.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS167 : List MemoKey := [(11,10,1,mn998,[mw6,mw7,mw2,mw23,mw3,mw4,mw5,mw20]),(11,10,1,mn999,[mw6,mw7,mw2,mw3,mw4,mw5,mw20,mw24])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS167p : mcS167.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS168 : List MemoKey := [(11,10,1,mn1000,[mw6,mw7,mw2,mw25,mw3,mw4,mw5,mw20]),(11,10,1,mn1001,[mw6,mw7,mw2,mw3,mw4,mw5,mw26,mw20])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS168p : mcS168.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS169 : List MemoKey := [(11,10,1,mn1002,[mw6,mw7,mw2,mw3,mw27,mw4,mw5,mw20]),(11,10,1,mn1019,[mw6,mw7,mw21,mw2,mw3,mw4,mw5,mw22])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS169p : mcS169.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS170 : List MemoKey := [(11,10,1,mn1020,[mw6,mw7,mw21,mw2,mw23,mw3,mw4,mw5]),(11,10,1,mn1021,[mw6,mw7,mw21,mw2,mw3,mw4,mw5,mw24])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS170p : mcS170.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS171 : List MemoKey := [(11,10,1,mn1022,[mw6,mw7,mw21,mw2,mw25,mw3,mw4,mw5]),(11,10,1,mn1023,[mw6,mw7,mw21,mw2,mw3,mw4,mw5,mw26])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS171p : mcS171.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS172 : List MemoKey := [(11,10,1,mn1024,[mw6,mw7,mw21,mw2,mw3,mw27,mw4,mw5]),(11,10,1,mn1030,[mw6,mw7,mw2,mw23,mw5,mw22])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS172p : mcS172.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS173 : List MemoKey := [(11,10,1,mn1031,[mw6,mw7,mw2,mw23,mw3,mw5,mw22]),(11,10,1,mn1032,[mw6,mw7,mw2,mw4,mw5,mw22,mw24])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS173p : mcS173.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS174 : List MemoKey := [(11,10,1,mn1033,[mw6,mw7,mw2,mw25,mw3,mw4,mw5,mw22]),(11,10,1,mn1034,[mw6,mw7,mw2,mw3,mw4,mw5,mw22,mw26])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS174p : mcS174.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS175 : List MemoKey := [(11,10,1,mn1047,[mw6,mw7,mw2,mw23,mw3,mw4,mw5,mw24]),(11,10,1,mn1048,[mw6,mw7,mw2,mw23,mw25,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS175p : mcS175.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS176 : List MemoKey := [(11,10,1,mn1053,[mw6,mw7,mw2,mw25,mw4,mw24]),(11,10,1,mn1054,[mw6,mw7,mw2,mw25,mw3,mw4,mw24])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS176p : mcS176.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS177 : List MemoKey := [(11,10,1,mn1055,[mw6,mw7,mw2,mw25,mw4,mw5,mw24]),(11,10,1,mn1056,[mw6,mw7,mw2,mw25,mw3,mw4,mw5,mw24])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS177p : mcS177.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS178 : List MemoKey := [(11,10,1,mn1057,[mw6,mw7,mw2,mw3,mw4,mw5,mw26,mw24]),(11,10,1,mn1058,[mw6,mw7,mw2,mw3,mw27,mw4,mw5,mw24])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS178p : mcS178.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS179 : List MemoKey := [(11,10,1,mn1079,[mw6,mw7,mw2,mw25,mw3,mw4,mw5,mw26]),(11,10,1,mn1080,[mw6,mw7,mw2,mw25,mw3,mw27,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS179p : mcS179.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS180 : List MemoKey := [(11,10,1,mn1097,[mw6,mw7,mw2,mw3,mw27,mw26]),(11,10,1,mn1098,[mw6,mw7,mw2,mw3,mw27,mw5,mw26])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS180p : mcS180.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def memoChunksS : List {xs : List MemoKey // xs.all (fun e => !(keyRun originalS e)) = true} := [⟨mcS0,mcS0p⟩,⟨mcS1,mcS1p⟩,⟨mcS2,mcS2p⟩,⟨mcS3,mcS3p⟩,⟨mcS4,mcS4p⟩,⟨mcS5,mcS5p⟩,⟨mcS6,mcS6p⟩,⟨mcS7,mcS7p⟩,⟨mcS8,mcS8p⟩,⟨mcS9,mcS9p⟩,⟨mcS10,mcS10p⟩,⟨mcS11,mcS11p⟩,⟨mcS12,mcS12p⟩,⟨mcS13,mcS13p⟩,⟨mcS14,mcS14p⟩,⟨mcS15,mcS15p⟩,⟨mcS16,mcS16p⟩,⟨mcS17,mcS17p⟩,⟨mcS18,mcS18p⟩,⟨mcS19,mcS19p⟩,⟨mcS20,mcS20p⟩,⟨mcS21,mcS21p⟩,⟨mcS22,mcS22p⟩,⟨mcS23,mcS23p⟩,⟨mcS24,mcS24p⟩,⟨mcS25,mcS25p⟩,⟨mcS26,mcS26p⟩,⟨mcS27,mcS27p⟩,⟨mcS28,mcS28p⟩,⟨mcS29,mcS29p⟩,⟨mcS30,mcS30p⟩,⟨mcS31,mcS31p⟩,⟨mcS32,mcS32p⟩,⟨mcS33,mcS33p⟩,⟨mcS34,mcS34p⟩,⟨mcS35,mcS35p⟩,⟨mcS36,mcS36p⟩,⟨mcS37,mcS37p⟩,⟨mcS38,mcS38p⟩,⟨mcS39,mcS39p⟩,⟨mcS40,mcS40p⟩,⟨mcS41,mcS41p⟩,⟨mcS42,mcS42p⟩,⟨mcS43,mcS43p⟩,⟨mcS44,mcS44p⟩,⟨mcS45,mcS45p⟩,⟨mcS46,mcS46p⟩,⟨mcS47,mcS47p⟩,⟨mcS48,mcS48p⟩,⟨mcS49,mcS49p⟩,⟨mcS50,mcS50p⟩,⟨mcS51,mcS51p⟩,⟨mcS52,mcS52p⟩,⟨mcS53,mcS53p⟩,⟨mcS54,mcS54p⟩,⟨mcS55,mcS55p⟩,⟨mcS56,mcS56p⟩,⟨mcS57,mcS57p⟩,⟨mcS58,mcS58p⟩,⟨mcS59,mcS59p⟩,⟨mcS60,mcS60p⟩,⟨mcS61,mcS61p⟩,⟨mcS62,mcS62p⟩,⟨mcS63,mcS63p⟩,⟨mcS64,mcS64p⟩,⟨mcS65,mcS65p⟩,⟨mcS66,mcS66p⟩,⟨mcS67,mcS67p⟩,⟨mcS68,mcS68p⟩,⟨mcS69,mcS69p⟩,⟨mcS70,mcS70p⟩,⟨mcS71,mcS71p⟩,⟨mcS72,mcS72p⟩,⟨mcS73,mcS73p⟩,⟨mcS74,mcS74p⟩,⟨mcS75,mcS75p⟩,⟨mcS76,mcS76p⟩,⟨mcS77,mcS77p⟩,⟨mcS78,mcS78p⟩,⟨mcS79,mcS79p⟩,⟨mcS80,mcS80p⟩,⟨mcS81,mcS81p⟩,⟨mcS82,mcS82p⟩,⟨mcS83,mcS83p⟩,⟨mcS84,mcS84p⟩,⟨mcS85,mcS85p⟩,⟨mcS86,mcS86p⟩,⟨mcS87,mcS87p⟩,⟨mcS88,mcS88p⟩,⟨mcS89,mcS89p⟩,⟨mcS90,mcS90p⟩,⟨mcS91,mcS91p⟩,⟨mcS92,mcS92p⟩,⟨mcS93,mcS93p⟩,⟨mcS94,mcS94p⟩,⟨mcS95,mcS95p⟩,⟨mcS96,mcS96p⟩,⟨mcS97,mcS97p⟩,⟨mcS98,mcS98p⟩,⟨mcS99,mcS99p⟩,⟨mcS100,mcS100p⟩,⟨mcS101,mcS101p⟩,⟨mcS102,mcS102p⟩,⟨mcS103,mcS103p⟩,⟨mcS104,mcS104p⟩,⟨mcS105,mcS105p⟩,⟨mcS106,mcS106p⟩,⟨mcS107,mcS107p⟩,⟨mcS108,mcS108p⟩,⟨mcS109,mcS109p⟩,⟨mcS110,mcS110p⟩,⟨mcS111,mcS111p⟩,⟨mcS112,mcS112p⟩,⟨mcS113,mcS113p⟩,⟨mcS114,mcS114p⟩,⟨mcS115,mcS115p⟩,⟨mcS116,mcS116p⟩,⟨mcS117,mcS117p⟩,⟨mcS118,mcS118p⟩,⟨mcS119,mcS119p⟩,⟨mcS120,mcS120p⟩,⟨mcS121,mcS121p⟩,⟨mcS122,mcS122p⟩,⟨mcS123,mcS123p⟩,⟨mcS124,mcS124p⟩,⟨mcS125,mcS125p⟩,⟨mcS126,mcS126p⟩,⟨mcS127,mcS127p⟩,⟨mcS128,mcS128p⟩,⟨mcS129,mcS129p⟩,⟨mcS130,mcS130p⟩,⟨mcS131,mcS131p⟩,⟨mcS132,mcS132p⟩,⟨mcS133,mcS133p⟩,⟨mcS134,mcS134p⟩,⟨mcS135,mcS135p⟩,⟨mcS136,mcS136p⟩,⟨mcS137,mcS137p⟩,⟨mcS138,mcS138p⟩,⟨mcS139,mcS139p⟩,⟨mcS140,mcS140p⟩,⟨mcS141,mcS141p⟩,⟨mcS142,mcS142p⟩,⟨mcS143,mcS143p⟩,⟨mcS144,mcS144p⟩,⟨mcS145,mcS145p⟩,⟨mcS146,mcS146p⟩,⟨mcS147,mcS147p⟩,⟨mcS148,mcS148p⟩,⟨mcS149,mcS149p⟩,⟨mcS150,mcS150p⟩,⟨mcS151,mcS151p⟩,⟨mcS152,mcS152p⟩,⟨mcS153,mcS153p⟩,⟨mcS154,mcS154p⟩,⟨mcS155,mcS155p⟩,⟨mcS156,mcS156p⟩,⟨mcS157,mcS157p⟩,⟨mcS158,mcS158p⟩,⟨mcS159,mcS159p⟩,⟨mcS160,mcS160p⟩,⟨mcS161,mcS161p⟩,⟨mcS162,mcS162p⟩,⟨mcS163,mcS163p⟩,⟨mcS164,mcS164p⟩,⟨mcS165,mcS165p⟩,⟨mcS166,mcS166p⟩,⟨mcS167,mcS167p⟩,⟨mcS168,mcS168p⟩,⟨mcS169,mcS169p⟩,⟨mcS170,mcS170p⟩,⟨mcS171,mcS171p⟩,⟨mcS172,mcS172p⟩,⟨mcS173,mcS173p⟩,⟨mcS174,mcS174p⟩,⟨mcS175,mcS175p⟩,⟨mcS176,mcS176p⟩,⟨mcS177,mcS177p⟩,⟨mcS178,mcS178p⟩,⟨mcS179,mcS179p⟩,⟨mcS180,mcS180p⟩]
def memoKeysS : List MemoKey := (memoChunksS.map Subtype.val).flatten
lemma memoKeysS_sound : ∀ e ∈ memoKeysS, keyRun originalS e = false := checkedChunks_sound (keyRun originalS) memoChunksS
end memo_data

noncomputable section memo_bridge
def memoTop (keysC keysS : List MemoKey) (NN AA HX HY l m g K H ph k t z : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) (tstC NN AA HX HY (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
    Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (mvC NN AA HX HY (memoLookC NN AA HX HY l m g keysC K) l m g k t z v y) (Nat.beq ph 1)) true
      (nodeC NN (memoLookS NN AA HX HY l m g K keysC keysS K (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) v.length z v (fun h xs => pairsC H h (fs xs))))) true (Nat.ble v.length 1)
def memoStart (keysC keysS : List MemoKey) (NN AA HX HY l m g B K t p H ph : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
    (child (fun z r => memoTop keysC keysS NN AA HX HY l m g K H ph K t z r) g (fun h => h v) (Nat.sub B (sumc v)))
    (Nat.ble v.length (Nat.sub (Nat.succ K) t))) (hasP p v)
def memoChk (keysC keysS : List MemoKey) (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ) : Bool :=
  (fun l => (fun m => (fun P => (fun g => (fun B => (fun p =>
    frc (avl P m (rawL E)) (fun v => st l fun l => st m fun m => st g fun g => st B fun B => st p fun p =>
      st I.NN fun nn => st I.AA fun aa => st I.HX fun hx => st I.HY fun hy =>
      anySubC nn (pos t) l v 0 (fun r => memoStart keysC keysS nn aa hx hy l m g B K t p H ph r)))
    (pwr E Z)) (pL (Q.map fun e => 16 + (K - e.2)))) (pL (Q.map fun _ => 16))) (PZ Q)) (mz Z)) (lz Z)
lemma memoTop_eq (keysC keysS : List MemoKey) (NN AA HX HY l m g K H ph k t z : Nat) (v : List W)
    (hC : ∀ e ∈ keysC, keyRun (lookC NN AA HX HY l m g) e = false)
    (hS : ∀ e ∈ keysS, keyRun (look1C NN AA HX HY l m g K) e = false) :
    memoTop keysC keysS NN AA HX HY l m g K H ph k t z v = topCC NN AA HX HY l m g K H ph k t z v := by
  unfold memoTop topCC
  rw [memoLookC_eq NN AA HX HY l m g keysC hC, memoLookS_eq NN AA HX HY l m g K keysC keysS hC hS]
lemma memoStart_eq (keysC keysS : List MemoKey) (NN AA HX HY l m g B K t p H ph : Nat) (v : List W)
    (hC : ∀ e ∈ keysC, keyRun (lookC NN AA HX HY l m g) e = false)
    (hS : ∀ e ∈ keysS, keyRun (look1C NN AA HX HY l m g K) e = false) :
    memoStart keysC keysS NN AA HX HY l m g B K t p H ph v = startvC NN AA HX HY l m g B K t p H ph v := by
  simp only [memoStart,startvC,memoTop_eq keysC keysS NN AA HX HY l m g K _ _ _ _ _ _ hC hS]
lemma memoChk_eq (H ph : Nat) :
    memoChk memoKeysC memoKeysS [] rt 0 12 1 H ph = chk [] rt 0 12 1 H ph := by
  unfold memoChk chk
  simp only [st_eq]
  simp only [memoStart_eq memoKeysC memoKeysS I.NN I.AA I.HX I.HY (lz 0) (mz 0)
    (pL (rt.map (fun _ => 16))) _ 12 _ _ _ _ _ memoKeysC_sound memoKeysS_sound]
end memo_bridge

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def root_p : pOk 0 rt = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def root_0 : chk [] rt 0 11 0 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def root_1 : chk [] rt 0 11 1 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def root_2 : chk [] rt 0 11 2 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def root_3 : chk [] rt 0 11 3 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def root_4 : chk [] rt 0 11 4 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def root_5 : chk [] rt 0 11 5 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def root_6 : chk [] rt 0 11 6 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def root_7 : chk [] rt 0 11 7 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def root_8 : chk [] rt 0 11 8 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def root_9 : chk [] rt 0 11 9 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def root_10 : chk [] rt 0 11 10 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def root_11 : chk [] rt 0 11 11 FF 1 = false := by decide +kernel
lemma iroot : Imp [] 0 12 := imp_ts (Or.inl rfl) root_p (by norm_num) ir (fun t ht => by
  interval_cases t
  · exact one root_0
  · exact one root_1
  · exact one root_2
  · exact one root_3
  · exact one root_4
  · exact one root_5
  · exact one root_6
  · exact one root_7
  · exact one root_8
  · exact one root_9
  · exact one root_10
  · exact one root_11)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_0 : chk [] rt 0 12 1 (0) 1 = false := (memoChk_eq (0) 1).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_1 : chk [] rt 0 12 1 (memoCell 4 0) 0 = false := (memoChk_eq (memoCell 4 0) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_2 : chk [] rt 0 12 1 (memoCell 4 4) 0 = false := (memoChk_eq (memoCell 4 4) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_3 : chk [] rt 0 12 1 (memoCell 4 8) 0 = false := (memoChk_eq (memoCell 4 8) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_4 : chk [] rt 0 12 1 (memoCell 4 12) 0 = false := (memoChk_eq (memoCell 4 12) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_5 : chk [] rt 0 12 1 (memoCell 4 16) 0 = false := (memoChk_eq (memoCell 4 16) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_6 : chk [] rt 0 12 1 (memoCell 4 20) 0 = false := (memoChk_eq (memoCell 4 20) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_7 : chk [] rt 0 12 1 (memoCell 4 24) 0 = false := (memoChk_eq (memoCell 4 24) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_8 : chk [] rt 0 12 1 (memoCell 4 28) 0 = false := (memoChk_eq (memoCell 4 28) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_9 : chk [] rt 0 12 1 (memoCell 4 32) 0 = false := (memoChk_eq (memoCell 4 32) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_10 : chk [] rt 0 12 1 (memoCell 4 36) 0 = false := (memoChk_eq (memoCell 4 36) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_11 : chk [] rt 0 12 1 (memoCell 4 40) 0 = false := (memoChk_eq (memoCell 4 40) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_12 : chk [] rt 0 12 1 (memoCell 4 44) 0 = false := (memoChk_eq (memoCell 4 44) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_13 : chk [] rt 0 12 1 (memoCell 4 48) 0 = false := (memoChk_eq (memoCell 4 48) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_14 : chk [] rt 0 12 1 (memoCell 4 52) 0 = false := (memoChk_eq (memoCell 4 52) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_15 : chk [] rt 0 12 1 (memoCell 4 56) 0 = false := (memoChk_eq (memoCell 4 56) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_16 : chk [] rt 0 12 1 (memoCell 4 60) 0 = false := (memoChk_eq (memoCell 4 60) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_17 : chk [] rt 0 12 1 (memoCell 4 64) 0 = false := (memoChk_eq (memoCell 4 64) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_18 : chk [] rt 0 12 1 (memoCell 4 68) 0 = false := (memoChk_eq (memoCell 4 68) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_19 : chk [] rt 0 12 1 (memoCell 4 72) 0 = false := (memoChk_eq (memoCell 4 72) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_20 : chk [] rt 0 12 1 (memoCell 4 76) 0 = false := (memoChk_eq (memoCell 4 76) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_21 : chk [] rt 0 12 1 (memoCell 4 80) 0 = false := (memoChk_eq (memoCell 4 80) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_22 : chk [] rt 0 12 1 (memoCell 4 84) 0 = false := (memoChk_eq (memoCell 4 84) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_23 : chk [] rt 0 12 1 (memoCell 4 88) 0 = false := (memoChk_eq (memoCell 4 88) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_24 : chk [] rt 0 12 1 (memoCell 4 92) 0 = false := (memoChk_eq (memoCell 4 92) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_25 : chk [] rt 0 12 1 (memoCell 4 96) 0 = false := (memoChk_eq (memoCell 4 96) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_26 : chk [] rt 0 12 1 (memoCell 4 100) 0 = false := (memoChk_eq (memoCell 4 100) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_27 : chk [] rt 0 12 1 (memoCell 4 104) 0 = false := (memoChk_eq (memoCell 4 104) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_28 : chk [] rt 0 12 1 (memoCell 4 108) 0 = false := (memoChk_eq (memoCell 4 108) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_29 : chk [] rt 0 12 1 (memoCell 4 112) 0 = false := (memoChk_eq (memoCell 4 112) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_30 : chk [] rt 0 12 1 (memoCell 4 116) 0 = false := (memoChk_eq (memoCell 4 116) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_31 : chk [] rt 0 12 1 (memoCell 4 120) 0 = false := (memoChk_eq (memoCell 4 120) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_32 : chk [] rt 0 12 1 (memoCell 4 124) 0 = false := (memoChk_eq (memoCell 4 124) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_33 : chk [] rt 0 12 1 (memoCell 4 128) 0 = false := (memoChk_eq (memoCell 4 128) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_34 : chk [] rt 0 12 1 (memoCell 4 132) 0 = false := (memoChk_eq (memoCell 4 132) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_35 : chk [] rt 0 12 1 (memoCell 4 136) 0 = false := (memoChk_eq (memoCell 4 136) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_36 : chk [] rt 0 12 1 (memoCell 4 140) 0 = false := (memoChk_eq (memoCell 4 140) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_37 : chk [] rt 0 12 1 (memoCell 4 144) 0 = false := (memoChk_eq (memoCell 4 144) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_38 : chk [] rt 0 12 1 (memoCell 4 148) 0 = false := (memoChk_eq (memoCell 4 148) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_39 : chk [] rt 0 12 1 (memoCell 4 152) 0 = false := (memoChk_eq (memoCell 4 152) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_40 : chk [] rt 0 12 1 (memoCell 4 156) 0 = false := (memoChk_eq (memoCell 4 156) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_41 : chk [] rt 0 12 1 (memoCell 4 160) 0 = false := (memoChk_eq (memoCell 4 160) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_42 : chk [] rt 0 12 1 (memoCell 4 164) 0 = false := (memoChk_eq (memoCell 4 164) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_43 : chk [] rt 0 12 1 (memoCell 4 168) 0 = false := (memoChk_eq (memoCell 4 168) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_44 : chk [] rt 0 12 1 (memoCell 4 172) 0 = false := (memoChk_eq (memoCell 4 172) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_45 : chk [] rt 0 12 1 (memoCell 4 176) 0 = false := (memoChk_eq (memoCell 4 176) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_46 : chk [] rt 0 12 1 (memoCell 4 180) 0 = false := (memoChk_eq (memoCell 4 180) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_47 : chk [] rt 0 12 1 (memoCell 4 184) 0 = false := (memoChk_eq (memoCell 4 184) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_48 : chk [] rt 0 12 1 (memoCell 4 188) 0 = false := (memoChk_eq (memoCell 4 188) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_49 : chk [] rt 0 12 1 (memoCell 4 192) 0 = false := (memoChk_eq (memoCell 4 192) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_50 : chk [] rt 0 12 1 (memoCell 4 196) 0 = false := (memoChk_eq (memoCell 4 196) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_51 : chk [] rt 0 12 1 (memoCell 4 200) 0 = false := (memoChk_eq (memoCell 4 200) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_52 : chk [] rt 0 12 1 (memoCell 4 204) 0 = false := (memoChk_eq (memoCell 4 204) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_53 : chk [] rt 0 12 1 (memoCell 4 208) 0 = false := (memoChk_eq (memoCell 4 208) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_54 : chk [] rt 0 12 1 (memoCell 4 212) 0 = false := (memoChk_eq (memoCell 4 212) 0).symm.trans (by decide +kernel)
def cacheR1Checked : List {p : ℕ × ℕ // chk [] rt 0 12 1 p.1 p.2 = false} := [⟨((0), 1), cacheR1Proof_0⟩, ⟨((memoCell 4 0), 0), cacheR1Proof_1⟩, ⟨((memoCell 4 4), 0), cacheR1Proof_2⟩, ⟨((memoCell 4 8), 0), cacheR1Proof_3⟩, ⟨((memoCell 4 12), 0), cacheR1Proof_4⟩, ⟨((memoCell 4 16), 0), cacheR1Proof_5⟩, ⟨((memoCell 4 20), 0), cacheR1Proof_6⟩, ⟨((memoCell 4 24), 0), cacheR1Proof_7⟩, ⟨((memoCell 4 28), 0), cacheR1Proof_8⟩, ⟨((memoCell 4 32), 0), cacheR1Proof_9⟩, ⟨((memoCell 4 36), 0), cacheR1Proof_10⟩, ⟨((memoCell 4 40), 0), cacheR1Proof_11⟩, ⟨((memoCell 4 44), 0), cacheR1Proof_12⟩, ⟨((memoCell 4 48), 0), cacheR1Proof_13⟩, ⟨((memoCell 4 52), 0), cacheR1Proof_14⟩, ⟨((memoCell 4 56), 0), cacheR1Proof_15⟩, ⟨((memoCell 4 60), 0), cacheR1Proof_16⟩, ⟨((memoCell 4 64), 0), cacheR1Proof_17⟩, ⟨((memoCell 4 68), 0), cacheR1Proof_18⟩, ⟨((memoCell 4 72), 0), cacheR1Proof_19⟩, ⟨((memoCell 4 76), 0), cacheR1Proof_20⟩, ⟨((memoCell 4 80), 0), cacheR1Proof_21⟩, ⟨((memoCell 4 84), 0), cacheR1Proof_22⟩, ⟨((memoCell 4 88), 0), cacheR1Proof_23⟩, ⟨((memoCell 4 92), 0), cacheR1Proof_24⟩, ⟨((memoCell 4 96), 0), cacheR1Proof_25⟩, ⟨((memoCell 4 100), 0), cacheR1Proof_26⟩, ⟨((memoCell 4 104), 0), cacheR1Proof_27⟩, ⟨((memoCell 4 108), 0), cacheR1Proof_28⟩, ⟨((memoCell 4 112), 0), cacheR1Proof_29⟩, ⟨((memoCell 4 116), 0), cacheR1Proof_30⟩, ⟨((memoCell 4 120), 0), cacheR1Proof_31⟩, ⟨((memoCell 4 124), 0), cacheR1Proof_32⟩, ⟨((memoCell 4 128), 0), cacheR1Proof_33⟩, ⟨((memoCell 4 132), 0), cacheR1Proof_34⟩, ⟨((memoCell 4 136), 0), cacheR1Proof_35⟩, ⟨((memoCell 4 140), 0), cacheR1Proof_36⟩, ⟨((memoCell 4 144), 0), cacheR1Proof_37⟩, ⟨((memoCell 4 148), 0), cacheR1Proof_38⟩, ⟨((memoCell 4 152), 0), cacheR1Proof_39⟩, ⟨((memoCell 4 156), 0), cacheR1Proof_40⟩, ⟨((memoCell 4 160), 0), cacheR1Proof_41⟩, ⟨((memoCell 4 164), 0), cacheR1Proof_42⟩, ⟨((memoCell 4 168), 0), cacheR1Proof_43⟩, ⟨((memoCell 4 172), 0), cacheR1Proof_44⟩, ⟨((memoCell 4 176), 0), cacheR1Proof_45⟩, ⟨((memoCell 4 180), 0), cacheR1Proof_46⟩, ⟨((memoCell 4 184), 0), cacheR1Proof_47⟩, ⟨((memoCell 4 188), 0), cacheR1Proof_48⟩, ⟨((memoCell 4 192), 0), cacheR1Proof_49⟩, ⟨((memoCell 4 196), 0), cacheR1Proof_50⟩, ⟨((memoCell 4 200), 0), cacheR1Proof_51⟩, ⟨((memoCell 4 204), 0), cacheR1Proof_52⟩, ⟨((memoCell 4 208), 0), cacheR1Proof_53⟩, ⟨((memoCell 4 212), 0), cacheR1Proof_54⟩]
def cacheR1Parts : List (ℕ × ℕ) := cacheR1Checked.map Subtype.val
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Full : mFull cacheR1Parts = true := by decide +kernel
def cacheR1One : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk [] rt 0 12 1 p.1 p.2 = false := by
  refine ⟨cacheR1Parts, cacheR1Full, ?_⟩
  intro p hp
  obtain ⟨q, _, rfl⟩ := List.mem_map.mp hp
  exact q.property
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_0 : chk [] rt 0 12 2 (0) 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_1 : chk [] rt 0 12 2 (memoCell 4 0) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_2 : chk [] rt 0 12 2 (memoCell 4 4) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_3 : chk [] rt 0 12 2 (memoCell 4 8) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_4 : chk [] rt 0 12 2 (memoCell 4 12) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_5 : chk [] rt 0 12 2 (memoCell 4 16) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_6 : chk [] rt 0 12 2 (memoCell 4 20) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_7 : chk [] rt 0 12 2 (memoCell 4 24) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_8 : chk [] rt 0 12 2 (memoCell 4 28) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_9 : chk [] rt 0 12 2 (memoCell 4 32) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_10 : chk [] rt 0 12 2 (memoCell 4 36) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_11 : chk [] rt 0 12 2 (memoCell 4 40) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_12 : chk [] rt 0 12 2 (memoCell 4 44) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_13 : chk [] rt 0 12 2 (memoCell 4 48) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_14 : chk [] rt 0 12 2 (memoCell 4 52) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_15 : chk [] rt 0 12 2 (memoCell 4 56) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_16 : chk [] rt 0 12 2 (memoCell 4 60) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_17 : chk [] rt 0 12 2 (memoCell 4 64) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_18 : chk [] rt 0 12 2 (memoCell 4 68) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_19 : chk [] rt 0 12 2 (memoCell 4 72) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_20 : chk [] rt 0 12 2 (memoCell 4 76) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_21 : chk [] rt 0 12 2 (memoCell 4 80) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_22 : chk [] rt 0 12 2 (memoCell 4 84) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_23 : chk [] rt 0 12 2 (memoCell 4 88) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_24 : chk [] rt 0 12 2 (memoCell 4 92) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_25 : chk [] rt 0 12 2 (memoCell 4 96) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_26 : chk [] rt 0 12 2 (memoCell 4 100) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_27 : chk [] rt 0 12 2 (memoCell 4 104) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_28 : chk [] rt 0 12 2 (memoCell 4 108) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_29 : chk [] rt 0 12 2 (memoCell 4 112) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_30 : chk [] rt 0 12 2 (memoCell 4 116) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_31 : chk [] rt 0 12 2 (memoCell 4 120) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_32 : chk [] rt 0 12 2 (memoCell 4 124) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_33 : chk [] rt 0 12 2 (memoCell 4 128) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_34 : chk [] rt 0 12 2 (memoCell 4 132) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_35 : chk [] rt 0 12 2 (memoCell 4 136) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_36 : chk [] rt 0 12 2 (memoCell 4 140) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_37 : chk [] rt 0 12 2 (memoCell 4 144) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_38 : chk [] rt 0 12 2 (memoCell 4 148) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_39 : chk [] rt 0 12 2 (memoCell 4 152) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_40 : chk [] rt 0 12 2 (memoCell 4 156) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_41 : chk [] rt 0 12 2 (memoCell 4 160) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_42 : chk [] rt 0 12 2 (memoCell 4 164) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_43 : chk [] rt 0 12 2 (memoCell 4 168) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_44 : chk [] rt 0 12 2 (memoCell 4 172) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_45 : chk [] rt 0 12 2 (memoCell 4 176) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_46 : chk [] rt 0 12 2 (memoCell 4 180) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_47 : chk [] rt 0 12 2 (memoCell 4 184) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_48 : chk [] rt 0 12 2 (memoCell 4 188) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_49 : chk [] rt 0 12 2 (memoCell 4 192) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_50 : chk [] rt 0 12 2 (memoCell 4 196) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_51 : chk [] rt 0 12 2 (memoCell 4 200) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_52 : chk [] rt 0 12 2 (memoCell 4 204) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_53 : chk [] rt 0 12 2 (memoCell 4 208) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_54 : chk [] rt 0 12 2 (memoCell 4 212) 0 = false := by decide +kernel
def cacheR2Checked : List {p : ℕ × ℕ // chk [] rt 0 12 2 p.1 p.2 = false} := [⟨((0), 1), cacheR2Proof_0⟩, ⟨((memoCell 4 0), 0), cacheR2Proof_1⟩, ⟨((memoCell 4 4), 0), cacheR2Proof_2⟩, ⟨((memoCell 4 8), 0), cacheR2Proof_3⟩, ⟨((memoCell 4 12), 0), cacheR2Proof_4⟩, ⟨((memoCell 4 16), 0), cacheR2Proof_5⟩, ⟨((memoCell 4 20), 0), cacheR2Proof_6⟩, ⟨((memoCell 4 24), 0), cacheR2Proof_7⟩, ⟨((memoCell 4 28), 0), cacheR2Proof_8⟩, ⟨((memoCell 4 32), 0), cacheR2Proof_9⟩, ⟨((memoCell 4 36), 0), cacheR2Proof_10⟩, ⟨((memoCell 4 40), 0), cacheR2Proof_11⟩, ⟨((memoCell 4 44), 0), cacheR2Proof_12⟩, ⟨((memoCell 4 48), 0), cacheR2Proof_13⟩, ⟨((memoCell 4 52), 0), cacheR2Proof_14⟩, ⟨((memoCell 4 56), 0), cacheR2Proof_15⟩, ⟨((memoCell 4 60), 0), cacheR2Proof_16⟩, ⟨((memoCell 4 64), 0), cacheR2Proof_17⟩, ⟨((memoCell 4 68), 0), cacheR2Proof_18⟩, ⟨((memoCell 4 72), 0), cacheR2Proof_19⟩, ⟨((memoCell 4 76), 0), cacheR2Proof_20⟩, ⟨((memoCell 4 80), 0), cacheR2Proof_21⟩, ⟨((memoCell 4 84), 0), cacheR2Proof_22⟩, ⟨((memoCell 4 88), 0), cacheR2Proof_23⟩, ⟨((memoCell 4 92), 0), cacheR2Proof_24⟩, ⟨((memoCell 4 96), 0), cacheR2Proof_25⟩, ⟨((memoCell 4 100), 0), cacheR2Proof_26⟩, ⟨((memoCell 4 104), 0), cacheR2Proof_27⟩, ⟨((memoCell 4 108), 0), cacheR2Proof_28⟩, ⟨((memoCell 4 112), 0), cacheR2Proof_29⟩, ⟨((memoCell 4 116), 0), cacheR2Proof_30⟩, ⟨((memoCell 4 120), 0), cacheR2Proof_31⟩, ⟨((memoCell 4 124), 0), cacheR2Proof_32⟩, ⟨((memoCell 4 128), 0), cacheR2Proof_33⟩, ⟨((memoCell 4 132), 0), cacheR2Proof_34⟩, ⟨((memoCell 4 136), 0), cacheR2Proof_35⟩, ⟨((memoCell 4 140), 0), cacheR2Proof_36⟩, ⟨((memoCell 4 144), 0), cacheR2Proof_37⟩, ⟨((memoCell 4 148), 0), cacheR2Proof_38⟩, ⟨((memoCell 4 152), 0), cacheR2Proof_39⟩, ⟨((memoCell 4 156), 0), cacheR2Proof_40⟩, ⟨((memoCell 4 160), 0), cacheR2Proof_41⟩, ⟨((memoCell 4 164), 0), cacheR2Proof_42⟩, ⟨((memoCell 4 168), 0), cacheR2Proof_43⟩, ⟨((memoCell 4 172), 0), cacheR2Proof_44⟩, ⟨((memoCell 4 176), 0), cacheR2Proof_45⟩, ⟨((memoCell 4 180), 0), cacheR2Proof_46⟩, ⟨((memoCell 4 184), 0), cacheR2Proof_47⟩, ⟨((memoCell 4 188), 0), cacheR2Proof_48⟩, ⟨((memoCell 4 192), 0), cacheR2Proof_49⟩, ⟨((memoCell 4 196), 0), cacheR2Proof_50⟩, ⟨((memoCell 4 200), 0), cacheR2Proof_51⟩, ⟨((memoCell 4 204), 0), cacheR2Proof_52⟩, ⟨((memoCell 4 208), 0), cacheR2Proof_53⟩, ⟨((memoCell 4 212), 0), cacheR2Proof_54⟩]
def cacheR2Parts : List (ℕ × ℕ) := cacheR2Checked.map Subtype.val
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Full : mFull cacheR2Parts = true := by decide +kernel
def cacheR2One : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk [] rt 0 12 2 p.1 p.2 = false := by
  refine ⟨cacheR2Parts, cacheR2Full, ?_⟩
  intro p hp
  obtain ⟨q, _, rfl⟩ := List.mem_map.mp hp
  exact q.property
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_0 : chk [] rt 0 12 3 (0) 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_1 : chk [] rt 0 12 3 (memoCell 7 0) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_2 : chk [] rt 0 12 3 (memoCell 7 7) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_3 : chk [] rt 0 12 3 (memoCell 7 14) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_4 : chk [] rt 0 12 3 (memoCell 7 21) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_5 : chk [] rt 0 12 3 (memoCell 7 28) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_6 : chk [] rt 0 12 3 (memoCell 7 35) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_7 : chk [] rt 0 12 3 (memoCell 7 42) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_8 : chk [] rt 0 12 3 (memoCell 7 49) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_9 : chk [] rt 0 12 3 (memoCell 7 56) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_10 : chk [] rt 0 12 3 (memoCell 7 63) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_11 : chk [] rt 0 12 3 (memoCell 7 70) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_12 : chk [] rt 0 12 3 (memoCell 7 77) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_13 : chk [] rt 0 12 3 (memoCell 7 84) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_14 : chk [] rt 0 12 3 (memoCell 7 91) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_15 : chk [] rt 0 12 3 (memoCell 7 98) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_16 : chk [] rt 0 12 3 (memoCell 7 105) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_17 : chk [] rt 0 12 3 (memoCell 7 112) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_18 : chk [] rt 0 12 3 (memoCell 7 119) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_19 : chk [] rt 0 12 3 (memoCell 7 126) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_20 : chk [] rt 0 12 3 (memoCell 7 133) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_21 : chk [] rt 0 12 3 (memoCell 7 140) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_22 : chk [] rt 0 12 3 (memoCell 7 147) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_23 : chk [] rt 0 12 3 (memoCell 7 154) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_24 : chk [] rt 0 12 3 (memoCell 7 161) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_25 : chk [] rt 0 12 3 (memoCell 7 168) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_26 : chk [] rt 0 12 3 (memoCell 7 175) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_27 : chk [] rt 0 12 3 (memoCell 7 182) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_28 : chk [] rt 0 12 3 (memoCell 7 189) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_29 : chk [] rt 0 12 3 (memoCell 7 196) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_30 : chk [] rt 0 12 3 (memoCell 7 203) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_31 : chk [] rt 0 12 3 (memoCell 7 210) 0 = false := by decide +kernel
def cacheR3Checked : List {p : ℕ × ℕ // chk [] rt 0 12 3 p.1 p.2 = false} := [⟨((0), 1), cacheR3Proof_0⟩, ⟨((memoCell 7 0), 0), cacheR3Proof_1⟩, ⟨((memoCell 7 7), 0), cacheR3Proof_2⟩, ⟨((memoCell 7 14), 0), cacheR3Proof_3⟩, ⟨((memoCell 7 21), 0), cacheR3Proof_4⟩, ⟨((memoCell 7 28), 0), cacheR3Proof_5⟩, ⟨((memoCell 7 35), 0), cacheR3Proof_6⟩, ⟨((memoCell 7 42), 0), cacheR3Proof_7⟩, ⟨((memoCell 7 49), 0), cacheR3Proof_8⟩, ⟨((memoCell 7 56), 0), cacheR3Proof_9⟩, ⟨((memoCell 7 63), 0), cacheR3Proof_10⟩, ⟨((memoCell 7 70), 0), cacheR3Proof_11⟩, ⟨((memoCell 7 77), 0), cacheR3Proof_12⟩, ⟨((memoCell 7 84), 0), cacheR3Proof_13⟩, ⟨((memoCell 7 91), 0), cacheR3Proof_14⟩, ⟨((memoCell 7 98), 0), cacheR3Proof_15⟩, ⟨((memoCell 7 105), 0), cacheR3Proof_16⟩, ⟨((memoCell 7 112), 0), cacheR3Proof_17⟩, ⟨((memoCell 7 119), 0), cacheR3Proof_18⟩, ⟨((memoCell 7 126), 0), cacheR3Proof_19⟩, ⟨((memoCell 7 133), 0), cacheR3Proof_20⟩, ⟨((memoCell 7 140), 0), cacheR3Proof_21⟩, ⟨((memoCell 7 147), 0), cacheR3Proof_22⟩, ⟨((memoCell 7 154), 0), cacheR3Proof_23⟩, ⟨((memoCell 7 161), 0), cacheR3Proof_24⟩, ⟨((memoCell 7 168), 0), cacheR3Proof_25⟩, ⟨((memoCell 7 175), 0), cacheR3Proof_26⟩, ⟨((memoCell 7 182), 0), cacheR3Proof_27⟩, ⟨((memoCell 7 189), 0), cacheR3Proof_28⟩, ⟨((memoCell 7 196), 0), cacheR3Proof_29⟩, ⟨((memoCell 7 203), 0), cacheR3Proof_30⟩, ⟨((memoCell 7 210), 0), cacheR3Proof_31⟩]
def cacheR3Parts : List (ℕ × ℕ) := cacheR3Checked.map Subtype.val
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Full : mFull cacheR3Parts = true := by decide +kernel
def cacheR3One : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk [] rt 0 12 3 p.1 p.2 = false := by
  refine ⟨cacheR3Parts, cacheR3Full, ?_⟩
  intro p hp
  obtain ⟨q, _, rfl⟩ := List.mem_map.mp hp
  exact q.property
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proot_4 : chk [] rt 0 12 4 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proot_5 : chk [] rt 0 12 5 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proot_6 : chk [] rt 0 12 6 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proot_7 : chk [] rt 0 12 7 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proot_8 : chk [] rt 0 12 8 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proot_9 : chk [] rt 0 12 9 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proot_10 : chk [] rt 0 12 10 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proot_11 : chk [] rt 0 12 11 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proot_12 : chk [] rt 0 12 12 FF 1 = false := by decide +kernel
lemma iroot_pos {t : ℕ} {S : Finset ℕ} (ht1 : 1 ≤ t) (hS : (S : Set ℕ) ⊆ C (mz 0) (WZ [] 0))
    (hl : Live Z0 (mz 0) (tz 0) 12 t S) : False := by
  have hmin : ∀ q < 12, ¬ Sol Z0 (mz 0) (tz 0) q (C (mz 0) (WZ [] 0)) := fun q hq => iroot q hq
  have hm0 : Min Z0 (mz 0) (tz 0) 12 t S := ⟨hl, fun q hq hs => hmin q hq (hs.mono le_rfl (by rintro x (hx | hx); exact hS hx; exact Or.inr hx))⟩
  have htk : t < 13 := by have := hm0.size.2; omega
  have hM : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk [] rt 0 12 t p.1 p.2 = false := by
    interval_cases t
    · exact cacheR1One
    · exact cacheR2One
    · exact cacheR3One
    · exact one proot_4
    · exact one proot_5
    · exact one proot_6
    · exact one proot_7
    · exact one proot_8
    · exact one proot_9
    · exact one proot_10
    · exact one proot_11
    · exact one proot_12
  exact imp_of_live (L := 13) (Or.inl rfl) root_p (by norm_num) ir (by omega) hS hl hmin (Or.inr hM)
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def f (x : Fin 6 → Bool) : Bool := (x 0 && x 2) || (x 0 && x 1 && x 3) || (x 1 && x 2 && x 4) || (x 0 && x 3 && x 4) || (x 0 && x 1 && x 5) || (x 0 && x 3 && x 5) || (x 1 && x 2 && x 3 && x 5) || (x 1 && x 3 && x 4 && x 5)
def EF : ℕ := (rawP0.getD 0 0 &&& rawP0.getD 2 0) ||| (rawP0.getD 0 0 &&& rawP0.getD 1 0 &&& rawP0.getD 3 0) ||| (rawP0.getD 1 0 &&& rawP0.getD 2 0 &&& rawP0.getD 4 0) ||| (rawP0.getD 0 0 &&& rawP0.getD 3 0 &&& rawP0.getD 4 0) ||| (rawP0.getD 0 0 &&& rawP0.getD 1 0 &&& rawP0.getD 5 0) ||| (rawP0.getD 0 0 &&& rawP0.getD 3 0 &&& rawP0.getD 5 0) ||| (rawP0.getD 1 0 &&& rawP0.getD 2 0 &&& rawP0.getD 3 0 &&& rawP0.getD 5 0) ||| (rawP0.getD 1 0 &&& rawP0.getD 3 0 &&& rawP0.getD 4 0 &&& rawP0.getD 5 0)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma EF_ok : EF &&& mz 0 = tz 0 := by decide +kernel
lemma rawP_len0 : rawP0.length = 6 := rfl
lemma row_list (b : ℕ) : List.ofFn (fun v : Fin 6 => (rawP0.getD v.val 0).testBit b) = rawP0.map (fun x => x.testBit b) := by
  apply List.ext_getElem
  · simp [rawP_len0]
  · intro i h1 h2
    have : i < rawP0.length := by simpa using h2
    rw [List.getElem_ofFn, List.getElem_map, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem this]; rfl
lemma f_bit (k : ℕ) : EF.testBit k = f (fun v : Fin 6 => (rawP0.getD v.val 0).testBit k) := by
  simp only [f, EF, Nat.testBit_or, Nat.testBit_and]
  rfl
theorem bridge (D : PEqualNP.CircuitLowerBounds.Circuit) (hD : PEqualNP.MetaComplexity.FanInTwo D)
    (hf : ∀ y : Fin 6 → Bool, D.eval (List.ofFn y) = f y) :
    Sol Z0 (mz 0) (tz 0) D.size (C (mz 0) (WZ [] 0)) := by
  obtain ⟨gates, out⟩ := D
  let row : ℕ → Fin 6 → Bool := fun k v => (rawP0.getD v.val 0).testBit k
  let init : List ℕ := rawP0.map (· &&& mz 0)
  have hinit_sub : ∀ x ∈ init, x &&& mz 0 = x := by
    intro x hx; simp only [init, List.mem_map] at hx; obtain ⟨w, _, rfl⟩ := hx; rw [Nat.and_assoc, Nat.and_self]
  have hinit_mem : ∀ x ∈ init, x ∈ C (mz 0) (WZ [] 0) := by
    intro x hx; simp only [init, List.mem_map] at hx; obtain ⟨w, hw, rfl⟩ := hx; exact Or.inl ⟨w, List.mem_append_left _ hw, rfl⟩
  have hinit_bits : ∀ k, (mz 0).testBit k = true → init.map (fun x => x.testBit k) = List.ofFn (row k) := by
    intro k hk; simp only [init, List.map_map, Function.comp_def, Nat.testBit_and, hk, Bool.and_true]; rw [row_list]
  have hout : (ex (mz 0) gates init).getD out 0 = tz 0 := by
    rw [← EF_ok]
    have hsub : ∀ x ∈ ex (mz 0) gates init, x &&& mz 0 = x := ex_sub (mz 0) hinit_sub
    have hsub' := getD_mem (S := {x | x &&& mz 0 = x}) hsub (by simp) out
    apply Nat.eq_of_testBit_eq; intro k
    have e1 := congrArg (fun x => x.testBit k) hsub'
    simp only [Nat.testBit_and] at e1; rw [← e1, Nat.testBit_and]
    cases hk : (mz 0).testBit k with
    | false => simp
    | true =>
      simp only [Bool.and_true]; rw [← getD_map, ex_bit (mz 0) hk gates init hD, hinit_bits k hk]
      have h := hf (row k)
      change (gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn (row k))).getD out false = f (row k) at h
      rw [h]; exact (f_bit k).symm
  exact ex_sol (mz 0) gates init (C (mz 0) (WZ [] 0)) hinit_mem (Or.inr (Set.mem_insert _ _)) (Or.inr (Set.mem_insert_of_mem _ rfl)) hD ⟨out, hout⟩
theorem bridge_not (gates : List Gate) (o : ℕ) (hD : FanInTwo ⟨gates, o⟩) (hnot : ∃ g ∈ gates, g.op = GateOp.not)
    (hf : ∀ y : Fin 6 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn y) = f y) :
    Sol Z0 (mz 0) (tz 0) (gates.length - 1) (C (mz 0) (WZ [] 0)) ∨
    ∃ t, 1 ≤ t ∧ ∃ S0 : Finset ℕ, (S0 : Set ℕ) ⊆ C (mz 0) (WZ [] 0) ∧ Live Z0 (mz 0) (tz 0) gates.length t S0 := by
  let row : ℕ → Fin 6 → Bool := fun k v => (rawP0.getD v.val 0).testBit k
  let init : List ℕ := rawP0.map (· &&& mz 0)
  have hinit_sub : ∀ x ∈ init, x &&& mz 0 = x := by intro x hx; simp only [init, List.mem_map] at hx; obtain ⟨w, _, rfl⟩ := hx; rw [Nat.and_assoc, Nat.and_self]
  have hinit_mem : ∀ x ∈ init, x ∈ C (mz 0) (WZ [] 0) := by intro x hx; simp only [init, List.mem_map] at hx; obtain ⟨w, hw, rfl⟩ := hx; exact Or.inl ⟨w, List.mem_append_left _ hw, rfl⟩
  have hinit_bits : ∀ k, (mz 0).testBit k = true → init.map (fun x => x.testBit k) = List.ofFn (row k) := by intro k hk; simp only [init, List.map_map, Function.comp_def, Nat.testBit_and, hk, Bool.and_true]; rw [row_list]
  have hout : (ex (mz 0) gates init).getD o 0 = tz 0 := by
    rw [← EF_ok]
    have hsub : ∀ x ∈ ex (mz 0) gates init, x &&& mz 0 = x := ex_sub (mz 0) hinit_sub
    have hsub' := getD_mem (S := {x | x &&& mz 0 = x}) hsub (by simp) o
    apply Nat.eq_of_testBit_eq; intro k
    have e1 := congrArg (fun x => x.testBit k) hsub'
    simp only [Nat.testBit_and] at e1; rw [← e1, Nat.testBit_and]
    cases hk : (mz 0).testBit k with
    | false => simp
    | true =>
      simp only [Bool.and_true]; rw [← getD_map, ex_bit (mz 0) hk gates init hD, hinit_bits k hk]
      have h := hf (row k)
      change (gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn (row k))).getD o false = f (row k) at h
      rw [h]; exact (f_bit k).symm
  exact ex_sol_not (mz 0) gates init (C (mz 0) (WZ [] 0)) hinit_mem (Or.inr (Set.mem_insert _ _)) (Or.inr (Set.mem_insert_of_mem _ rfl)) hD hnot ⟨o, hout⟩
def onWit : List Gate := [⟨.and, [3, 5]⟩, ⟨.and, [2, 6]⟩, ⟨.or, [2, 6]⟩, ⟨.and, [4, 3]⟩, ⟨.or, [4, 7]⟩, ⟨.or, [3, 5]⟩, ⟨.and, [8, 10]⟩, ⟨.and, [1, 11]⟩, ⟨.or, [9, 13]⟩, ⟨.and, [1, 12]⟩, ⟨.or, [8, 14]⟩, ⟨.and, [0, 16]⟩, ⟨.or, [15, 17]⟩]
theorem onWitBasis : ∀ g ∈ onWit,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [onWit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem onWitCorrect : ∀ x : Fin 6 → Bool, Circuit.eval ⟨onWit, 18⟩ (List.ofFn x) = f x := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem onTableCorrect : ∀ x : Fin 6 → Bool, f x = Nat.testBit (4008241832 * 2 ^ 32 + 3940591776) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by decide +kernel
end inst_data
end PEqualNP.Outside.L_meta_45698_aux

open PEqualNP.Outside.L_meta_45698_aux PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_45698 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008241832 * 2 ^ 32 + 3940591776) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008241832 * 2 ^ 32 + 3940591776) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  intro s hs
  obtain ⟨⟨gates, o⟩, hC, hsize, hcorrect⟩ := hs
  have hf : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = f x := fun x => (hcorrect x).trans (onTableCorrect x).symm
  by_cases hnot : ∃ g ∈ gates, g.op = GateOp.not
  · have hge : 13 ≤ gates.length := by
      by_contra hlt
      by_cases hsmall : gates.length < 12
      · exact iroot gates.length hsmall (bridge ⟨gates, o⟩ hC hf)
      · have heq : gates.length = 12 := by omega
        rcases bridge_not gates o hC hnot hf with hs | ⟨t, ht, S0, hS, hl⟩
        · exact iroot (gates.length - 1) (by omega) hs
        · rw [heq] at hl
          exact iroot_pos ht hS hl
    refine ⟨⟨onWit, 18⟩, ?_, ?_, fun x => (onWitCorrect x).trans (onTableCorrect x)⟩
    · intro g hg
      obtain ⟨ho, hl⟩ := onWitBasis g hg
      exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using ho, hl⟩
    · have hw : (⟨onWit, 18⟩ : Circuit).size = 13 := rfl
      change gates.length ≤ s at hsize
      omega
  · refine ⟨⟨gates, o⟩, ?_, hsize, hcorrect⟩
    intro g hg
    obtain ⟨ho, hl⟩ := hC g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ho ⊢
    refine ⟨?_, hl⟩
    rcases ho with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hnot ⟨g, hg, h⟩).elim
