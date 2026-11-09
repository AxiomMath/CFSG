module

public import Certificates.Kernel.PermCent.U43P1Tab
public import Certificates.Data.Kernel.PermCent.U43P1Chk
public import Certificates.Data.Kernel.PermCent.U43P1W
public import Certificates.Kernel.PermCent.U43P1A6
public import Certificates.Kernel.PermCent.U43P1Img
public import CFSG.Certificates.Kernel.Spor.PcompFacts
public import CFSG.Certificates.Kernel.Spor.PK.Basic

set_option maxRecDepth 400000
set_option maxHeartbeats 0

public section

namespace CertificateChecks.KernelPermCent.U43P1

open CFSG.ComponentClassification.HarrisLit.P1.U43.Cover CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def memCM1a (v : ℕ) : Bool :=
  (List.range 720).any fun j => Nat.beq (CgM1a.T j) v

@[expose] noncomputable def memCIa (v : ℕ) : Bool :=
  (List.range 720).any fun j => Nat.beq (CgIa.T j) v

@[expose] noncomputable def cfgM1aK (k : ℕ) : Bool :=
  commOK (pk (wM1a.getD k (0, false)).1 (wM1a.getD k (0, false)).2) (clsT 1 (clsR 1)) &&
    ((List.range (tM1a.getD k []).length).all fun j => commOK (tM1aG k j) (clsT 1 (clsR 1))) &&
    Nat.beq (cfgM1a.getD k []).length (cond (Nat.beq k 0) 16 32) &&
    cfgOK (tM1aT k) a6T a6N (!Nat.beq k 0) memCM1a (invL.map LM1a.T) (pk cDi false)
      (pk cDmi false) (cfgM1a.getD k [])

@[expose] noncomputable def cfgIaK (k : ℕ) : Bool :=
  commOK (pk (wIa.getD k (0, false)).1 (wIa.getD k (0, false)).2) (clsT 5 (clsR 5)) &&
    ((List.range (tIa.getD k []).length).all fun j => commOK (tIaG k j) (clsT 5 (clsR 5))) &&
    Nat.beq (cfgIa.getD k []).length (cond (Nat.beq k 0) 16 32) &&
    cfgOK (tIaT k) a6T a6N (!Nat.beq k 0) memCIa (invL.map LIa.T) (pk cDi false)
      (pk cDmi false) (cfgIa.getD k [])

@[expose] noncomputable def noneIa (u : ℕ) : Bool :=
  isId (pc u u) &&
    !(List.range 4536).any fun j => Nat.beq (CIa.T j) (pc u (pc (clsT 5 (clsR 5)) u))

@[expose] noncomputable def u43St (T l i : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight T (Nat.mul 10 (Nat.land (Nat.shiftRight l (Nat.mul 10 i)) 1023))) 1023

theorem u43_st_eq (T l i : ℕ) : u43St T l i = at10 T (at10 l i) := rfl

@[expose] noncomputable def u43P1 (p i : ℕ) : ℕ := Nat.land (Nat.shiftRight p (Nat.mul 10 i)) 1023

theorem u43_p1_eq (p i : ℕ) : u43P1 p i = at10 p i := rfl

@[expose] noncomputable def u43Inv (p : ℕ) : Bool :=
  allN 820 fun i => Nat.blt (u43P1 p i) 820 && Nat.beq (u43P1 p (u43P1 p i)) i

@[expose] def u43W2 (f : ℕ → ℕ) (i : ℕ) : Bool :=
  cond (Nat.ble (f i) i) true (Nat.beq (f (f i)) i)

@[expose] def u43W4 (f : ℕ → ℕ) (i : ℕ) : Bool :=
  cond (Nat.ble (f i) i) true (cond (Nat.ble (f (f i)) i) true
    (cond (Nat.blt (f (f (f i))) i) true (Nat.beq (f (f (f (f i)))) i)))

theorem u43_w2 (f : ℕ → ℕ) (hb : ∀ i < 820, f i < 820)
    (hj : ∀ a < 820, ∀ b < 820, f a = f b → a = b) (h : ∀ i < 820, u43W2 f i = true) :
    ∀ i < 820, f (f i) = i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
  intro hi
  have hw := h i hi
  have b1 := hb i hi
  have b2 := hb _ b1
  unfold u43W2 at hw
  cases c1 : Nat.ble (f i) i
  · rw [c1, Bool.cond_false, Nat.beq_eq] at hw
    exact hw
  · rcases Nat.lt_or_eq_of_le (Nat.ble_eq.mp c1) with c | c
    · exact hj _ b2 _ hi (ih _ c b1)
    · rw [c, c]

theorem u43_w4 (f : ℕ → ℕ) (hb : ∀ i < 820, f i < 820)
    (hj : ∀ a < 820, ∀ b < 820, f a = f b → a = b) (h : ∀ i < 820, u43W4 f i = true) :
    ∀ i < 820, f (f (f (f i))) = i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
  intro hi
  have hw := h i hi
  have b1 := hb i hi
  have b2 := hb _ b1
  have b3 := hb _ b2
  have b4 := hb _ b3
  unfold u43W4 at hw
  cases c1 : Nat.ble (f i) i
  · rw [c1, Bool.cond_false] at hw
    cases c2 : Nat.ble (f (f i)) i
    · rw [c2, Bool.cond_false] at hw
      cases c3 : Nat.blt (f (f (f i))) i
      · rw [c3, Bool.cond_false, Nat.beq_eq] at hw
        exact hw
      · have e := ih _ (Nat.blt_eq.mp c3) b3
        have e1 := hj _ (hb _ (hb _ b4)) _ b2 e
        have e2 := hj _ (hb _ b4) _ b1 e1
        exact hj _ b4 _ hi e2
    · rcases Nat.lt_or_eq_of_le (Nat.ble_eq.mp c2) with c | c
      · have e := ih _ c b2
        have e1 := hj _ (hb _ b4) _ b1 e
        exact hj _ b4 _ hi e1
      · rw [c, c]
  · rcases Nat.lt_or_eq_of_le (Nat.ble_eq.mp c1) with c | c
    · exact hj _ b4 _ hi (ih _ c b1)
    · rw [c, c, c, c]

@[expose] noncomputable def u43St4 (T l i : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight T (Nat.mul 10 (Nat.land (Nat.shiftRight l (Nat.mul 10
  (Nat.land (Nat.shiftRight T (Nat.mul 10 (Nat.land (Nat.shiftRight l (Nat.mul 10
  (Nat.land (Nat.shiftRight T (Nat.mul 10 (Nat.land (Nat.shiftRight l (Nat.mul 10
  (Nat.land (Nat.shiftRight T (Nat.mul 10 (Nat.land (Nat.shiftRight l (Nat.mul 10 i)) 1023))) 1023)
  )) 1023))) 1023)
  )) 1023))) 1023)
  )) 1023))) 1023

theorem u43_st4_eq (T l i : ℕ) :
    u43St4 T l i = u43St T l (u43St T l (u43St T l (u43St T l i))) := rfl

@[expose] noncomputable def u43Bnd (T : ℕ) : Bool :=
  (List.range 1024).all fun j => Nat.blt (at10 T j) 820

@[expose] noncomputable def u43NotOrd8 (T l : ℕ) : Bool :=
  ((List.range 820).all fun i => Nat.beq (u43St4 T l i) i) ||
    (List.range 820).any fun i => !Nat.beq (u43St4 T l (u43St4 T l i)) i

theorem u43_sq (p : ℕ) (f : ℕ → ℕ) (hf : ∀ i < 820, at10 p i = f i)
    (hr : ∀ i < 820, f i < 820) : ∀ i < 820, at10 (pc p p) i = f (f i) := by
  intro i hi
  have e := CFSG.KS.PF.pg_pcomp (n := 820) (w := 10) (p := p) (q := p) (by norm_num) hi
  simp only [at10, pc] at hf ⊢
  rw [e, hf i hi, hf _ (hr i hi)]

theorem u43_st (T l : ℕ) (hT : u43Bnd T = true) :
    (∀ i < 820, at10 (pc T l) i = u43St T l i) ∧ ∀ i < 820, u43St T l i < 820 := by
  refine ⟨fun i hi => ?_, fun i _ => ?_⟩
  · rw [u43_st_eq]
    simp only [at10, pc]
    exact CFSG.KS.PF.pg_pcomp (by norm_num) hi
  · rw [u43_st_eq]
    have hl : at10 l i < 1024 := CFSG.KS.PF.pg_lt 10 l i
    simp only [u43Bnd, List.all_eq_true, List.mem_range, Nat.blt_eq] at hT
    exact hT _ hl

theorem u43_inj (T l : ℕ) (hT : u43Inv T = true) (hl : u43Inv l = true) :
    ∀ a < 820, ∀ b < 820, u43St T l a = u43St T l b → a = b := by
  have hT' := PK.allN_iff.mp hT
  have hl' := PK.allN_iff.mp hl
  intro a ha b hb e
  rw [u43_st_eq, u43_st_eq] at e
  have la := hl' a ha
  have lb := hl' b hb
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, u43_p1_eq] at la lb
  have x := hT' _ la.1
  have y := hT' _ lb.1
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, u43_p1_eq] at x y
  have e1 : at10 l a = at10 l b := by rw [← x.2, ← y.2, e]
  rw [← la.2, ← lb.2, e1]

theorem u43_isId (p : ℕ) (f : ℕ → ℕ) (hf : ∀ i < 820, at10 p i = f i) :
    isId p = (List.range 820).all fun i => Nat.beq (f i) i := by
  unfold isId
  apply Bool.eq_iff_iff.mpr
  rw [List.all_eq_true, List.all_eq_true]
  refine forall₂_congr fun i hi => ?_
  rw [List.mem_range] at hi
  rw [hf i hi]

theorem u43_notOrd8 (T l : ℕ) (hT : u43Bnd T = true) (h : u43NotOrd8 T l = true) :
    notOrd8 (pc T l) = true := by
  obtain ⟨h1, r1⟩ := u43_st T l hT
  have h2 := u43_sq _ _ h1 r1
  have h4 := u43_sq _ _ h2 fun i hi => r1 _ (r1 i hi)
  have r4 : ∀ i < 820, u43St4 T l i < 820 := fun i hi => r1 _ (r1 _ (r1 _ (r1 i hi)))
  have h8 := u43_sq _ (u43St4 T l) h4 r4
  simp only [notOrd8, notOrd8F]
  rw [u43_isId _ _ h4, u43_isId _ _ h8]
  simp only [u43NotOrd8, Bool.or_eq_true, List.any_eq_true, List.all_eq_true, List.mem_range,
    Bool.not_eq_true', Nat.beq_eq] at h ⊢
  rcases h with h | ⟨i, hi, hne⟩
  · left
    intro i hi
    simpa [u43_st4_eq] using h i hi
  · right
    rw [Bool.eq_false_iff]
    intro hall
    rw [List.all_eq_true] at hall
    have := hall i (List.mem_range.mpr hi)
    simp only [u43_st4_eq] at hne this
    rw [this] at hne
    exact Bool.false_ne_true hne.symm

@[expose] noncomputable def u43Ex (T l v : ℕ) : Bool :=
  cond (Nat.blt v 8)
    (cond (Nat.beq v 1) (allN 820 fun i => Nat.beq (u43St T l i) i)
      (cond (Nat.beq v 2) (allN 820 fun i => u43W2 (u43St T l) i)
        (allN 820 fun i => u43W4 (u43St T l) i)))
    (Nat.blt (v - 8) 820 && !Nat.beq (u43St4 T l (u43St4 T l (v - 8))) (v - 8))

theorem u43_ex4 (T l v : ℕ) (hT : u43Bnd T = true) (hTi : u43Inv T = true)
    (hl : u43Inv l = true) (hv : v < 8) (h : u43Ex T l v = true) :
    ∀ i < 820, u43St4 T l i = i := by
  have hb := (u43_st T l hT).2
  have hj := u43_inj T l hTi hl
  unfold u43Ex at h
  have hb8 : Nat.blt v 8 = true := Nat.blt_eq.mpr hv
  rw [hb8, Bool.cond_true] at h
  intro i hi
  rw [u43_st4_eq]
  cases b1 : Nat.beq v 1
  · rw [b1, Bool.cond_false] at h
    cases b2 : Nat.beq v 2
    · rw [b2, Bool.cond_false] at h
      exact u43_w4 _ hb hj (PK.allN_iff.mp h) i hi
    · rw [b2, Bool.cond_true] at h
      have e := u43_w2 _ hb hj (PK.allN_iff.mp h)
      rw [e _ (hb _ (hb _ hi)), e _ hi]
  · rw [b1, Bool.cond_true] at h
    have e := PK.allN_iff.mp h
    simp only [Nat.beq_eq] at e
    rw [e _ hi, e _ hi, e _ hi, e _ hi]

theorem u43_ex (T l v : ℕ) (hT : u43Bnd T = true) (hTi : u43Inv T = true)
    (hl : u43Inv l = true) (h : u43Ex T l v = true) : u43NotOrd8 T l = true := by
  unfold u43NotOrd8
  rw [Bool.or_eq_true]
  cases hb : Nat.blt v 8
  · right
    unfold u43Ex at h
    rw [hb] at h
    simp only [Bool.cond_false, Bool.and_eq_true, Nat.blt_eq] at h
    rw [List.any_eq_true]
    exact ⟨v - 8, List.mem_range.mpr h.1, h.2⟩
  · left
    have f4 := u43_ex4 T l v hT hTi hl (Nat.blt_eq.mp hb) h
    rw [List.all_eq_true]
    intro i hi
    rw [List.mem_range] at hi
    rw [Nat.beq_eq]
    exact f4 i hi

theorem u43_inv4 (f g : ℕ → ℕ) (hg : ∀ i < 820, g i < 820) (h : ∀ i < 820, f (g i) = i)
    (hf : ∀ i < 820, f (f (f (f i))) = i) : ∀ i < 820, g (g (g (g i))) = i := by
  intro i hi
  have b1 := hg i hi
  have b2 := hg _ b1
  have b3 := hg _ b2
  have e := hf _ (hg _ b3)
  rw [h _ b3, h _ b2, h _ b1, h _ hi] at e
  exact e.symm

@[expose] noncomputable def u43Ex2 (T : ℕ) (Ls vs : List ℕ) (l v : ℕ) : Bool :=
  cond (Nat.blt v 1000) (u43Ex T l v)
    (Nat.blt (v - 1000) Ls.length && Nat.blt (vs.getD (v - 1000) 4) 8 &&
      allN 820 fun i => Nat.beq (u43St T (Ls.getD (v - 1000) 0) (u43St T l i)) i)

@[expose] noncomputable def u43AllEx (T : ℕ) (Ls vs : List ℕ) : Bool :=
  allN Ls.length fun j => u43Ex2 T Ls vs (Ls.getD j 0) (vs.getD j 4)

theorem u43_allEx (T : ℕ) (hT : u43Bnd T = true) (hTi : u43Inv T = true) (Ls vs : List ℕ)
    (hL : ∀ l ∈ Ls, u43Inv l = true)
    (h : u43AllEx T Ls vs = true) : ∀ l ∈ Ls, u43NotOrd8 T l = true := by
  have hj := PK.allN_iff.mp h
  intro l hl
  have hli := hL l hl
  obtain ⟨j, hj', rfl⟩ := List.getElem_of_mem hl
  have e := hj j hj'
  rw [List.getD_eq_getElem _ _ hj'] at e
  unfold u43Ex2 at e
  generalize vs.getD j 4 = v at e
  cases hb : Nat.blt v 1000
  · rw [hb, Bool.cond_false] at e
    simp only [Bool.and_eq_true, Nat.blt_eq, PK.allN_iff, Nat.beq_eq] at e
    obtain ⟨⟨ha, hc⟩, hinv⟩ := e
    have ea := hj _ ha
    have hc' : Nat.blt (vs.getD (v - 1000) 4) 1000 = true := Nat.blt_eq.mpr (by omega)
    unfold u43Ex2 at ea
    rw [hc', Bool.cond_true] at ea
    have hai : u43Inv (Ls.getD (v - 1000) 0) = true := by
      rw [List.getD_eq_getElem _ _ ha]
      exact hL _ (List.getElem_mem ha)
    have f4 := u43_ex4 _ _ _ hT hTi hai hc ea
    unfold u43NotOrd8
    rw [Bool.or_eq_true, List.all_eq_true]
    left
    intro i hi
    rw [List.mem_range] at hi
    rw [Nat.beq_eq, u43_st4_eq]
    exact u43_inv4 _ _ (u43_st T _ hT).2 hinv
      (fun i hi => (u43_st4_eq _ _ _).symm.trans (f4 i hi)) i hi
  · rw [hb, Bool.cond_true] at e
    exact u43_ex T _ _ hT hTi hli e

@[expose] def u43VM1a : List (List (List ℕ)) := [
  [[], [2, 8, 4, 4, 8, 8, 4, 2, 4, 1006, 4, 1008, 4, 1012, 1010, 2, 8, 8, 8, 8, 8, 8, 8, 2, 2, 8, 8,
    1003, 8, 2, 2, 8, 8, 8, 8, 1002, 8, 8, 8, 8, 2, 8, 2, 8, 8], [], [1, 8, 4, 4, 8, 8, 8, 4, 8, 8,
    8, 8, 8, 8, 8, 4, 8, 8, 8, 8, 8, 8, 8, 1007, 2, 8, 8, 1003, 8, 1015, 2, 8, 8, 8, 8, 1002, 8, 8,
    8, 8, 2, 8, 2, 8, 8], [4, 8, 2, 8, 8, 8, 4, 8, 8, 8, 8, 4, 4, 8, 4, 8, 2, 2, 4, 2, 8, 1011, 8,
    8, 1000, 8, 8, 8, 8, 8, 8, 1006, 2, 2, 1018, 2, 1012, 1014, 8, 2, 8, 8, 2, 8, 8], [2, 4, 2, 2,
    8, 4, 8, 4, 8, 8, 8, 8, 8, 8, 8, 4, 8, 4, 4, 8, 8, 8, 8, 1007, 2, 8, 8, 2, 8, 1015, 2, 8, 8, 8,
    1018, 2, 8, 8, 8, 1017, 2, 8, 2, 1001, 1005], [4, 8, 2, 8, 4, 8, 8, 8, 4, 4, 4, 8, 8, 1004, 8,
    8, 8, 4, 2, 8, 2, 8, 1009, 8, 1000, 1010, 2, 8, 2, 8, 8, 8, 8, 8, 2, 2, 8, 8, 2, 1017, 8, 1008,
    2, 8, 8], [2, 8, 2, 4, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 4, 4, 8, 8, 8, 8, 8, 2, 8, 8,
    1003, 8, 8, 4, 8, 8, 8, 1018, 2, 8, 8, 8, 1017, 1030, 8, 1, 8, 8], [4, 8, 1, 8, 8, 8, 8, 8, 8,
    8, 8, 8, 8, 8, 8, 8, 4, 2, 4, 1016, 8, 8, 8, 8, 1000, 8, 8, 8, 8, 8, 8, 8, 4, 1032, 1018, 2, 8,
    8, 8, 2, 8, 8, 2, 8, 8], [4, 8, 2, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 4, 2, 8, 4, 8, 8,
    8, 1000, 8, 4, 8, 1020, 8, 8, 8, 8, 8, 2, 1, 8, 8, 1026, 1017, 8, 8, 2, 8, 8], [], [2, 2, 4, 2,
    4, 2, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 4, 1021, 8, 2, 4, 8, 2, 8, 8, 4, 4, 8, 8, 8,
    1002, 1025, 1004, 8, 8, 1030, 1031, 2, 2, 2], [], [], [2, 4, 4, 2, 8, 4, 8, 8, 8, 8, 8, 8, 8, 8,
    8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 1, 8, 8, 2, 8, 8, 4, 8, 8, 8, 8, 1002, 8, 8, 8, 8, 1030, 8, 2,
    1001, 1005], [2, 8, 2, 4, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 4, 2, 2, 1016, 4, 8, 8, 8, 2, 8,
    4, 1003, 1020, 8, 4, 8, 4, 1032, 2, 2, 8, 8, 1026, 2, 1030, 8, 2, 8, 8]],
  [],
  [[], [], [8, 2, 8, 4, 4, 8, 2, 4, 2, 4, 8, 1007, 8, 8, 8, 1009, 2, 4, 4, 1017, 1018, 8, 8, 8,
    1003, 8, 8, 2, 2, 8, 8, 2, 8, 8, 8, 8, 8, 1004, 8, 8, 8, 2, 8, 2, 8], [], [], [], [], [2, 2, 2,
    2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2, 2, 2, 2, 2], [8, 2, 4, 8, 8, 8, 2, 8, 4, 2, 8, 8, 4, 8, 8, 2, 2, 2, 8, 2, 8,
    8, 4, 8, 8, 8, 1022, 4, 1008, 4, 8, 2, 8, 8, 8, 8, 1012, 8, 8, 1002, 1029, 2, 8, 1027, 8], [],
    [4, 8, 2, 8, 8, 8, 4, 8, 8, 8, 8, 4, 4, 8, 4, 8, 2, 2, 4, 2, 8, 1011, 8, 8, 1000, 8, 8, 8, 8, 8,
    8, 1006, 2, 2, 1018, 2, 1012, 1014, 8, 2, 8, 8, 2, 8, 8], [8, 8, 4, 8, 8, 8, 4, 8, 8, 8, 8, 8,
    2, 4, 8, 8, 2, 2, 8, 2, 8, 8, 8, 1013, 8, 4, 8, 8, 8, 8, 8, 1006, 8, 8, 8, 8, 2, 8, 8, 1002, 8,
    8, 8, 8, 1025], [8, 8, 4, 4, 4, 1003, 4, 4, 8, 8, 4, 8, 2, 2, 8, 8, 2, 2, 8, 2, 1010, 8, 8, 2,
    8, 2, 8, 8, 8, 8, 1007, 1006, 8, 8, 8, 8, 2, 8, 1004, 1002, 8, 8, 8, 8, 2], [], [8, 8, 2, 8, 8,
    8, 4, 8, 8, 8, 8, 8, 4, 8, 8, 8, 2, 2, 8, 2, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 1006, 4, 1032, 8,
    4, 1012, 8, 8, 2, 8, 8, 1035, 8, 8], [], [4, 4, 8, 8, 8, 4, 2, 8, 8, 2, 4, 8, 8, 8, 1010, 2, 2,
    4, 8, 1017, 8, 1005, 2, 8, 8, 8, 2, 8, 8, 2, 1000, 2, 8, 8, 4, 8, 8, 8, 1034, 8, 2, 1001, 8, 8,
    8], [], [], [], [], [], [], [], [8, 4, 8, 8, 8, 8, 2, 8, 8, 2, 8, 8, 8, 8, 8, 2, 2, 4, 8, 1017,
    8, 8, 4, 8, 8, 8, 1022, 8, 8, 4, 8, 2, 8, 8, 8, 8, 8, 8, 8, 8, 1029, 1001, 8, 8, 8], [8, 2, 8,
    8, 8, 8, 2, 8, 4, 4, 8, 8, 8, 8, 8, 1009, 2, 4, 8, 1017, 8, 8, 8, 8, 8, 8, 8, 4, 1008, 8, 8, 2,
    8, 8, 8, 8, 8, 8, 8, 8, 8, 2, 8, 1027, 8], [8, 4, 4, 8, 8, 8, 2, 8, 8, 4, 8, 8, 4, 8, 8, 1009,
    2, 2, 8, 2, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 2, 8, 8, 8, 8, 1012, 8, 8, 1002, 8, 1001, 8, 8, 8],
    [8, 4, 2, 8, 8, 8, 2, 8, 8, 4, 8, 8, 2, 4, 8, 1009, 2, 2, 8, 2, 8, 8, 8, 1013, 8, 4, 8, 8, 8, 8,
    8, 2, 4, 1032, 8, 4, 2, 8, 8, 2, 8, 1001, 1035, 8, 1025], [], [], [], []],
  [],
  [[], [], [2, 2, 4, 2, 4, 2, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 4, 1021, 8, 2, 4, 8, 2,
    8, 8, 4, 4, 8, 8, 8, 1002, 1025, 1004, 8, 8, 1030, 1031, 2, 2, 2], [], [], [], [], [4, 2, 8, 2,
    2, 4, 4, 8, 4, 8, 8, 8, 8, 4, 4, 8, 1006, 8, 8, 8, 8, 8, 8, 8, 2, 8, 8, 2, 1008, 8, 8, 2, 1014,
    8, 8, 8, 8, 2, 1013, 8, 8, 2, 1000, 2, 1005], [], [], [8, 2, 4, 8, 8, 8, 2, 8, 4, 2, 8, 8, 4, 8,
    8, 2, 2, 2, 8, 2, 8, 8, 4, 8, 8, 8, 1022, 4, 1008, 4, 8, 2, 8, 8, 8, 8, 1012, 8, 8, 1002, 1029,
    2, 8, 1027, 8], [8, 2, 8, 4, 2, 8, 8, 8, 8, 8, 8, 8, 8, 4, 4, 8, 8, 8, 8, 8, 8, 8, 8, 8, 1003,
    8, 8, 2, 8, 8, 8, 4, 1014, 8, 8, 8, 8, 2, 1013, 8, 8, 1031, 8, 2, 8], [8, 2, 8, 8, 8, 8, 4, 2,
    2, 8, 4, 2, 8, 8, 8, 8, 1006, 8, 2, 8, 2, 4, 8, 4, 8, 1010, 8, 4, 2, 8, 1023, 2, 8, 1021, 4,
    1034, 8, 8, 8, 8, 8, 2, 8, 1027, 8], [], [], [8, 2, 8, 4, 2, 8, 8, 8, 8, 8, 4, 8, 4, 2, 2, 8, 8,
    8, 8, 8, 8, 8, 8, 1012, 1003, 8, 4, 2, 8, 1010, 8, 4, 2, 4, 1026, 8, 8, 2, 2, 1033, 8, 1031, 8,
    2, 8], [], [], [], [], [], [8, 2, 8, 4, 4, 8, 4, 8, 4, 8, 8, 8, 8, 8, 8, 8, 1006, 8, 8, 8, 8, 8,
    8, 8, 1003, 8, 8, 2, 1008, 8, 8, 2, 8, 8, 8, 8, 8, 1004, 8, 8, 8, 2, 8, 2, 8], [], [8, 2, 8, 8,
    8, 8, 2, 8, 4, 4, 8, 8, 8, 8, 8, 1009, 2, 4, 8, 1017, 8, 8, 8, 8, 8, 8, 8, 4, 1008, 8, 8, 2, 8,
    8, 8, 8, 8, 8, 8, 8, 8, 2, 8, 1027, 8], [8, 2, 8, 8, 8, 8, 4, 4, 2, 8, 8, 1007, 8, 8, 8, 8,
    1006, 8, 4, 8, 1018, 8, 8, 8, 8, 8, 8, 4, 2, 8, 8, 2, 8, 8, 8, 8, 8, 8, 8, 8, 8, 2, 8, 1027, 8],
    [8, 2, 8, 4, 4, 8, 2, 4, 2, 4, 8, 1007, 8, 8, 8, 1009, 2, 4, 4, 1017, 1018, 8, 8, 8, 1003, 8, 8,
    2, 2, 8, 8, 2, 8, 8, 8, 8, 8, 1004, 8, 8, 8, 2, 8, 2, 8], [], [4, 2, 8, 2, 4, 4, 8, 8, 8, 8, 8,
    8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 2, 8, 8, 2, 8, 8, 8, 4, 8, 8, 8, 8, 8, 1004, 8, 8, 8,
    1031, 1000, 2, 1005], [], [], [], [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]],
  []]

@[expose] def u43VIa : List (List (List ℕ)) := [
  [[], [], [8, 8, 8, 8, 8, 8, 8, 8, 4, 8, 2, 8, 8, 8, 4, 8, 8, 8, 2, 8, 1, 8, 8, 8, 8, 2, 8, 8, 2,
    1014, 8, 8, 8, 8, 4, 1034, 4, 8, 8, 8, 8, 1008, 8, 8, 1036], [], [], [], [], [8, 8, 8, 2, 8, 2,
    8, 8, 8, 8, 4, 8, 4, 8, 8, 8, 9, 8, 8, 1012, 1010, 4, 1021, 9, 4, 2, 8, 1024, 8, 8, 8, 8, 8, 8,
    8, 8, 2, 8, 8, 8, 8, 8, 8, 8, 1], [8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 1, 8, 8, 8, 2, 4, 8, 8, 4, 8,
    2, 8, 8, 8, 8, 2, 8, 8, 1018, 2, 8, 8, 4, 8, 8, 8, 4, 1032, 8, 8, 1015, 8, 8, 8, 1036], [8, 8,
    8, 4, 8, 1003, 8, 8, 8, 8, 4, 8, 2, 4, 8, 8, 4, 1016, 8, 2, 1010, 8, 8, 1013, 8, 2, 8, 8, 8, 8,
    8, 8, 8, 8, 8, 8, 1, 8, 8, 8, 8, 8, 8, 8, 2], [8, 8, 8, 4, 8, 1003, 8, 8, 8, 8, 2, 8, 4, 8, 4,
    8, 8, 8, 4, 1012, 2, 8, 8, 8, 8, 1, 8, 8, 1018, 1014, 8, 8, 8, 8, 8, 8, 2, 8, 8, 8, 8, 8, 8, 8,
    2], [], [], [], [], []],
  [[], [], [4, 8, 8, 8, 4, 8, 4, 8, 8, 1006, 2, 8, 8, 8, 2, 2, 8, 8, 4, 8, 2, 8, 8, 8, 8, 2, 8, 8,
    1018, 2, 1000, 8, 2, 4, 8, 8, 4, 2, 8, 1033, 2, 8, 8, 1004, 1036], [8, 8, 8, 4, 8, 1003, 8, 8,
    4, 8, 2, 8, 4, 8, 2, 4, 9, 8, 2, 1012, 2, 8, 8, 9, 8, 2, 9, 8, 2, 2, 8, 8, 4, 9, 4, 1034, 2,
    1032, 8, 8, 1015, 1008, 9, 9, 2], [], [], [], [], [], [], [], [4, 4, 8, 2, 8, 2, 8, 8, 8, 4, 4,
    4, 4, 8, 8, 8, 8, 8, 8, 1012, 1010, 2, 2, 8, 2, 2, 1009, 2, 8, 8, 8, 8, 8, 1011, 8, 8, 2, 8, 8,
    8, 8, 8, 1000, 1001, 2], [], [], [], [8, 8, 4, 4, 4, 1003, 4, 4, 8, 8, 4, 8, 2, 2, 8, 8, 2, 2,
    8, 2, 1010, 8, 8, 2, 8, 2, 8, 8, 8, 8, 1007, 1006, 8, 8, 8, 8, 2, 8, 1004, 1002, 8, 8, 8, 8, 2],
    [], [], [], [], [], [], [], [], [], [], [], [], [], [], [8, 4, 4, 8, 8, 8, 8, 4, 2, 8, 2, 1007,
    8, 8, 4, 8, 8, 8, 2, 8, 2, 8, 8, 8, 8, 2, 4, 8, 2, 1014, 8, 1001, 8, 8, 2, 2, 4, 8, 1026, 8, 8,
    2, 1002, 8, 1036], [8, 8, 8, 2, 8, 2, 8, 8, 8, 8, 2, 8, 2, 4, 4, 8, 4, 1016, 4, 2, 2, 4, 1021,
    1013, 4, 2, 8, 1024, 1018, 1014, 8, 8, 8, 8, 8, 8, 2, 8, 8, 8, 8, 8, 8, 8, 2]],
  [],
  []]

@[expose] noncomputable def u43CfgOK (T : ℕ → ℕ) (cls : ℕ → ℕ → ℕ) (sz : ℕ → ℕ) (inner : Bool)
    (mem : ℕ → Bool) (Ls : List ℕ) (d dI : ℕ) (W : List ℕ) (V : List (List ℕ)) : Bool :=
  (W.zipIdx).all fun x =>
    cond (Nat.beq x.1 0) (!invol (T x.2))
      (cond (Nat.beq x.1 1) (inner && mem (T x.2))
        (cond (Nat.beq x.1 2) (u43Bnd (T x.2) && u43Inv (T x.2) &&
            u43AllEx (T x.2) Ls (V.getD x.2 []))
          (cond (Nat.blt ((x.1 - 3) / 65536) 2)
            (inCls cls sz [0, 1] ((x.1 - 3) / 65536) ((x.1 - 3) % 65536) (T x.2))
            (inCls cls sz [0, 1] ((x.1 - 3) / 65536 - 2) ((x.1 - 3) % 65536)
              (pc dI (pc (T x.2) d))))))

theorem u43_cfgOK (T : ℕ → ℕ) (cls : ℕ → ℕ → ℕ) (sz : ℕ → ℕ) (inner : Bool) (mem : ℕ → Bool)
    (Ls : List ℕ) (d dI : ℕ) (W : List ℕ) (V : List (List ℕ)) (hL : ∀ l ∈ Ls, u43Inv l = true)
    (h : u43CfgOK T cls sz inner mem Ls d dI W V = true) :
    cfgOK T cls sz inner mem Ls d dI W = true := by
  simp only [u43CfgOK, cfgOK, List.all_eq_true] at h ⊢
  intro x hx
  have hx' := h x hx
  generalize Nat.beq x.1 0 = b0 at hx' ⊢
  generalize Nat.beq x.1 1 = b1 at hx' ⊢
  generalize Nat.beq x.1 2 = b2 at hx' ⊢
  cases b0 <;> cases b1 <;> cases b2 <;> simp only [Bool.cond_true, Bool.cond_false] at hx' ⊢ <;>
    first
    | exact hx'
    | simp only [Bool.and_eq_true] at hx'
      rw [List.all_eq_true]
      exact fun l hl => u43_notOrd8 _ _ hx'.1.1 (u43_allEx _ hx'.1.1 hx'.1.2 _ _ hL hx'.2 l hl)

@[expose] noncomputable def u43CfgM1aK (k : ℕ) : Bool :=
  commOK (pk (wM1a.getD k (0, false)).1 (wM1a.getD k (0, false)).2) (clsT 1 (clsR 1)) &&
    ((List.range (tM1a.getD k []).length).all fun j => commOK (tM1aG k j) (clsT 1 (clsR 1))) &&
    Nat.beq (cfgM1a.getD k []).length (cond (Nat.beq k 0) 16 32) &&
    u43CfgOK (tM1aT k) a6T a6N (!Nat.beq k 0) memCM1a (invL.map LM1a.T) (pk cDi false)
      (pk cDmi false) (cfgM1a.getD k []) (u43VM1a.getD k [])

@[expose] noncomputable def u43CfgIaK (k : ℕ) : Bool :=
  commOK (pk (wIa.getD k (0, false)).1 (wIa.getD k (0, false)).2) (clsT 5 (clsR 5)) &&
    ((List.range (tIa.getD k []).length).all fun j => commOK (tIaG k j) (clsT 5 (clsR 5))) &&
    Nat.beq (cfgIa.getD k []).length (cond (Nat.beq k 0) 16 32) &&
    u43CfgOK (tIaT k) a6T a6N (!Nat.beq k 0) memCIa (invL.map LIa.T) (pk cDi false)
      (pk cDmi false) (cfgIa.getD k []) (u43VIa.getD k [])

theorem u43_invM1a : (invL.map LM1a.T).all u43Inv = true := by
  decide +kernel

theorem u43_invIa : (invL.map LIa.T).all u43Inv = true := by
  decide +kernel

theorem u43_cfgM1aK (k : ℕ) (h : u43CfgM1aK k = true) : cfgM1aK k = true := by
  simp only [u43CfgM1aK, cfgM1aK, Bool.and_eq_true] at h ⊢
  exact ⟨h.1, u43_cfgOK _ _ _ _ _ _ _ _ _ _ (List.all_eq_true.mp u43_invM1a) h.2⟩

theorem u43_cfgIaK (k : ℕ) (h : u43CfgIaK k = true) : cfgIaK k = true := by
  simp only [u43CfgIaK, cfgIaK, Bool.and_eq_true] at h ⊢
  exact ⟨h.1, u43_cfgOK _ _ _ _ _ _ _ _ _ _ (List.all_eq_true.mp u43_invIa) h.2⟩

theorem u43_and {a b : Bool} (ha : a = true) (hb : b = true) : (a && b) = true := by
  rw [ha, hb]
  rfl

theorem u43_andL {a b : Bool} (h : (a && b) = true) : a = true := by
  revert h
  cases a <;> cases b <;> decide

theorem u43_andR {a b : Bool} (h : (a && b) = true) : b = true := by
  revert h
  cases a <;> cases b <;> decide

theorem cfgM1a_lo : (cfgM1aK 0 && cfgM1aK 1 && cfgM1aK 2) = true := by
  have h : (u43CfgM1aK 0 && u43CfgM1aK 1 && u43CfgM1aK 2) = true := by
    simp only [u43CfgM1aK, u43_pk]
    decide +kernel
  exact u43_and (u43_and (u43_cfgM1aK 0 (u43_andL (u43_andL h)))
    (u43_cfgM1aK 1 (u43_andR (u43_andL h)))) (u43_cfgM1aK 2 (u43_andR h))

theorem cfgM1a_hi : (cfgM1aK 3 && cfgM1aK 4 && cfgM1aK 5) = true := by
  have h : (u43CfgM1aK 3 && u43CfgM1aK 4 && u43CfgM1aK 5) = true := by
    simp only [u43CfgM1aK, u43_pk]
    decide +kernel
  exact u43_and (u43_and (u43_cfgM1aK 3 (u43_andL (u43_andL h)))
    (u43_cfgM1aK 4 (u43_andR (u43_andL h)))) (u43_cfgM1aK 5 (u43_andR h))

theorem cfgIa_all : (cfgIaK 0 && cfgIaK 1 && cfgIaK 2 && cfgIaK 3 && noneIa (pk cI true) &&
    noneIa (pk cM1 true)) = true := by
  have h : (u43CfgIaK 0 && u43CfgIaK 1 && u43CfgIaK 2 && u43CfgIaK 3 && noneIa (pk cI true) &&
      noneIa (pk cM1 true)) = true := by
    simp only [u43CfgIaK, u43_pk]
    decide +kernel
  have h4 := u43_andL (u43_andL h)
  exact u43_and (u43_and (u43_and (u43_and (u43_and
    (u43_cfgIaK 0 (u43_andL (u43_andL (u43_andL h4))))
    (u43_cfgIaK 1 (u43_andR (u43_andL (u43_andL h4)))))
    (u43_cfgIaK 2 (u43_andR (u43_andL h4)))) (u43_cfgIaK 3 (u43_andR h4)))
    (u43_andR (u43_andL h))) (u43_andR h)

end CertificateChecks.KernelPermCent.U43P1

end
