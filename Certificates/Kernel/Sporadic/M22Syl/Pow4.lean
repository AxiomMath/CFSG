module

public import Certificates.Kernel.Sporadic.M22Syl.Checks
public import CFSG.Certificates.Kernel.Spor.PK.Basic
public import CFSG.Certificates.Kernel.Spor.PK.Enc
public import CFSG.Certificates.Kernel.Spor.PK.Perm.Comp
public import Certificates.Data.Kernel.Spor.PCountW
public import Certificates.Data.Kernel.Spor.MSylow

public section

namespace CertificateChecks.KernelSpor.M22Syl

open CFSG.KC.Enum CFSG.KS CFSG.KS.PK CFSG.KS.PCnt CFSG.KS.MSyl CFSG.Sporadic.Schreier

set_option maxRecDepth 100000

theorem p4_fd_pcomp (p q j : Nat) :
    fd 5 (pcomp 22 5 (mask 5) p q) j = if j < 22 then fd 5 p (fd 5 q j) else 0 := by
  by_cases hj : j < 22
  · rw [if_pos hj]
    exact CFSG.KS.PK.fd_pcomp (by norm_num) 5 p q hj
  · rw [if_neg hj]
    have hlt := CFSG.KS.PK.pcomp_lt (n := 22) (by norm_num) 5 p q
    unfold fd
    rw [Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num) (by omega))),
      Nat.zero_mod]

theorem p4_fd_I : ∀ i < 22, fd 5 I i = i := by decide +kernel

theorem p4_II : pcomp 22 5 (mask 5) I I = I := Nat.eq_of_beq_eq_true (by decide +kernel)

theorem p4_fixes {x : Nat} (h : x = I) {i : Nat} (hi : i < 22) : fd 5 x i = i := by
  rw [h, p4_fd_I i hi]

@[expose] noncomputable def p4sq (y j : Nat) : Nat :=
  nIf(Nat.blt j 22, pg 5 (mask 5) y (pg 5 (mask 5) y j), nat_lit 0)

theorem p4sq_eq (y j : Nat) : p4sq y j = fd 5 (pcomp 22 5 (mask 5) y y) j := by
  rw [p4_fd_pcomp]
  unfold p4sq
  by_cases hj : j < 22
  · rw [if_pos hj, show Nat.blt j 22 = true from Nat.blt_eq.mpr hj]
    show pg 5 (mask 5) y (pg 5 (mask 5) y j) = _
    simp only [CFSG.KS.PK.pg_eq]
    try rfl
  · rw [if_neg hj, show Nat.blt j 22 = false from
      Bool.eq_false_iff.mpr fun h => hj (Nat.blt_eq.mp h)]
    try rfl

@[expose] noncomputable def p4q (y : Nat) : Bool :=
  allN 22 (fun i => Nat.beq (p4sq y (p4sq y i)) i)

theorem p4q_of {y : Nat}
    (h : pcomp 22 5 (mask 5) (pcomp 22 5 (mask 5) y y) (pcomp 22 5 (mask 5) y y) = I) :
    p4q y = true := by
  unfold p4q
  rw [CFSG.KS.PK.allN_iff]
  intro i hi
  show Nat.beq (p4sq y (p4sq y i)) i = true
  have e := p4_fixes h hi
  rw [p4_fd_pcomp, if_pos hi] at e
  rw [p4sq_eq, p4sq_eq, e]
  exact Nat.beq_refl i

theorem p4q_cntW {X y : Nat} (hq : p4q y = false) : cntW 22 5 (mask 5) I X y = 0 := by
  have h2 : Nat.beq (pcomp 22 5 (mask 5) y y) I = false := by
    cases hb : Nat.beq (pcomp 22 5 (mask 5) y y) I
    · rfl
    · have e := Nat.eq_of_beq_eq_true hb
      rw [p4q_of (y := y) (by rw [e, p4_II])] at hq
      exact absurd hq (by decide)
  have h4 : ordFour 22 5 (mask 5) I y = 0 := by
    unfold ordFour
    simp only [CFSG.KS.PK.strictN_eq]
    rw [h2]
    cases hb : Nat.beq (pcomp 22 5 (mask 5) (pcomp 22 5 (mask 5) y y)
        (pcomp 22 5 (mask 5) y y)) I
    · rfl
    · rw [p4q_of (Nat.eq_of_beq_eq_true hb)] at hq
      exact absurd hq (by decide)
  unfold cntW ordTwo partnerW
  rw [h2, h4]
  cases Nat.beq y I <;> rfl

@[expose] noncomputable def cntQ (y : Nat) : Nat :=
  nIf(p4q y, cntW 22 5 (mask 5) I A y, nat_lit 0)

theorem cntQ_eq : cntQ = cntW 22 5 (mask 5) I A := by
  funext y
  unfold cntQ
  cases hq : p4q y
  · exact (p4q_cntW hq).symm
  · rfl

@[expose] noncomputable def p4cu (x j : Nat) : Nat :=
  nIf(Nat.blt j 22, p4sq x (pg 5 (mask 5) x j), nat_lit 0)

theorem p4cu_eq (x j : Nat) :
    p4cu x j = fd 5 (pcomp 22 5 (mask 5) (pcomp 22 5 (mask 5) x x) x) j := by
  rw [p4_fd_pcomp]
  unfold p4cu
  by_cases hj : j < 22
  · rw [if_pos hj, show Nat.blt j 22 = true from Nat.blt_eq.mpr hj, ← p4sq_eq]
    show p4sq x (pg 5 (mask 5) x j) = _
    rw [CFSG.KS.PK.pg_eq]
    try rfl
  · rw [if_neg hj, show Nat.blt j 22 = false from
      Bool.eq_false_iff.mpr fun h => hj (Nat.blt_eq.mp h)]
    try rfl

@[expose] noncomputable def p4r (x : Nat) : Bool :=
  allN 22 (fun i => Nat.beq (p4cu x (pg 5 (mask 5) x i)) i)

theorem p4r_of {x : Nat}
    (h : pcomp 22 5 (mask 5) (pcomp 22 5 (mask 5) (pcomp 22 5 (mask 5) x x) x) x = I) :
    p4r x = true := by
  unfold p4r
  rw [CFSG.KS.PK.allN_iff]
  intro i hi
  show Nat.beq (p4cu x (pg 5 (mask 5) x i)) i = true
  have e := p4_fixes h hi
  rw [p4_fd_pcomp, if_pos hi] at e
  rw [p4cu_eq, CFSG.KS.PK.pg_eq]
  change Nat.beq (fd 5 _ (fd 5 x i)) i = true
  rw [e]
  exact Nat.beq_refl i

theorem p4_oL (x k p d : Nat) : ordLoop 22 5 (mask 5) I x 4 (k + 1) p d =
    bIf(Nat.beq d 4, Nat.beq p I,
      bAnd(bIf(Nat.beq (Nat.mod 4 d) (nat_lit 0), bIf(Nat.beq p I, false, true), true),
        strictB (pcomp 22 5 (mask 5) p x) (fun q => ordLoop 22 5 (mask 5) I x 4 k q (Nat.succ d)))) :=
  rfl

theorem p4_oL4 (x p d : Nat) : ordLoop 22 5 (mask 5) I x 4 4 p d =
    bIf(Nat.beq d 4, Nat.beq p I,
      bAnd(bIf(Nat.beq (Nat.mod 4 d) (nat_lit 0), bIf(Nat.beq p I, false, true), true),
        strictB (pcomp 22 5 (mask 5) p x) (fun q => ordLoop 22 5 (mask 5) I x 4 3 q (Nat.succ d)))) :=
  p4_oL x 3 p d

theorem p4_oL3 (x p d : Nat) : ordLoop 22 5 (mask 5) I x 4 3 p d =
    bIf(Nat.beq d 4, Nat.beq p I,
      bAnd(bIf(Nat.beq (Nat.mod 4 d) (nat_lit 0), bIf(Nat.beq p I, false, true), true),
        strictB (pcomp 22 5 (mask 5) p x) (fun q => ordLoop 22 5 (mask 5) I x 4 2 q (Nat.succ d)))) :=
  p4_oL x 2 p d

theorem p4_oL2 (x p d : Nat) : ordLoop 22 5 (mask 5) I x 4 2 p d =
    bIf(Nat.beq d 4, Nat.beq p I,
      bAnd(bIf(Nat.beq (Nat.mod 4 d) (nat_lit 0), bIf(Nat.beq p I, false, true), true),
        strictB (pcomp 22 5 (mask 5) p x) (fun q => ordLoop 22 5 (mask 5) I x 4 1 q (Nat.succ d)))) :=
  p4_oL x 1 p d

theorem p4_oL1 (x p d : Nat) : ordLoop 22 5 (mask 5) I x 4 1 p d =
    bIf(Nat.beq d 4, Nat.beq p I,
      bAnd(bIf(Nat.beq (Nat.mod 4 d) (nat_lit 0), bIf(Nat.beq p I, false, true), true),
        strictB (pcomp 22 5 (mask 5) p x) (fun q => ordLoop 22 5 (mask 5) I x 4 0 q (Nat.succ d)))) :=
  p4_oL x 0 p d

theorem p4_ordExP (x : Nat) : ordExP 22 5 (mask 5) I x 4 =
    bAnd(bIf(Nat.beq x I, false, true),
      bAnd(bIf(Nat.beq (pcomp 22 5 (mask 5) x x) I, false, true),
        bAnd(true, Nat.beq (pcomp 22 5 (mask 5)
          (pcomp 22 5 (mask 5) (pcomp 22 5 (mask 5) x x) x) x) I))) := by
  unfold ordExP
  simp only [p4_oL4, p4_oL3, p4_oL2, p4_oL1, CFSG.KS.PK.strictB_eq]
  try rfl

theorem p4r_survF {h : Nat} (hr : p4r h = false) :
    survF 22 5 (mask 5) I A Ai B ZB m22Derivs ES PT 11 6 4 h = 0 := by
  have ho : ordExP 22 5 (mask 5) I h 4 = false := by
    cases hb : ordExP 22 5 (mask 5) I h 4
    · rfl
    · exfalso
      rw [p4_ordExP] at hb
      cases hc : Nat.beq (pcomp 22 5 (mask 5)
          (pcomp 22 5 (mask 5) (pcomp 22 5 (mask 5) h h) h) h) I
      · rw [hc] at hb
        revert hb
        cases Nat.beq h I <;> cases Nat.beq (pcomp 22 5 (mask 5) h h) I <;> decide
      · rw [p4r_of (Nat.eq_of_beq_eq_true hc)] at hr
        exact absurd hr (by decide)
  unfold survF
  rw [ho]
  try rfl

@[expose] noncomputable def chainP (x p : Nat) (k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) p (fun _ q => pcomp 22 5 (mask 5) q x) k

theorem chainP_succ' (x : Nat) : ∀ k p, chainP x p (k + 1) = chainP x (pcomp 22 5 (mask 5) p x) k
  | 0, _ => rfl
  | k + 1, p => by
    show pcomp 22 5 (mask 5) (chainP x p (k + 1)) x =
      pcomp 22 5 (mask 5) (chainP x (pcomp 22 5 (mask 5) p x) k) x
    rw [chainP_succ' x k p]

theorem ordLoop_chain (x o : Nat) : ∀ k p d, d + k = o →
    ordLoop 22 5 (mask 5) I x o (k + 1) p d = true → chainP x p k = I
  | 0, p, d, hd, h => by
    have hb : Nat.beq d o = true := by rw [Nat.beq_eq]; omega
    change bIf(Nat.beq d o, Nat.beq p I,
      bAnd(bIf(Nat.beq (Nat.mod o d) (nat_lit 0), bIf(Nat.beq p I, false, true), true),
        strictB (pcomp 22 5 (mask 5) p x) (fun q => ordLoop 22 5 (mask 5) I x o 0 q (Nat.succ d))))
      = true at h
    rw [hb] at h
    exact Nat.eq_of_beq_eq_true h
  | k + 1, p, d, hd, h => by
    have hb : Nat.beq d o = false :=
      Bool.eq_false_iff.mpr fun e => by have := Nat.eq_of_beq_eq_true e; omega
    change bIf(Nat.beq d o, Nat.beq p I,
      bAnd(bIf(Nat.beq (Nat.mod o d) (nat_lit 0), bIf(Nat.beq p I, false, true), true),
        strictB (pcomp 22 5 (mask 5) p x)
          (fun q => ordLoop 22 5 (mask 5) I x o (k + 1) q (Nat.succ d)))) = true at h
    rw [hb] at h
    simp only [CFSG.KS.PK.strictB_eq, CFSG.KS.PK.bAnd_eq, Bool.and_eq_true] at h
    rw [chainP_succ']
    exact ordLoop_chain x o k _ (Nat.succ d) (by omega) h.2

theorem ordExP_chain {x k : Nat} (h : ordExP 22 5 (mask 5) I x (k + 1) = true) : chainP x x k = I :=
  ordLoop_chain x (k + 1) k x 1 (by omega) h

@[expose] noncomputable def rdC (x p : Nat) (k : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun j => pg 5 (mask 5) p j)
    (fun _ r j => nIf(Nat.blt j 22, r (pg 5 (mask 5) x j), nat_lit 0)) k

theorem rdC_eq (x p : Nat) : ∀ k j, rdC x p k j = fd 5 (chainP x p k) j
  | 0, j => CFSG.KS.PK.pg_eq 5 p j
  | k + 1, j => by
    show nIf(Nat.blt j 22, rdC x p k (pg 5 (mask 5) x j), nat_lit 0) =
      fd 5 (pcomp 22 5 (mask 5) (chainP x p k) x) j
    rw [p4_fd_pcomp, rdC_eq x p k, CFSG.KS.PK.pg_eq]
    by_cases hj : j < 22
    · rw [if_pos hj, show Nat.blt j 22 = true from Nat.blt_eq.mpr hj]
      try rfl
    · rw [if_neg hj, show Nat.blt j 22 = false from
        Bool.eq_false_iff.mpr fun h => hj (Nat.blt_eq.mp h)]
      try rfl

@[expose] noncomputable def chainQ (x k : Nat) : Bool := allN 22 (fun i => Nat.beq (rdC x x k i) i)

theorem chainQ_of {x k : Nat} (h : chainP x x k = I) : chainQ x k = true := by
  unfold chainQ
  rw [CFSG.KS.PK.allN_iff]
  intro i hi
  show Nat.beq (rdC x x k i) i = true
  rw [rdC_eq, p4_fixes h hi]
  exact Nat.beq_refl i

theorem chainQ_survF {h : Nat} (hq : chainQ (pcomp 22 5 (mask 5) A h) 10 = false) :
    survF 22 5 (mask 5) I A Ai B ZB m22Derivs ES PT 11 6 4 h = 0 := by
  have ho : ordExP 22 5 (mask 5) I (pcomp 22 5 (mask 5) A h) 11 = false := by
    cases hb : ordExP 22 5 (mask 5) I (pcomp 22 5 (mask 5) A h) 11
    · rfl
    · rw [chainQ_of (ordExP_chain (k := 10) hb)] at hq
      exact absurd hq (by decide)
  unfold survF
  rw [ho]
  cases ordExP 22 5 (mask 5) I h 4 <;> rfl

@[expose] noncomputable def survQ (h : Nat) : Nat :=
  nIf(p4r h, nIf(chainQ (pcomp 22 5 (mask 5) A h) 10,
    survF 22 5 (mask 5) I A Ai B ZB m22Derivs ES PT 11 6 4 h, nat_lit 0), nat_lit 0)

theorem survQ_eq : survQ = survF 22 5 (mask 5) I A Ai B ZB m22Derivs ES PT 11 6 4 := by
  funext h
  unfold survQ
  cases hr : p4r h
  · exact (p4r_survF hr).symm
  · cases hq : chainQ (pcomp 22 5 (mask 5) A h) 10
    · exact (chainQ_survF hq).symm
    · rfl

theorem cnt_eqQ (t : Nat) :
    cnt t = pcnt 22 5 (mask 5) survQ [[t], L1, L2, L3, L4] I 0 := by
  rw [cnt, survQ_eq]

@[expose] noncomputable def chunkQ (k : Nat) : Bool :=
  allL (fun t => Nat.beq (pcnt 22 5 (mask 5) survQ [[t], L1, L2, L3, L4] I 0) 0)
    ((L0.drop (3 * k)).take 3)

theorem chunkOK_eqQ (k : Nat) : chunkOK k = chunkQ k := by
  unfold chunkOK chunkQ
  simp only [cnt_eqQ]

@[expose] noncomputable def tQ (n : Nat) : Bool :=
  Nat.beq (pcnt 22 5 (mask 5) survQ [[L0.getD n 0], L1, L2, L3, L4] I 0) 0

theorem p4_allL_of {f : Nat → Bool} : ∀ {L : List Nat}, (∀ x ∈ L, f x = true) → allL f L = true
  | [], _ => rfl
  | a :: l, h => by
    show Bool.rec (motive := fun _ => Bool) false (allL f l) (f a) = true
    rw [h a List.mem_cons_self, p4_allL_of (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem p4_len_L0 : L0.length = 22 := by decide

theorem chunkQ_of (k : Nat) (h : ∀ i, i < 3 → 3 * k + i < 22 → tQ (3 * k + i) = true) :
    chunkQ k = true := by
  unfold chunkQ
  apply p4_allL_of
  intro t ht
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ht
  simp only [List.length_take, List.length_drop, p4_len_L0] at hi
  have hn : 3 * k + i < 22 := by omega
  have e : ((L0.drop (3 * k)).take 3)[i] = L0.getD (3 * k + i) 0 := by
    rw [List.getElem_take, List.getElem_drop, List.getD_eq_getElem _ _ (by rw [p4_len_L0]; exact hn)]
  rw [e]
  have h' := h i (by omega) hn
  unfold tQ at h'
  exact h'

end CertificateChecks.KernelSpor.M22Syl

end
