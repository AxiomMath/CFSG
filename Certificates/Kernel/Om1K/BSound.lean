module

public import Certificates.Kernel.Om1K.BDefs
import CFSG.Certificates.Kernel.SporSch.LyLoop
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CertificateChecks.KernelOm1.B

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim
open CertificateChecks.KernelOm2 (wAK)
open CertificateChecks.KernelLC.E8 (NEG)
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Data (wDT)

@[expose] def NeAt (a b : Nat) : Prop := ∃ p < 240, ip a p ≠ ip b p

@[expose] def TwinFailK (x y s si : Nat) : Prop :=
  (∃ g ∈ [x, y], ∀ k < 4, (∃ q < 240, cjAt s si g q ≠ xpw x k q) ∧
      ∃ q < 240, cjAt s si g q ≠ ip y (xpw x k q)) ∧
    ∃ a ∈ [x, y], ∃ b ∈ [x, y], ∃ p < 240, ip a (cjAt s si b p) ≠ cjAt s si b (ip a p)

@[expose] def PairFact (Lg LgI : Nat → Nat) (nL : Nat) (inR inR' : Prop) (x y : Nat) : Prop :=
  (∃ p < 240, ip y (ip x p) ≠ ip x (ip x (ip x (ip y p)))) ∨ inR ∨ inR' ∨
    ∃ h < nL, TwinFailK x y (Lg h) (LgI h)

theorem om1B_strictB (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem om1B_bAnd (a b : Bool) : Bool.rec (motive := fun _ => Bool) false b a = (a && b) := by
  cases a <;> rfl

theorem om1B_neq (a b : Nat) :
    Bool.rec (motive := fun _ => Bool) true false (Nat.beq a b) = true ↔ a ≠ b := by
  cases h : Nat.beq a b
  · exact ⟨fun _ => Nat.ne_of_beq_eq_false h, fun _ => rfl⟩
  · exact ⟨fun e => absurd e Bool.false_ne_true, fun e => absurd (Nat.eq_of_beq_eq_true h) e⟩

theorem om1B_imp (c t : Bool) :
    Bool.rec (motive := fun _ => Bool) true t c = true ↔ (c = true → t = true) := by
  cases c
  · exact ⟨fun _ e => absurd e Bool.false_ne_true, fun _ => rfl⟩
  · exact ⟨fun h _ => h, fun h => h rfl⟩

theorem om1B_case (c t e : Bool) (h : Bool.rec (motive := fun _ => Bool) e t c = true) :
    (c = true ∧ t = true) ∨ (c = false ∧ e = true) := by
  cases c
  · exact Or.inr ⟨rfl, h⟩
  · exact Or.inl ⟨rfl, h⟩

theorem om1B_mem (c : Bool) (x y : Nat) : Bool.rec (motive := fun _ => Nat) y x c ∈ [x, y] := by
  cases c
  · exact List.mem_cons_of_mem _ List.mem_cons_self
  · exact List.mem_cons_self

theorem om1B_allN {n : Nat} {f : Nat → Bool} (h : allN n f = true) : ∀ i < n, f i = true :=
  CFSG.KS.Raw.Orb.allN_iff.1 h

theorem krOK_sound {k : Nat} (hk : krOK k = true) :
    BD.KR k = (q8K (A.EL.G 1) (A.EL.G 2)).getD k 0 :=
  Nat.eq_of_beq_eq_true hk

theorem ksOK_sound {KS : Nat → Nat} {k : Nat} (hk : ksOK KS k = true) :
    cnK (KS k) = true ∧ pc (A.EL.G 3) (BD.KR k) = pc (KS k) (A.EL.G 3) := by
  unfold ksOK at hk
  rw [om1B_bAnd, Bool.and_eq_true] at hk
  exact ⟨hk.1, Nat.eq_of_beq_eq_true hk.2⟩

theorem lhOK_sound {G A AI R : Nat → Nat} {ng h : Nat} (hc : lhOK G A AI R ng h = true) :
    ∃ a ≤ ng, ∃ b ≤ ng, A h = pc (gI G ng a) (gI G ng b) ∧ pc (A h) (AI h) = pid ∧
      cnK (AI h) = true := by
  unfold lhOK at hc
  simp only [om1B_strictB, om1B_bAnd, Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq] at hc
  obtain ⟨h1, h2, h3, h4, h5⟩ := hc
  exact ⟨_, h1, _, h2, h3, h4, h5⟩

theorem dtOK_sound {DG DF : Nat → Nat} {j : Nat} (h : dtOK DG DF j = true) :
    cnK (DG j) = true ∧ pc (DG j) (wAK (wDT.getD j [])) = pc (wAK (wDT.getD j [])) T0 ∧
      NeAt (DG j) T0 ∧ NeAt (DG j) (pc T0 NEG) := by
  unfold dtOK neAt at h
  simp only [om1B_strictB, om1B_bAnd, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, om1B_neq] at h
  obtain ⟨h1, h2, ⟨h3, h4⟩, ⟨h5, h6⟩⟩ := h
  exact ⟨h1, h2, ⟨_, h3, h4⟩, ⟨_, h5, h6⟩⟩

theorem witOK_sound {E W : Nat → Nat} {nE i : Nat} (h : witOK E nE W i = true) :
    fld(W i, 0, 7) = 0 ∨
      (fld(W i, 0, 7) ≤ 4 ∧ fld(W i, 39, 8191) < nE ∧ fld(W i, 52, 255) < 204 ∧
        wLetOK fld(W i, 3, 511) = true ∧ wLetOK fld(W i, 12, 511) = true ∧
        wLetOK fld(W i, 21, 511) = true ∧ wLetOK fld(W i, 30, 511) = true ∧
        ((wInv fld(W i, 3, 511) || wInv fld(W i, 12, 511) || wInv fld(W i, 21, 511) ||
            wInv fld(W i, 30, 511)) = true → pc (E i) (E fld(W i, 39, 8191)) = pid) ∧
        wProd (E i) (E fld(W i, 39, 8191)) fld(W i, 0, 7) fld(W i, 3, 511) fld(W i, 12, 511)
          fld(W i, 21, 511) fld(W i, 30, 511) = BD.DG fld(W i, 52, 255)) := by
  unfold witOK at h
  simp only [om1B_strictB] at h
  rcases om1B_case _ _ _ h with ⟨hz, -⟩ | ⟨-, h⟩
  · exact Or.inl (Nat.eq_of_beq_eq_true hz)
  · simp only [om1B_strictB, om1B_bAnd, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, Nat.beq_eq,
      om1B_imp] at h
    exact Or.inr h

theorem noWit_sound {W : Nat → Nat} {i : Nat} (h : noWit W i = false) : fld(W i, 0, 7) ≠ 0 := by
  intro e
  unfold noWit at h
  rw [e] at h
  exact Bool.false_ne_true h.symm

theorem cntN_eq (n : Nat) (p : Nat → Bool) : cntN n p = ((List.range n).filter p).length := by
  unfold cntN
  rw [CFSG.KS.SporSch.LyLoop.foldN_eqP]
  induction (List.range n) with
  | nil => rfl
  | cons x l ih =>
    rw [List.foldr_cons, ih, List.filter_cons]
    cases p x <;> rfl

theorem sqOK_sound {E SQ RT : Nat → Nat} {tt nR i : Nat} (h : sqOK E SQ RT tt nR i = true) :
    (∃ a < nR, fld(RT a, 0, 8191) = i) ∨ ∃ p < 240, ip (E i) (ip (E i) p) ≠ ip tt p := by
  unfold sqOK at h
  simp only [om1B_strictB] at h
  rcases om1B_case _ _ _ h with ⟨-, h⟩ | ⟨-, h⟩
  · simp only [om1B_strictB, om1B_bAnd, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
    exact Or.inl ⟨_, h.1, h.2⟩
  · simp only [om1B_strictB, om1B_bAnd, Bool.and_eq_true, Nat.blt_eq, om1B_neq] at h
    exact Or.inr ⟨_, h.1, h.2⟩

theorem rootOK_sound {E RT : Nat → Nat} {nE a : Nat} (h : rootOK E RT nE a = true) :
    fld(RT a, 0, 8191) < nE ∧
      (fld(RT a, 13, 1) = 1 → E fld(RT a, 0, 8191) = BD.KR fld(RT a, 14, 7)) ∧
      (fld(RT a, 17, 1) = 1 → E fld(RT a, 0, 8191) = BD.KS fld(RT a, 18, 7)) := by
  unfold rootOK at h
  simp only [om1B_strictB, om1B_bAnd, Bool.and_eq_true, Nat.blt_eq, om1B_imp, Nat.beq_eq] at h
  exact h

theorem om1B_twin {x y s si r : Nat} (h : twinOK x y s si r = true) : TwinFailK x y s si := by
  unfold twinOK at h
  simp only [om1B_strictB, om1B_bAnd, Bool.and_eq_true, Nat.blt_eq, om1B_neq] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨⟨_, om1B_mem (Nat.beq (Nat.land (Nat.shiftRight r 17) 1) 0) x y, fun k hk => ⟨?_, ?_⟩⟩,
    _, om1B_mem (Nat.beq (Nat.land (Nat.shiftRight r 18) 1) 0) x y,
    _, om1B_mem (Nat.beq (Nat.land (Nat.shiftRight r 19) 1) 0) x y, _, h3, h4⟩
  · have h5 := om1B_allN h1 k hk
    simp only [Bool.and_eq_true, Nat.blt_eq, om1B_neq] at h5
    exact ⟨_, h5.1, h5.2⟩
  · have h5 := om1B_allN h2 k hk
    simp only [Bool.and_eq_true, Nat.blt_eq, om1B_neq] at h5
    exact ⟨_, h5.1, h5.2⟩

theorem q8Row_sound {E RT PR Lg LgI : Nat → Nat} {nL nR : Nat} {withR : Bool} {a : Nat}
    (h : q8Row E RT PR Lg LgI nL nR withR a = true) : ∀ b < nR,
    PairFact Lg LgI nL (withR = true ∧ fld(RT a, 13, 1) = 1 ∧ fld(RT b, 13, 1) = 1)
      (withR = true ∧ fld(RT a, 17, 1) = 1 ∧ fld(RT b, 17, 1) = 1)
      (E fld(RT a, 0, 8191)) (E fld(RT b, 0, 8191)) := by
  intro b hb
  unfold q8Row at h
  simp only [om1B_strictB] at h
  have hp := om1B_allN h b hb
  unfold q8Pair at hp
  simp only [om1B_strictB] at hp
  rcases om1B_case _ _ _ hp with ⟨-, hp⟩ | ⟨-, hp⟩
  · simp only [om1B_bAnd, Bool.and_eq_true, Nat.blt_eq, om1B_neq] at hp
    exact Or.inl ⟨_, hp.1, hp.2⟩
  rcases om1B_case _ _ _ hp with ⟨-, hp⟩ | ⟨-, hp⟩
  · simp only [om1B_bAnd, Bool.and_eq_true, Nat.beq_eq] at hp
    exact Or.inr (Or.inl hp)
  rcases om1B_case _ _ _ hp with ⟨-, hp⟩ | ⟨-, hp⟩
  · simp only [om1B_bAnd, Bool.and_eq_true, Nat.beq_eq] at hp
    exact Or.inr (Or.inr (Or.inl hp))
  simp only [om1B_strictB, om1B_bAnd, Bool.and_eq_true, Nat.blt_eq] at hp
  exact Or.inr (Or.inr (Or.inr ⟨_, hp.1, om1B_twin hp.2⟩))

theorem oNodeOK_sound {OP : Nat → Nat} {m : Nat} (h : oNodeOK OP m = true) :
    (∀ c < 4, cnK (oc c m) = true) ∧
      (m = 0 → BD.OA 0 = A.EL.G 1 ∧ BD.OB 0 = A.EL.G 2 ∧
        pc (A.EL.G 3) (A.EL.G 1) = pc (BD.OC 0) (A.EL.G 3) ∧
        pc (A.EL.G 3) (A.EL.G 2) = pc (BD.OD 0) (A.EL.G 3)) ∧
      (m ≠ 0 → ∃ par < m, ∃ k < 7, ∀ c < 4, pc (A.TG.G k) (oc c par) = pc (oc c m) (A.TG.G k)) := by
  unfold oNodeOK at h
  simp only [om1B_strictB, om1B_bAnd, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨om1B_allN h1, fun hm => ?_, fun hm => ?_⟩
  · have hz : Nat.beq m 0 = true := by
      rw [hm]
      rfl
    rw [hz] at h2
    simp only [om1B_bAnd, Bool.and_eq_true, Nat.beq_eq] at h2
    exact h2
  · have hz : Nat.beq m 0 = false := by
      cases e : Nat.beq m 0
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true e) hm
    rw [hz] at h2
    simp only [om1B_bAnd, Bool.and_eq_true, Nat.blt_eq] at h2
    exact ⟨_, h2.1, _, h2.2.1, fun c hc => Nat.eq_of_beq_eq_true (om1B_allN h2.2.2 c hc)⟩

end CertificateChecks.KernelOm1.B

end
