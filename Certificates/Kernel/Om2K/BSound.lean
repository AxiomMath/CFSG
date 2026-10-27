module

public import Certificates.Kernel.Om2K.BDefs
import CFSG.Certificates.Kernel.Spor.Loops
import CFSG.Certificates.Kernel.SporSch.LyLoop

public section

namespace CertificateChecks.KernelOm2

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim

@[expose] def NeAt (a b : Nat) : Prop := ∃ p < 480, ip a p ≠ ip b p

@[expose] def TwinFailK (x y s si : Nat) : Prop :=
  (∃ g ∈ [x, y], ∀ k < 4, (∃ q < 480, cjAt s si g q ≠ xpw x k q) ∧
      ∃ q < 480, cjAt s si g q ≠ ip y (xpw x k q)) ∧
    ∃ a ∈ [x, y], ∃ b ∈ [x, y], ∃ p < 480, ip a (cjAt s si b p) ≠ cjAt s si b (ip a p)

@[expose] def PairFact (Lg LgI : Nat → Nat) (nL : Nat) (inR : Prop) (x y : Nat) : Prop :=
  (∃ p < 480, ip y (ip x p) ≠ ip x (ip x (ip x (ip y p)))) ∨ inR ∨
    ∃ h < nL, TwinFailK x y (Lg h) (LgI h)

theorem neAt_sound {a b p : Nat} (h : neAt a b p = true) : NeAt a b := by
  unfold neAt at h
  obtain ⟨hlt, hne⟩ := (bAnd_iff _ _).1 h
  refine ⟨p, Nat.blt_eq.mp hlt, fun heq => ?_⟩
  rw [SporSch.LyLoop.bIf_eqP, if_pos (Nat.beq_eq.mpr heq)] at hne
  cases hne

theorem lhOK_sound {G A AI R : Nat → Nat} {ng h : Nat} (hc : lhOK G A AI R ng h = true) :
    ∃ a ≤ ng, ∃ b ≤ ng, A h = pc (gI G ng a) (gI G ng b) ∧ pc (A h) (AI h) = pid ∧
      cnK (AI h) = true := by
  unfold lhOK at hc
  simp only [SporSch.LyLoop.strictB_eqB] at hc
  obtain ⟨ha, hc⟩ := (bAnd_iff _ _).1 hc
  obtain ⟨hb, hc⟩ := (bAnd_iff _ _).1 hc
  obtain ⟨hA, hc⟩ := (bAnd_iff _ _).1 hc
  obtain ⟨hI, hc⟩ := (bAnd_iff _ _).1 hc
  exact ⟨_, Nat.le_of_ble_eq_true ha, _, Nat.le_of_ble_eq_true hb, Nat.eq_of_beq_eq_true hA,
    Nat.eq_of_beq_eq_true hI, hc⟩

theorem zOK_sound {k : Nat} (hk : zOK k = true) :
    (k = 0 → BD.ZT 0 = EL.G 0) ∧ (k ≠ 0 → BD.ZT k = pc (EL.G 0) (cAK (k - 1))) := by
  unfold zOK at hk
  cases h : Nat.beq k 0
  · rw [h] at hk
    exact ⟨fun hh => absurd hh (Nat.ne_of_beq_eq_false h), fun _ => Nat.eq_of_beq_eq_true hk⟩
  · rw [h] at hk
    exact ⟨fun _ => Nat.eq_of_beq_eq_true hk, fun hh => absurd (Nat.eq_of_beq_eq_true h) hh⟩

theorem kgOK_sound {k : Nat} (hk : kgOK k = true) :
    BD.KG k = (q8K (EL.G 1) (EL.G 2)).getD k 0 :=
  Nat.eq_of_beq_eq_true hk

theorem nodeOK_sound {NG NP NF : Nat → Nat} {j : Nat} (h : nodeOK NG NP NF j = true) :
    cnK (NG j) = true ∧ (fld(NF j, 0, 1) = 1 → NeAt (NG j) (BD.ZT 0)) ∧
      (fld(NF j, 10, 1) = 1 → ∀ k, 0 < k → k < 4 → NeAt (NG j) (BD.ZT k)) ∧
      (j = 0 → NG 0 = EL.G 0) ∧
      (j ≠ 0 → ∃ par < j, ∃ l < 16, pc (L.G l) (NG par) = pc (NG j) (L.G l)) := by
  unfold nodeOK at h
  simp only [SporSch.LyLoop.strictB_eqB] at h
  obtain ⟨hcn, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨hflag, hrest⟩ := (bAnd_iff _ _).1 h
  unfold flagOK at hflag
  obtain ⟨hf0, hf10⟩ := (bAnd_iff _ _).1 hflag
  refine ⟨hcn, ?_, ?_, ?_, ?_⟩
  · intro hbit
    have hc : Nat.beq (fld(NF j, 0, 1)) 1 = true := Nat.beq_eq_true_eq _ _ ▸ hbit
    rw [hc] at hf0
    exact neAt_sound hf0
  · intro hbit k hk0 hk4
    have hc : Nat.beq (fld(NF j, 10, 1)) 1 = true := Nat.beq_eq_true_eq _ _ ▸ hbit
    rw [hc] at hf10
    obtain ⟨-, hf⟩ := (bAnd_iff _ _).1 hf10
    obtain ⟨hf1, hf⟩ := (bAnd_iff _ _).1 hf
    obtain ⟨hf2, hf3⟩ := (bAnd_iff _ _).1 hf
    interval_cases k
    exacts [neAt_sound hf1, neAt_sound hf2, neAt_sound hf3]
  · intro hj
    have hc : Nat.beq j 0 = true := Nat.beq_eq_true_eq _ _ ▸ hj
    rw [hc] at hrest
    exact Nat.eq_of_beq_eq_true hrest
  · intro hj
    have hc : Nat.beq j 0 = false := by
      cases hh : Nat.beq j 0
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true hh) hj
    rw [hc] at hrest
    obtain ⟨hpar, hl⟩ := (bAnd_iff _ _).1 hrest
    exact ⟨fld(NP j, 0, 4095), Nat.blt_eq.mp hpar, fld(NP j, 12, 15),
      Nat.lt_succ_of_le Nat.and_le_right, Nat.eq_of_beq_eq_true hl⟩

theorem witOK_sound {E W : Nat → Nat} {nE i : Nat} (h : witOK E nE W i = true) :
    fld(W i, 0, 3) = 0 ∨
      (fld(W i, 0, 3) < 4 ∧ fld(W i, 29, 8191) < nE ∧ fld(W i, 42, 4095) < BD.nN ∧
        fld(BD.NF fld(W i, 42, 4095), 0, 1) = 1 ∧ wLetOK fld(W i, 2, 511) = true ∧
        wLetOK fld(W i, 11, 511) = true ∧ wLetOK fld(W i, 20, 511) = true ∧
        ((wInv fld(W i, 2, 511) || wInv fld(W i, 11, 511) || wInv fld(W i, 20, 511)) = true →
          pc (E i) (E fld(W i, 29, 8191)) = pid) ∧
        wProd (E i) (E fld(W i, 29, 8191)) fld(W i, 0, 3) fld(W i, 2, 511) fld(W i, 11, 511)
          fld(W i, 20, 511) = BD.NG fld(W i, 42, 4095)) := by
  unfold witOK at h
  simp only [SporSch.LyLoop.strictB_eqB] at h
  cases hb : Nat.beq (fld(W i, 0, 3)) 0
  · right
    rw [hb] at h
    obtain ⟨h1, h⟩ := (bAnd_iff _ _).1 h
    obtain ⟨h2, h⟩ := (bAnd_iff _ _).1 h
    obtain ⟨h3, h⟩ := (bAnd_iff _ _).1 h
    obtain ⟨h4, h⟩ := (bAnd_iff _ _).1 h
    obtain ⟨h5, h⟩ := (bAnd_iff _ _).1 h
    obtain ⟨h6, h⟩ := (bAnd_iff _ _).1 h
    obtain ⟨h7, h⟩ := (bAnd_iff _ _).1 h
    obtain ⟨h8, h9⟩ := (bAnd_iff _ _).1 h
    refine ⟨Nat.blt_eq.mp h1, Nat.blt_eq.mp h2, Nat.blt_eq.mp h3,
      Nat.eq_of_beq_eq_true h4, h5, h6, h7, ?_, Nat.eq_of_beq_eq_true h9⟩
    intro hcond
    rw [hcond] at h8
    exact Nat.eq_of_beq_eq_true h8
  · left
    exact Nat.eq_of_beq_eq_true hb

theorem noWit_sound {W : Nat → Nat} {f i : Nat} (h : noWit W f i = false) :
    fld(W i, 0, 3) ≠ 0 ∧ fld(BD.NF fld(W i, 42, 4095), f, 1) = 1 := by
  unfold noWit at h
  simp only [SporSch.LyLoop.strictB_eqB] at h
  cases hb : Nat.beq (fld(W i, 0, 3)) 0
  · rw [hb] at h
    refine ⟨Nat.ne_of_beq_eq_false hb, ?_⟩
    have hle : fld(BD.NF fld(W i, 42, 4095), f, 1) ≤ 1 := Nat.and_le_right
    have hne : fld(BD.NF fld(W i, 42, 4095), f, 1) ≠ 0 := Nat.ne_of_beq_eq_false h
    omega
  · rw [hb] at h
    exact absurd h.symm Bool.false_ne_true

theorem cntN_eq (n : Nat) (p : Nat → Bool) : cntN n p = ((List.range n).filter p).length := by
  unfold cntN
  rw [CFSG.KS.SporSch.LyLoop.foldN_eqP]
  induction (List.range n) with
  | nil => rfl
  | cons x l ih =>
    rw [List.foldr_cons, ih, List.filter_cons]
    cases p x <;> rfl

theorem sqOK_sound {E SQ RT : Nat → Nat} {tt nR i : Nat} (h : sqOK E SQ RT tt nR i = true) :
    (∃ a < nR, fld(RT a, 0, 8191) = i) ∨ ∃ p < 480, ip (E i) (ip (E i) p) ≠ ip tt p := by
  unfold sqOK at h
  simp only [SporSch.LyLoop.strictB_eqB] at h
  cases hb : Nat.beq (fld(SQ i, 0, 1)) 1
  · right
    rw [hb] at h
    obtain ⟨hp, hne⟩ := (bAnd_iff _ _).1 h
    refine ⟨fld(SQ i, 1, 511), Nat.blt_eq.mp hp, fun heq => ?_⟩
    cases hc : Nat.beq (ip (E i) (ip (E i) (fld(SQ i, 1, 511)))) (ip tt (fld(SQ i, 1, 511)))
    · rw [hc] at hne
      exact Nat.ne_of_beq_eq_false hc heq
    · rw [hc] at hne
      exact Bool.noConfusion hne
  · left
    rw [hb] at h
    obtain ⟨ha, hbeq⟩ := (bAnd_iff _ _).1 h
    exact ⟨fld(SQ i, 1, 255), Nat.blt_eq.mp ha, Nat.eq_of_beq_eq_true hbeq⟩

theorem rootOK_sound {E RT : Nat → Nat} {nE a : Nat} (h : rootOK E RT nE a = true) :
    fld(RT a, 0, 8191) < nE ∧
      (fld(RT a, 13, 1) = 1 → E fld(RT a, 0, 8191) = BD.KG fld(RT a, 14, 7)) := by
  unfold rootOK at h
  simp only [SporSch.LyLoop.strictB_eqB] at h
  obtain ⟨hlt, hb⟩ := (bAnd_iff _ _).1 h
  refine ⟨Nat.blt_eq.mp hlt, fun h13 => ?_⟩
  rw [SporSch.LyLoop.bIf_eqP] at hb
  rw [if_pos (Nat.beq_eq.mpr h13)] at hb
  exact Nat.eq_of_beq_eq_true hb

theorem q8Row_sound {E RT PR Lg LgI : Nat → Nat} {nL nR : Nat} {withR : Bool} {a : Nat}
    (h : q8Row E RT PR Lg LgI nL nR withR a = true) : ∀ b < nR,
    PairFact Lg LgI nL (withR = true ∧ fld(RT a, 13, 1) = 1 ∧ fld(RT b, 13, 1) = 1)
      (E fld(RT a, 0, 8191)) (E fld(RT b, 0, 8191)) := by
  unfold q8Row at h
  simp only [SporSch.LyLoop.strictB_eqB] at h
  intro b hb
  have hb' := allN_spec h b hb
  unfold q8Pair at hb'
  simp only [SporSch.LyLoop.strictB_eqB] at hb'
  set x : Nat := E fld(RT a, 0, 8191) with hx
  set y : Nat := E fld(RT b, 0, 8191) with hy
  set r : Nat := fld(PR a, Nat.mul 96 b, 9903520314283042199192993791) with hr
  set kd : Nat := fld(r, 0, 3) with hkd
  have bIf_false_eq : ∀ c : Bool, bIf(c, false, true) = true → c = false := by
    intro c hc
    cases c
    · rfl
    · exact absurd hc Bool.false_ne_true
  have twin_sound : ∀ s si : Nat, twinOK x y s si r = true → TwinFailK x y s si := by
    intro s si ht
    unfold twinOK at ht
    simp only [SporSch.LyLoop.strictB_eqB] at ht
    obtain ⟨hL1, ht⟩ := (bAnd_iff _ _).1 ht
    obtain ⟨hL2, ht⟩ := (bAnd_iff _ _).1 ht
    obtain ⟨hplt, hne3⟩ := (bAnd_iff _ _).1 ht
    have mem_pair : ∀ z : Nat, (z = x ∨ z = y) → z ∈ [x, y] := by
      intro z hz
      rcases hz with h | h
      · rw [h]; exact List.mem_cons_self
      · rw [h]; exact List.mem_cons_of_mem x List.mem_cons_self
    have sel : ∀ c : Bool, nIf(c, x, y) = x ∨ nIf(c, x, y) = y := by
      intro c
      cases c
      · exact Or.inr rfl
      · exact Or.inl rfl
    unfold TwinFailK
    refine ⟨⟨nIf(Nat.beq (fld(r, 18, 1)) 0, x, y), mem_pair _ (sel _), fun k hk => ⟨?_, ?_⟩⟩,
      nIf(Nat.beq (fld(r, 19, 1)) 0, x, y), mem_pair _ (sel _),
      nIf(Nat.beq (fld(r, 20, 1)) 0, x, y), mem_pair _ (sel _),
      fld(r, 2, 511), Nat.blt_eq.mp hplt, ?_⟩
    · obtain ⟨hq, hne⟩ := (bAnd_iff _ _).1 (allN_spec hL1 k hk)
      exact ⟨_, Nat.blt_eq.mp hq, Nat.ne_of_beq_eq_false (bIf_false_eq _ hne)⟩
    · obtain ⟨hq, hne⟩ := (bAnd_iff _ _).1 (allN_spec hL2 k hk)
      exact ⟨_, Nat.blt_eq.mp hq, Nat.ne_of_beq_eq_false (bIf_false_eq _ hne)⟩
    · exact Nat.ne_of_beq_eq_false (bIf_false_eq _ hne3)
  unfold PairFact
  cases hk0 : Nat.beq kd 0
  case false =>
    rw [hk0] at hb'
    dsimp only at hb'
    cases hk1 : Nat.beq kd 1
    case false =>
      rw [hk1] at hb'
      dsimp only at hb'
      cases hk2 : Nat.beq kd 2
      case false =>
        rw [hk2] at hb'
        dsimp only at hb'
        exact absurd hb' Bool.false_ne_true
      case true =>
        rw [hk2] at hb'
        dsimp only at hb'
        obtain ⟨hlt, htwin⟩ := (bAnd_iff _ _).1 hb'
        exact Or.inr (Or.inr ⟨fld(r, 11, 127), Nat.blt_eq.mp hlt, twin_sound _ _ htwin⟩)
    case true =>
      rw [hk1] at hb'
      dsimp only at hb'
      obtain ⟨hwithR, hB⟩ := (bAnd_iff _ _).1 hb'
      obtain ⟨ha1, hb1⟩ := (bAnd_iff _ _).1 hB
      exact Or.inr (Or.inl ⟨hwithR, Nat.eq_of_beq_eq_true ha1, Nat.eq_of_beq_eq_true hb1⟩)
  case true =>
    rw [hk0] at hb'
    dsimp only at hb'
    obtain ⟨hplt, hne⟩ := (bAnd_iff _ _).1 hb'
    exact Or.inl ⟨fld(r, 2, 511), Nat.blt_eq.mp hplt, Nat.ne_of_beq_eq_false (bIf_false_eq _ hne)⟩

theorem oNodeOK_sound {m : Nat} (h : oNodeOK m = true) :
    cnK (BD.OA m) = true ∧ cnK (BD.OB m) = true ∧
      (m = 0 → BD.OA 0 = EL.G 1 ∧ BD.OB 0 = EL.G 2) ∧
      (m ≠ 0 → ∃ par < m, ∃ k < 8, pc (TG.G k) (BD.OA par) = pc (BD.OA m) (TG.G k) ∧
        pc (TG.G k) (BD.OB par) = pc (BD.OB m) (TG.G k)) := by
  unfold oNodeOK at h
  simp only [SporSch.LyLoop.strictB_eqB] at h
  rw [bAnd_iff] at h
  obtain ⟨hcA, h⟩ := h
  rw [bAnd_iff] at h
  obtain ⟨hcB, h⟩ := h
  rw [SporSch.LyLoop.bIf_eqP] at h
  refine ⟨hcA, hcB, ?_, ?_⟩
  · intro hm0
    rw [if_pos (Nat.beq_eq.mpr hm0)] at h
    rw [bAnd_iff] at h
    obtain ⟨hA, hB⟩ := h
    exact ⟨Nat.eq_of_beq_eq_true hA, Nat.eq_of_beq_eq_true hB⟩
  · intro hm0
    rw [if_neg (fun hq => hm0 (Nat.beq_eq.mp hq))] at h
    rw [bAnd_iff] at h
    obtain ⟨hpar, h⟩ := h
    rw [bAnd_iff] at h
    obtain ⟨hk, h⟩ := h
    rw [bAnd_iff] at h
    obtain ⟨hA, hB⟩ := h
    exact ⟨_, Nat.blt_eq.mp hpar, _, Nat.blt_eq.mp hk, Nat.eq_of_beq_eq_true hA,
      Nat.eq_of_beq_eq_true hB⟩

theorem oDistOK_sound {m : Nat} (h : oDistOK m = true) :
    ∀ m' < 24, m < m' → NeAt (BD.OA m) (BD.OA m') ∨ NeAt (BD.OB m) (BD.OB m') := by
  unfold oDistOK at h
  intro m' hm' hm
  have hh := allN_spec h m' hm'
  rw [SporSch.LyLoop.bIf_eqP] at hh
  rw [if_pos (Nat.blt_eq.mpr hm)] at hh
  simp only [SporSch.LyLoop.strictB_eqB] at hh
  rw [SporSch.LyLoop.bIf_eqP] at hh
  by_cases hb : fld(BD.OD (Nat.add (Nat.mul 24 m) m'), 0, 1) = 0
  · left
    rw [if_pos (Nat.beq_eq.mpr hb)] at hh
    exact neAt_sound hh
  · right
    rw [if_neg (fun hq => hb (Nat.beq_eq.mp hq))] at hh
    exact neAt_sound hh

theorem sgOK_sound {m : Nat} (h : sgOK m = true) :
    cnK (BD.SG m) = true ∧ (m / 2 = 0 → BD.SG m = EL.G (1 + m % 2)) ∧
      (m / 2 ≠ 0 → pc (FU.G (m / 2 - 1)) (EL.G (1 + m % 2)) = pc (BD.SG m) (FU.G (m / 2 - 1)) ∧
        pc (BD.SG m) (EL.G 1) = pc (EL.G 1) (BD.SG m) ∧
        pc (BD.SG m) (EL.G 2) = pc (EL.G 2) (BD.SG m)) := by
  unfold sgOK at h
  simp only [SporSch.LyLoop.strictB_eqB] at h
  rw [bAnd_iff] at h
  obtain ⟨hc, h⟩ := h
  rw [SporSch.LyLoop.bIf_eqP] at h
  refine ⟨hc, ?_, ?_⟩
  · intro hf
    have hf' : Nat.div m 2 = 0 := hf
    rw [if_pos (Nat.beq_eq.mpr hf')] at h
    exact Nat.eq_of_beq_eq_true h
  · intro hf
    have hf' : Nat.div m 2 ≠ 0 := hf
    rw [if_neg (fun hq => hf' (Nat.beq_eq.mp hq))] at h
    rw [bAnd_iff] at h
    obtain ⟨h1, h⟩ := h
    rw [bAnd_iff] at h
    obtain ⟨h2, h3⟩ := h
    exact ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3⟩

theorem crOK_sound {CR E : Nat → Nat} {i : Nat} (h : crOK CR E i = true) :
    (fld(CR i, 0, 1) = 1 ∨ ∃ p < 480,
        ip (E i) (ip (BD.SG fld(CR i, 1, 7)) p) ≠ ip (BD.SG fld(CR i, 1, 7)) (ip (E i) p)) ∧
      ((∃ q < 480, ip (E i) (ip (E i) q) ≠ q) ∨ (∃ k < 4, E i = BD.ZT k) ∨
        (NeAt (E i) (EL.G 0) ∧ ∀ l < 8, pc (E i) (L.G l) = pc (L.G l) (E i))) := by
  unfold crOK at h
  simp only [SporSch.LyLoop.strictB_eqB] at h
  obtain ⟨hA, hB⟩ := (bAnd_iff _ _).1 h
  refine ⟨?_, ?_⟩
  · rw [SporSch.LyLoop.bIf_eqP] at hA
    by_cases hb0 : fld(CR i, 0, 1) = 1
    · left
      exact hb0
    · right
      rw [if_neg (fun hq => hb0 (Nat.beq_eq.mp hq))] at hA
      rw [bAnd_iff] at hA
      obtain ⟨hlt, hne⟩ := hA
      refine ⟨fld(CR i, 4, 511), Nat.blt_eq.mp hlt, fun heq => ?_⟩
      rw [SporSch.LyLoop.bIf_eqP] at hne
      rw [if_pos (Nat.beq_eq.mpr heq)] at hne
      cases hne
  · rw [SporSch.LyLoop.bIf_eqP] at hB
    by_cases hb13 : fld(CR i, 13, 1) = 0
    · left
      rw [if_pos (Nat.beq_eq.mpr hb13)] at hB
      rw [bAnd_iff] at hB
      obtain ⟨hlt, hne⟩ := hB
      refine ⟨fld(CR i, 14, 511), Nat.blt_eq.mp hlt, fun heq => ?_⟩
      rw [SporSch.LyLoop.bIf_eqP] at hne
      rw [if_pos (Nat.beq_eq.mpr heq)] at hne
      cases hne
    · rw [if_neg (fun hq => hb13 (Nat.beq_eq.mp hq))] at hB
      rw [SporSch.LyLoop.bIf_eqP] at hB
      by_cases hb23 : fld(CR i, 23, 1) = 0
      · right; left
        rw [if_pos (Nat.beq_eq.mpr hb23)] at hB
        exact ⟨fld(CR i, 24, 3), Nat.lt_succ_of_le Nat.and_le_right, Nat.eq_of_beq_eq_true hB⟩
      · right; right
        rw [if_neg (fun hq => hb23 (Nat.beq_eq.mp hq))] at hB
        obtain ⟨hne, hall⟩ := (bAnd_iff _ _).1 hB
        exact ⟨neAt_sound hne, fun l hl => Nat.eq_of_beq_eq_true (allN_spec hall l hl)⟩

end CertificateChecks.KernelOm2

end
