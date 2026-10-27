module

public import Certificates.Kernel.SporSch.Ly.FiveLanes
public import Certificates.Kernel.SporSch.Ly.FiveSmall
public import Certificates.Kernel.SporSch.Ly.FiveRelT
public import Certificates.Kernel.SporSch.Ly.FiveRelR1
public import Certificates.Kernel.SporSch.Ly.Five8131
public import Certificates.Kernel.SporSch.Ly.NeId
public import CFSG.RankThree.Native.LyFiveCheckInputs
public import CFSG.Certificates.Kernel.Spor.RawSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.LyFR

open CFSG.KC.Enum CFSG.KS CFSG.KC.Ord CFSG.KS.SporSch.LyM CFSG.KD.OrdLy CFSG.KC.LyFiveRel
open CFSG.RankThree.Native CFSG.Sporadic.He.Native CFSG.Sporadic.Ly.Native CFSG.Sporadic.LySchreier.Native
open CertificateChecks.KernelSporSch.LyBS CertificateChecks.KernelSporSch.LyBSF
open CertificateChecks.KernelSporSch.LyFL (pw V nfL powE v_eq aa_eq bb_eq x_eq vAA vBB vXX nf_eq)

local notation "U" X:max => unpackL 111 12 1332 X

theorem powB {X : Nat} (hX : vld X = true) (e : Nat) :
    (powM 5 111 (U X) e == idM 111) = Nat.beq (pw X e) ONE :=
  LyNe.powB hX e

theorem neId {X : Nat} (hX : vld X = true) : lyNeId (U X) = !Nat.beq X ONE := LyNe.neId hX

theorem chkV_eq (i : Fin 4) : lyFiveChkV i = LyFL.chkVL i := by
  obtain ⟨r, v⟩ := v_eq i
  unfold lyFiveChkV LyFL.chkVL
  rw [r, x_eq, powB v, mulE vXX v, mulE v vXX, beqE (mulV vXX v) (mulV v vXX)]
  all_goals rfl

theorem chkComm_eq (i j : Fin 4) : lyFiveChkComm i j = LyFL.chkCommL i j := by
  obtain ⟨ri, vi⟩ := v_eq i
  obtain ⟨rj, vj⟩ := v_eq j
  obtain ⟨pi, qi⟩ := powE vi 4
  obtain ⟨pj, qj⟩ := powE vj 4
  obtain ⟨px, qx⟩ := powE vXX (lyFiveOmega i j).val
  unfold lyFiveChkComm LyFL.chkCommL
  rw [ri, rj, x_eq, pi, pj, px, mulE vi vj, mulE (mulV vi vj) qi, mulE (mulV (mulV vi vj) qi) qj,
    beqE (mulV (mulV (mulV vi vj) qi) qj) qx]

theorem chkConj_eq (i : Fin 4) : lyFiveChkConj i = LyFL.chkConjL i := by
  obtain ⟨r, v⟩ := v_eq i
  obtain ⟨na, va⟩ := nf_eq (lyFiveAlpha i).val fun j => (lyFiveAbar j i).val
  obtain ⟨nb, vb⟩ := nf_eq (lyFiveBeta i).val fun j => (lyFiveBbar j i).val
  unfold lyFiveChkConj LyFL.chkConjL
  rw [r, aa_eq, bb_eq, na, nb, mulE vAA v, mulE va vAA, mulE vBB v, mulE vb vBB,
    beqE (mulV vAA v) (mulV va vAA), beqE (mulV vBB v) (mulV vb vBB)]
  all_goals rfl

theorem small : lyFiveSmallCheck = true := by
  have eV : lyFiveChkV = LyFL.chkVL := funext chkV_eq
  have eC : lyFiveChkComm = LyFL.chkCommL := funext fun i => funext (chkComm_eq i)
  have eJ : lyFiveChkConj = LyFL.chkConjL := funext chkConj_eq
  unfold lyFiveSmallCheck lyFiveChkA25 lyFiveChkX lyFiveChkB8 lyFiveChkB4 lyFiveChkBX
  rw [eV, eC, eJ, aa_eq, bb_eq, x_eq, powB vAA 25, powB vBB 8, (powE vBB 4).1,
    neId (powE vBB 4).2, neId vXX, (powE vXX 2).1, mulE vBB vXX, mulE (powE vXX 2).2 vBB,
    beqE (mulV vBB vXX) (mulV (powE vXX 2).2 vBB)]
  simp only [LyFL.sA25, LyFL.sX, LyFL.sB8, LyFL.sB4, LyFL.sBX, LyFL.sV, LyFL.sComm, LyFL.sConj,
    Bool.and_self]

theorem next_eq : lyFiveNextArr = CFSG.KS.Raw.unpack 5760 12 (LyFRN.F 0) := by
  have h := CFSG.KC.Misc.HexFlat.hexTable3_sound LyFRN.all 0 (by norm_num)
  rw [Nat.mul_zero, ← LyFRN.eq] at h
  exact h

theorem q_eq : lyFiveQArr = CFSG.KS.Raw.unpack 5760 12 (LyFRQ.F 0) := by
  have h := CFSG.KC.Misc.HexFlat.hexTable3_sound LyFRQ.all 0 (by norm_num)
  rw [Nat.mul_zero, ← LyFRQ.eq] at h
  exact h

theorem par_get {k : Nat} (hk : k < 2880) : lyFiveParArr[k]! = ix (LyFTP.F 0) k := by
  rw [LyFT.par_eq, CFSG.KS.LyFiveTb.unpack_get hk]; rfl

theorem gen_get {k : Nat} (hk : k < 2880) : lyFiveGenArr[k]! = ix (LyFTG.F 0) k := by
  rw [LyFT.gen_eq, CFSG.KS.LyFiveTb.unpack_get hk]; rfl

theorem next_get {t : Nat} (ht : t < 5760) : lyFiveNextArr[t]! = ix (LyFRN.F 0) t := by
  rw [next_eq, CFSG.KS.LyFiveTb.unpack_get ht]; rfl

theorem q_get {t : Nat} (ht : t < 5760) : lyFiveQArr[t]! = ix (LyFRQ.F 0) t := by
  rw [q_eq, CFSG.KS.LyFiveTb.unpack_get ht]; rfl

theorem tAll : ∀ k < 2880, tAt mul LyFL.D.AA LyFL.D.BB ONE (LyFTP.F 0) (LyFTG.F 0) TT k = true := by
  intro k hk
  have hall : ∀ g < 45, tBlk g = true := LyFRT.all
  have h := CFSG.KC.Pack.allBlk_spec (hall (k / 64) (by omega)) (k % 64) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul 64 (k / 64)) (k % 64) = k := Nat.div_add_mod k 64
  rwa [e] at h

theorem andOf' {a b : Bool} (h : Bool.rec (motive := fun _ => Bool) false b a = true) :
    a = true ∧ b = true := LyBSF.andOf h

theorem tArr_get : ∀ k < 2880, lyFiveTArr[k]! = U (TT k) ∧ vld (TT k) = true := by
  have key : ∀ n ≤ 2880, ∀ k < n,
      (Nat.fold n (fun k _ acc => acc.push (lyFiveTStep k acc)) #[])[k]! = U (TT k) ∧
        vld (TT k) = true := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn k hk
      rw [CFSG.KS.LyFiveTb.fold_push_get _ n k hk]
      have hk' : k < 2880 := by omega
      have h := tAll k hk'
      unfold tAt at h
      by_cases h0 : k = 0
      · subst h0
        have e : TT 0 = ONE := Nat.eq_of_beq_eq_true h
        unfold lyFiveTStep
        rw [if_pos rfl, e, idE]
        exact ⟨rfl, vOne⟩
      · have hb : Nat.beq k 0 = false := Bool.eq_false_iff.mpr fun e => h0 (Nat.eq_of_beq_eq_true e)
        rw [hb] at h
        obtain ⟨h1, h2⟩ := andOf' h
        obtain ⟨h2, h3⟩ := andOf' h2
        have hpk := Nat.blt_eq.mp h1
        have es : ∀ acc, lyFiveTStep k acc = mulM 5 111 (if lyFiveGenArr[k]! = 1 then lyFiveBArr
            else lyFiveAArr) acc[lyFiveParArr[k]!]! := fun acc => by
          unfold lyFiveTStep
          rw [if_neg h0]
        obtain ⟨rp, vp⟩ := ih k hk (by omega) _ hpk
        rw [es, par_get hk', gen_get hk', rp, Nat.eq_of_beq_eq_true h3]
        by_cases hg : ix (LyFTG.F 0) k = 1
        · have hb1 : Nat.beq (ix (LyFTG.F 0) k) 1 = true := by rw [hg]; rfl
          rw [if_pos hg, bb_eq, mulE vBB vp, hb1]
          exact ⟨rfl, mulV vBB vp⟩
        · have hb1 : Nat.beq (ix (LyFTG.F 0) k) 1 = false :=
            Bool.eq_false_iff.mpr fun e => hg (Nat.eq_of_beq_eq_true e)
          rw [if_neg hg, aa_eq, mulE vAA vp, hb1]
          exact ⟨rfl, mulV vAA vp⟩
  exact key 2880 le_rfl

theorem vp_eq {i e : Nat} (hi : i < 4) (he : e < 5) : VP (5 * i + e) = pw (V i) e := by
  have hall : ∀ u < 20, Nat.beq (VP u) (pw (V (Nat.div u 5)) (Nat.mod u 5)) = true :=
    CFSG.KC.Pack.allN_spec vp
  have h := hall (5 * i + e) (by omega)
  have e1 : Nat.div (5 * i + e) 5 = i := by change (5 * i + e) / 5 = i; omega
  have e2 : Nat.mod (5 * i + e) 5 = e := by change (5 * i + e) % 5 = e; omega
  rw [e1, e2] at h
  exact Nat.eq_of_beq_eq_true h

theorem vpow_get {i e : Nat} (hi : i < 4) (he : e < 5) :
    (lyFiveVPow i)[e]! = U (VP (5 * i + e)) ∧ vld (VP (5 * i + e)) = true := by
  obtain ⟨r, v⟩ := v_eq ⟨i, hi⟩
  unfold lyFiveVPow
  rw [ofFn_get! _ he, vp_eq hi he]
  simp only at r v ⊢
  rw [r]
  exact powE v e

theorem xpow_get {c : Nat} (hc : c < 5) : lyFiveXPow[c]! = U (XP c) ∧ vld (XP c) = true := by
  have h := Nat.eq_of_beq_eq_true (CFSG.KC.Pack.allN_spec xp c hc)
  unfold lyFiveXPow
  rw [ofFn_get! _ hc, h]
  simp only
  rw [x_eq]
  exact powE vXX c

theorem pa_get {u : Nat} (hu : u < 25) : lyFiveP32[u]! = U (PA u) ∧ vld (PA u) = true := by
  have h : PA u = mul (VP (15 + u / 5)) (VP (10 + u % 5)) :=
    Nat.eq_of_beq_eq_true (CFSG.KC.Pack.allN_spec pa u hu)
  obtain ⟨r1, v1⟩ := vpow_get (i := 3) (e := u / 5) (by norm_num) (by omega)
  obtain ⟨r2, v2⟩ := vpow_get (i := 2) (e := u % 5) (by norm_num) (Nat.mod_lt _ (by norm_num))
  have e1 : 5 * 3 + u / 5 = 15 + u / 5 := by omega
  have e2 : 5 * 2 + u % 5 = 10 + u % 5 := by omega
  rw [e1] at r1 v1
  rw [e2] at r2 v2
  unfold lyFiveP32 lyFiveP3 lyFiveVPow2
  rw [ofFn_get! _ hu]
  simp only
  rw [r1, r2, mulE v1 v2, h]
  exact ⟨rfl, mulV v1 v2⟩

theorem pb_get {u : Nat} (hu : u < 125) : lyFiveP321[u]! = U (PB u) ∧ vld (PB u) = true := by
  have h : PB u = mul (PA (u / 5)) (VP (5 + u % 5)) :=
    Nat.eq_of_beq_eq_true (CFSG.KC.Pack.allN_spec pb u hu)
  obtain ⟨r1, v1⟩ := pa_get (u := u / 5) (by omega)
  obtain ⟨r2, v2⟩ := vpow_get (i := 1) (e := u % 5) (by norm_num) (Nat.mod_lt _ (by norm_num))
  have e2 : 5 * 1 + u % 5 = 5 + u % 5 := by omega
  rw [e2] at r2 v2
  unfold lyFiveP321 lyFiveVPow1
  rw [ofFn_get! _ hu]
  simp only
  rw [r1, r2, mulE v1 v2, h]
  exact ⟨rfl, mulV v1 v2⟩

theorem pc_get {u : Nat} (hu : u < 625) : lyFiveP3210[u]! = U (PC u) ∧ vld (PC u) = true := by
  have h : PC u = mul (PB (u / 5)) (VP (u % 5)) :=
    Nat.eq_of_beq_eq_true (CFSG.KC.Pack.allN_spec pc u hu)
  obtain ⟨r1, v1⟩ := pb_get (u := u / 5) (by omega)
  obtain ⟨r2, v2⟩ := vpow_get (i := 0) (e := u % 5) (by norm_num) (Nat.mod_lt _ (by norm_num))
  have e2 : 5 * 0 + u % 5 = u % 5 := by omega
  rw [e2] at r2 v2
  unfold lyFiveP3210 lyFiveVPow0
  rw [ofFn_get! _ hu]
  simp only
  rw [r1, r2, mulE v1 v2, h]
  exact ⟨rfl, mulV v1 v2⟩

theorem nf_get {q : Nat} (hq : q < 3125) : lyFiveNFArr q = U (NF q) ∧ vld (NF q) = true := by
  obtain ⟨r1, v1⟩ := pc_get (u := q / 5) (by omega)
  obtain ⟨r2, v2⟩ := xpow_get (c := q % 5) (Nat.mod_lt _ (by norm_num))
  unfold lyFiveNFArr NF
  rw [r1, r2, mulE v1 v2]
  exact ⟨rfl, mulV v1 v2⟩

theorem relAll : ∀ k < 2880, relK k = true := by
  intro k hk
  have hall0 : ∀ g < 45, relBlk g = true := LyFRR0.all
  have hall1 : ∀ g < 45, relBlk1 g = true := LyFRR1.all
  by_cases h : k < 1440
  · have h1 := CFSG.KC.Pack.allBlk_spec (hall0 (k / 32) (by omega)) (k % 32)
      (Nat.mod_lt _ (by norm_num))
    have e : Nat.add (Nat.mul 32 (k / 32)) (k % 32) = k := Nat.div_add_mod k 32
    rwa [e] at h1
  · have h1 := hall1 ((k - 1440) / 32) (by omega)
    unfold relBlk1 relBlk at h1
    have h2 := CFSG.KC.Pack.allBlk_spec h1 (k % 32) (Nat.mod_lt _ (by norm_num))
    have e : Nat.add (Nat.mul 32 (Nat.add 45 ((k - 1440) / 32))) (k % 32) = k := by
      change 32 * (45 + (k - 1440) / 32) + k % 32 = k
      omega
    rwa [e] at h2

theorem rel_sound {k s : Nat} (hk : k < 2880) (hs : s < 2)
    (h : relAt mul LyFL.D.AA LyFL.D.BB (LyFTP.F 0) (LyFTG.F 0) (LyFRN.F 0) (LyFRQ.F 0) TT NF k s = true) :
    lyFiveRelOK k s = true := by
  unfold relAt at h
  beta_reduce at h
  have ht : 2 * k + s < 5760 := by omega
  have et : Nat.add (Nat.mul 2 k) s = 2 * k + s := rfl
  rw [et] at h
  obtain ⟨hn, h⟩ := andOf' h
  obtain ⟨hq, h⟩ := andOf' h
  have hn' := Nat.blt_eq.mp hn
  have hq' := Nat.blt_eq.mp hq
  unfold lyFiveRelOK
  rw [next_get ht, q_get ht, par_get hn', gen_get hn']
  by_cases hr : relTree (LyFTP.F 0) (LyFTG.F 0) (LyFRN.F 0) (LyFRQ.F 0) k s = true
  · unfold relTree at hr
    beta_reduce at hr
    rw [et] at hr
    obtain ⟨a1, hr⟩ := andOf' hr
    obtain ⟨a2, hr⟩ := andOf' hr
    obtain ⟨a3, a4⟩ := andOf' hr
    have b1 := Nat.eq_of_beq_eq_true a1
    have b2 := Nat.eq_of_beq_eq_true a2
    have b4 := Nat.eq_of_beq_eq_true a4
    have b3 : ix (LyFRN.F 0) (2 * k + s) ≠ 0 := fun e => by rw [e] at a3; exact absurd a3 (by decide)
    simp [b1, b2, b3, b4]
  · have hf : relTree (LyFTP.F 0) (LyFTG.F 0) (LyFRN.F 0) (LyFRQ.F 0) k s = false := by
      simpa using hr
    rw [hf] at h
    obtain ⟨rk, vk⟩ := tArr_get k hk
    obtain ⟨rn, vn⟩ := tArr_get _ hn'
    obtain ⟨rq, vq⟩ := nf_get hq'
    have hG : (if s = 1 then lyFiveBArr else lyFiveAArr) =
        U (nIf(Nat.beq s 1, LyFL.D.BB, LyFL.D.AA)) ∧ vld (nIf(Nat.beq s 1, LyFL.D.BB, LyFL.D.AA)) = true := by
      by_cases h1 : s = 1
      · subst h1; exact ⟨by rw [if_pos rfl, bb_eq]; rfl, vBB⟩
      · have : Nat.beq s 1 = false := Bool.eq_false_iff.mpr fun e => h1 (Nat.eq_of_beq_eq_true e)
        rw [if_neg h1, this]
        exact ⟨aa_eq, vAA⟩
    obtain ⟨rg, vg⟩ := hG
    rw [rk, rn, rq, rg, mulE vg vk, mulE vn vq, beqE (mulV vg vk) (mulV vn vq)]
    simp only at h
    simp [h]

theorem rels : lyFiveRelsCheck = true := by
  unfold lyFiveRelsCheck
  rw [List.all_eq_true]
  intro k hk
  have hk' := List.mem_range.1 hk
  have h := relAll k hk'
  unfold relK at h
  obtain ⟨h0, h1⟩ := andOf' h
  rw [rel_sound hk' (by norm_num) h0, rel_sound hk' (by norm_num) h1]
  rfl

theorem tree : lyFiveTreeCheck = true := by
  unfold lyFiveTreeCheck
  have s1 : lyFiveParArr.size = 2880 := by rw [LyFT.par_eq]; simp [CFSG.KS.Raw.unpack]
  have s2 : lyFiveGenArr.size = 2880 := by rw [LyFT.gen_eq]; simp [CFSG.KS.Raw.unpack]
  have s3 : lyFiveNextArr.size = 5760 := by rw [next_eq]; simp [CFSG.KS.Raw.unpack]
  have s4 : lyFiveQArr.size = 5760 := by rw [q_eq]; simp [CFSG.KS.Raw.unpack]
  have t1 : ((List.range 2880).all fun k => k == 0 || (decide (lyFiveParArr[k]! < k) &&
      decide (lyFiveGenArr[k]! < 2))) = true := by
    rw [List.all_eq_true]
    intro k hk
    have hk' := List.mem_range.1 hk
    by_cases h0 : k = 0
    · simp [h0]
    · have h := tAll k hk'
      unfold tAt at h
      have hb : Nat.beq k 0 = false := Bool.eq_false_iff.mpr fun e => h0 (Nat.eq_of_beq_eq_true e)
      rw [hb] at h
      obtain ⟨h1, h2⟩ := andOf' h
      obtain ⟨h2, -⟩ := andOf' h2
      rw [par_get hk', gen_get hk']
      simp [Nat.blt_eq.mp h1, Nat.blt_eq.mp h2]
  have t2 : ((List.range 5760).all fun t => decide (lyFiveNextArr[t]! < 2880) &&
      decide (lyFiveQArr[t]! < 3125)) = true := by
    rw [List.all_eq_true]
    intro t ht
    have ht' := List.mem_range.1 ht
    have hk : t / 2 < 2880 := by omega
    have hs : t % 2 < 2 := Nat.mod_lt _ (by norm_num)
    have h := relAll (t / 2) hk
    unfold relK at h
    obtain ⟨h0, h1⟩ := andOf' h
    have hh : relAt mul LyFL.D.AA LyFL.D.BB (LyFTP.F 0) (LyFTG.F 0) (LyFRN.F 0) (LyFRQ.F 0) TT NF
        (t / 2) (t % 2) = true := by
      rcases Nat.mod_two_eq_zero_or_one t with e | e <;> rw [e] <;> assumption
    unfold relAt at hh
    beta_reduce at hh
    have et : Nat.add (Nat.mul 2 (t / 2)) (t % 2) = t := Nat.div_add_mod t 2
    rw [et] at hh
    obtain ⟨hn, hh⟩ := andOf' hh
    obtain ⟨hq, -⟩ := andOf' hh
    rw [next_get ht', q_get ht']
    simp [Nat.blt_eq.mp hn, Nat.blt_eq.mp hq]
  rw [s1, s2, s3, s4, t1, t2]
  rfl

end CertificateChecks.KernelSporSch.LyFR

end
