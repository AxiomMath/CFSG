module

public import Certificates.Data.D4HexAutCheck
public import Certificates.Kernel.S63K.HChecks
public import Certificates.Kernel.S63K.HBindGlue
public import Certificates.Kernel.S63K.A21112
public import CFSG.Certificates.Kernel.S63K.SortSound
import CFSG.Monster.B.Co2.PermArr
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option exponentiation.threshold 600

namespace CertificateChecks.KernelS63.H4240

open CFSG.D4Hex CFSG.LargeExtraspecial.S63 CFSG.KC.S63K CFSG.KC.Co1F2 CFSG.KS.SporSch.M24
  CFSG.KC.Enum CFSG.KS CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CertificateChecks.KernelS63.HD

theorem word_get : ∀ w : List ℕ, (∀ k ∈ w, k < 8) → ∀ x < 819,
    (locWordArr w)[x]! = ptW w x ∧ ptW w x < 819
  | [], _, x, hx => by
    refine ⟨?_, hx⟩
    change (idA 819)[x]! = x
    unfold idA
    rw [getElem!_pos _ x (by simp [hx]), Array.getElem_ofFn]
  | k :: w, hw, x, hx => by
    obtain ⟨h1, h2⟩ := word_get w (fun k' hk' => hw k' (List.mem_cons_of_mem _ hk')) x hx
    have hk := hw k List.mem_cons_self
    have e : locWordArr (k :: w) = compA 819 permArrs[k]! (locWordArr w) := rfl
    have e2 : ptW (k :: w) x = im k (ptW w x) := rfl
    rw [e, compA_get' hx, h1, perm_get hk h2, e2]
    exact ⟨rfl, (pa_get hk h2).2⟩

theorem lnPt_eq {l t : ℕ} (hl : l < 2457) (ht : t < 3) : lnPt l t = lp l t ∧ lp l t < 819 :=
  lt_get (by omega)

theorem cw_parts : cWords.length = 4 ∧ ∀ w ∈ cWords, ∀ k ∈ w, k < 8 := by
  have h := cw
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  exact h

theorem stab_eq {w : List ℕ} (hw : ∀ k ∈ w, k < 8) {l : ℕ} (hl : l < 2457) :
    stabsLine (locWordArr w) l = stabK w l := by
  obtain ⟨e0, b0⟩ := lnPt_eq hl (t := 0) (by omega)
  obtain ⟨e1, b1⟩ := lnPt_eq hl (t := 1) (by omega)
  obtain ⟨e2, b2⟩ := lnPt_eq hl (t := 2) (by omega)
  unfold stabsLine onLine stabK onK
  rw [e0, e1, e2, (word_get w hw _ b0).1, (word_get w hw _ b1).1, (word_get w hw _ b2).1,
    beq_nat, beq_nat, beq_nat, beq_nat, beq_nat, beq_nat, beq_nat, beq_nat, beq_nat]

theorem any_congr {p q : ℕ → Bool} : ∀ {l : List ℕ}, (∀ x ∈ l, p x = q x) → l.any p = l.any q
  | [], _ => rfl
  | a :: l, h => by
    rw [List.any_cons, List.any_cons, h a List.mem_cons_self,
      any_congr fun x hx => h x (List.mem_cons_of_mem a hx)]

theorem line_ok : lineMoved = true := by
  unfold lineMoved
  refine allLt_iff.2 fun l hl => ?_
  have h := MatL.allN_iff.1 lineK l hl
  rw [cw_parts.1, beq_nat]
  rw [any_congr (q := fun k => !stabK (cWords.getD k []) l)]
  · exact h
  · intro k hk
    have hk' := List.mem_range.1 hk
    have hmem : cWords.getD k [] ∈ cWords := by
      rw [List.getD_eq_getElem _ _ (by rw [cw_parts.1]; exact hk')]
      exact List.getElem_mem _
    rw [stab_eq (cw_parts.2 _ hmem) hl]

theorem ug_chk : ((List.range 4).all fun l => uGens[l]! == unpackR 24 (UG l)) = true := by
  decide +kernel

theorem ug_size : uGens.size = 4 := by decide +kernel

theorem ug_eq : ∀ l < 4, uGens[l]! = unpackR 24 (UG l) := fun l hl => by
  have h := List.all_eq_true.1 ug_chk l (List.mem_range.2 hl)
  simpa using h

theorem g3_eq : (d4Gens[3]! == unpackR 24 G3) = true := by decide +kernel

noncomputable abbrev DT : EnumData := DkG TP TPar TLab 4096

theorem et_eq : locET = DT := by
  unfold locET
  exact mkEnum_of_K ug_size ug_eq repT

theorem eq_eq : locEQ = A21112.DQ := by
  unfold locEQ
  exact A21112.dq_eq

theorem t_lt : ∀ i < 4096, TP i < 2 ^ 576 := (bfsDistK_sound (bfsK_sound repT).2.2.2.2.1).1

theorem q_lt : ∀ i < 512, CertificateChecks.KernelS63.AD.QP i < 2 ^ 576 :=
  (bfsDistK_sound (bfsK_sound CertificateChecks.KernelS63.AD.repQ).2.2.2.2.1).1

theorem cj_eq {i : ℕ} (hi : i < 4096) :
    conjI (wordR d4Gens autQWord.reverse) (wordR d4Gens autQWord) DT.El[i]! = unpackR 24 (cj i) := by
  have hg : d4Gens[3]! = unpackR 24 G3 := by simpa using g3_eq
  have hw : wordR d4Gens [3] = unpackR 24 (mw G3 idP) := by
    change mulR d4Gens[3]! oneR = _
    rw [hg, oneR_eq, mulR_unpackR]
    rfl
  change conjI (wordR d4Gens [3]) (wordR d4Gens [3]) (ElG TP 4096)[i]! = _
  rw [hw, elG_get hi, conjI, mulR_unpackR, mulR_unpackR, unpackR_mod]
  rfl

theorem auto_all : ∀ i < 4096, autK i = true := by
  intro i hi
  have hc : autC (i / 64) = true := by
    have hb : i / 64 < 64 := by omega
    generalize i / 64 = b at hb
    interval_cases b
    exacts [autC0, autC1, autC2, autC3, autC4, autC5, autC6, autC7, autC8, autC9, autC10, autC11,
      autC12, autC13, autC14, autC15, autC16, autC17, autC18, autC19, autC20, autC21, autC22,
      autC23, autC24, autC25, autC26, autC27, autC28, autC29, autC30, autC31, autC32, autC33,
      autC34, autC35, autC36, autC37, autC38, autC39, autC40, autC41, autC42, autC43, autC44,
      autC45, autC46, autC47, autC48, autC49, autC50, autC51, autC52, autC53, autC54, autC55,
      autC56, autC57, autC58, autC59, autC60, autC61, autC62, autC63]
  have h := MatL.allN_iff.1 hc (i % 64) (Nat.mod_lt _ (by norm_num))
  rwa [Nat.div_add_mod] at h

theorem eqM_lt {A B : ℕ} (hA : A < 2 ^ 576) (hB : B < 2 ^ 576) : eqM A B = Nat.beq A B := by
  unfold eqM
  rw [Nat.mod_eq_of_lt hA, Nat.mod_eq_of_lt hB]

theorem autQ_ok : autQCheck locET locEQ = true := by
  rw [et_eq, eq_eq]
  unfold autQCheck
  simp only [Bool.and_eq_true]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · have e : autQWord = [3] := rfl
    rw [e, (word_get [3] (by decide) 0 (by norm_num)).1, beq_nat]
    exact fix0
  · have hsz : DT.El.size = 4096 := by simp [DkG, ElG]
    rw [hsz]
    refine allLt_iff.2 fun i hi => ?_
    have hk := auto_all i hi
    unfold autK at hk
    simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.beq_eq] at hk
    have hcj : cj i < 2 ^ 576 := Nat.mod_lt _ (by positivity)
    have hd := (bfsK_sound repT).2.2.2.2.1
    rw [cj_eq hi]
    change (!memR (ElG TP 4096) (lookup (mkIdx (ElG TP 4096))) (unpackR 24 (cj i)) ||
      memR A21112.DQ.El A21112.DQ.idx (ElG TP 4096)[i]!) = true
    rw [memR_eq ug_size ug_eq repT, elG_get hi, A21112.memQ_eq]
    rcases hk with h0 | ⟨_, h1⟩
    · have hn := memS_zero hd h0
      have : ((List.range 4096).any fun w => eqM (TP w) (cj i)) = false := by
        rw [List.any_eq_false]
        intro w hw
        have hw' := List.mem_range.1 hw
        rw [eqM_lt (t_lt w hw') hcj]
        simpa [Nat.beq_eq] using hn w hw'
      rw [this]
      rfl
    · obtain ⟨w, hw, he⟩ := memS_one (bfsK_sound CertificateChecks.KernelS63.AD.repQ).2.2.2.2.1 h1
      have : CertificateChecks.KernelS63.AD.memQ (TP i) = true := by
        unfold CertificateChecks.KernelS63.AD.memQ
        refine List.any_eq_true.2 ⟨w, List.mem_range.2 hw, ?_⟩
        rw [eqM_lt (q_lt w hw) (t_lt i hi), he, Nat.beq_refl]
      rw [this, Bool.or_true]

theorem c4240 : CFSG.D4Hex.autCheck = true := by
  unfold autCheck
  rw [line_ok, autQ_ok]
  rfl

end CertificateChecks.KernelS63.H4240

end
