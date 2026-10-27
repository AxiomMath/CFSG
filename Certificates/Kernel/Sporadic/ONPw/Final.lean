module

public import Certificates.Kernel.Sporadic.ONPw.Facts
public import Certificates.Kernel.Sporadic.ONPw.Rec0
public import Certificates.Kernel.Sporadic.ONPw.Rec1
public import Certificates.Kernel.Sporadic.ONPw.Paths
public import CFSG.RankThree.PartOne.KS.ONPwCheck
public import CFSG.Certificates.Kernel.Spor.DecSLProved
public import Certificates.Kernel.Sporadic.OddCore.ON2123

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONPw

open CFSG.KC.Enum CFSG.KS CFSG.KS.ONPw CFSG.KS.ONPv CFSG.KS.ONNQ CFSG.ONSchreier
open CertificateChecks.KernelSpor.ONPv CertificateChecks.KernelSpor.ON
open CFSG.RankThree.PartOne.ONPw (Facts concreteEnv liftWords nLifts yLetters bW zW y0W x0W kW)
open CFSG.Sporadic.ONOddCore (decodeCert QuotRecord LiftEntry)

theorem pw_items_main : wd (OPW.D 0) = zW ∧ wd (OPW.D 6) = y0W ∧ wd (OPW.D 7) = x0W ∧
    (∀ j < 4, wd (OPW.D (8 + j)) = kW j) ∧ wd (OPW.D 12) = bW ∧
    wd (OPW.D 61) = yLetters.map fun l : Nat => (l : Int) := by
  decide +kernel

theorem pw_items_lifts :
    (((decodeCert (CFSG.KS.DecSL.natsSL LocAutT.chars)).records.flatMap QuotRecord.lifts).map
        LiftEntry.words).map (fun ws => ws.map fun w => w.map fun l : Nat => (l : Int)) =
      (List.range 16).map fun q => (List.range 3).map fun j => wd (OPW.D (13 + 3 * q + j)) := by
  decide +kernel

theorem pw_lifts_idx {LW : List (List (List Nat))} {G : Nat → Nat → List Int}
    (h : LW.map (fun ws => ws.map fun w => w.map fun l : Nat => (l : Int)) =
      (List.range 16).map fun q => (List.range 3).map fun j => G q j) :
    LW.length = 16 ∧ ∀ q < 16, ∀ j < 3, ((LW[q]!)[j]!).map (fun l : Nat => (l : Int)) = G q j := by
  have hlen : LW.length = 16 := by simpa using congrArg List.length h
  refine ⟨hlen, fun q hq j hj => ?_⟩
  have h1 := List.getElem_of_eq h (i := q) (by simp; omega)
  simp only [List.getElem_map, List.getElem_range] at h1
  have hl3 : (LW[q]'(by omega)).length = 3 := by simpa using congrArg List.length h1
  have h2 := List.getElem_of_eq h1 (i := j) (by simp; omega)
  simp only [List.getElem_map, List.getElem_range] at h2
  rw [getElem!_pos LW q (by omega), getElem!_pos _ j (by omega)]
  exact h2

theorem pw_lifts : liftWords.length = 16 ∧ ∀ q < 16, ∀ j < 3,
    ((liftWords[q]!)[j]!).map (fun l : Nat => (l : Int)) = wd (OPW.D (13 + 3 * q + j)) := by
  have e : liftWords = ((decodeCert (CFSG.KS.DecSL.natsSL LocAutT.chars)).records.flatMap
      QuotRecord.lifts).map LiftEntry.words := by
    rw [CFSG.RankThree.PartOne.ONPw.liftWords, CFSG.Sporadic.ONOddCore.localCert, LocAutT.eq,
      CFSG.KS.DecSL.natsOf_ofList_proved ON2123.digits]
  rw [e]
  exact pw_lifts_idx pw_items_lifts

theorem wv_natW {n : Nat} {f : Nat → Equiv.Perm (Fin n)} {imgs : List (Equiv.Perm (Fin n))}
    (h : ∀ k < 3, imgs.getD k 1 = f k) : ∀ {w : List Nat},
    Lm 3 (w.map fun l : Nat => (l : Int)) →
      wv f (w.map fun l : Nat => (l : Int)) = CFSG.Sporadic.ONOddCore.evalPos imgs w
  | [], _ => by simp [wv, CFSG.Sporadic.ONOddCore.evalPos]
  | l :: w, hw => by
    simp only [List.map_cons] at hw ⊢
    obtain ⟨⟨h0, h3⟩, hw'⟩ := Lm_cons hw
    simp only [Int.natAbs_natCast] at h3
    have hp : (0 : Int) < (l : Int) := by omega
    have e : ((l : Int)).toNat - 1 = l - 1 := by omega
    rw [wv_cons, wv_natW h hw', lv, if_pos hp, e, ← h (l - 1) (by omega)]
    simp only [CFSG.Sporadic.ONOddCore.evalPos, List.map_cons, List.prod_cons]

theorem pw_nr' : OPW.D 70 = 224 := Nat.eq_of_beq_eq_true pw_nr

theorem pw_recs : ∀ r < OPW.D 70, recOK TT UU OPW.D r = true := by
  have hs : ∀ s < 14, recsOK TT UU OPW.D (16 * s) 16 = true := by
    intro s hs
    interval_cases s
    exacts [pw_r0, pw_r1, pw_r2, pw_r3, pw_r4, pw_r5, pw_r6, pw_r7, pw_r8, pw_r9, pw_r10, pw_r11,
      pw_r12, pw_r13]
  intro r hr
  rw [pw_nr'] at hr
  have h : recOK TT UU OPW.D (Nat.add (16 * (r / 16)) (r % 16)) = true :=
    allN_spec (hs (r / 16) (by omega)) (r % 16) (Nat.mod_lt _ (by omega))
  have e : Nat.add (16 * (r / 16)) (r % 16) = r := Nat.div_add_mod r 16
  rwa [e] at h

theorem pw_paths_all : ∀ r < OPW.D 70, pathEq OPW.D r = true := by
  intro r hr
  rw [pw_nr'] at hr
  exact allN_spec pw_paths r hr

theorem evalFP_wF (a k : Nat → CFSG.RankThree.PartOne.ONPw.PermN) :
    CFSG.RankThree.PartOne.ONPw.evalFP a k CFSG.RankThree.PartOne.ONPw.wF = fWP a k := by
  simp [CFSG.RankThree.PartOne.ONPw.evalFP, CFSG.RankThree.PartOne.ONPw.wF, fWP, mul_assoc]

section Facts


theorem hP_get : ∀ k < 3, concreteEnv.hP.getD k 1 = sI sgen OPW.D k := by
  intro k hk
  interval_cases k
  · rw [sI_eq (by omega) items_words.1]
    rfl
  · rw [sI_eq (by omega) items_words.2.1]
    rfl
  · rw [sI_eq (by omega) items_words.2.2.1]
    rfl

theorem pw_facts : Facts concreteEnv ∧ liftWords.length = nLifts := by
  obtain ⟨iz, iy0, ix0, ik, ib, iy⟩ := pw_items_main
  have W := CFSG.KS.ONPw.pw_words rp_on pw_items sgen_mem7 sep_pv pw_b0 pw_b1 pw_b2
  have hb : concreteEnv.bP = sI sgen OPW.D 12 := (sI_eq (by omega) ib).symm
  have hz : concreteEnv.zP = sI sgen OPW.D 0 := (sI_eq (by omega) iz).symm
  have hy0 : concreteEnv.y0P = sI sgen OPW.D 6 := (sI_eq (by omega) iy0).symm
  have hx0 : concreteEnv.x0P = sI sgen OPW.D 7 := (sI_eq (by omega) ix0).symm
  have hk : ∀ j < 4, concreteEnv.kP j = sI sgen OPW.D (8 + j) :=
    fun j hj => (sI_eq (by omega) (ik j hj)).symm
  have hxp : concreteEnv.xP = xp sgen OPW.D := by
    simp only [CFSG.RankThree.PartOne.ONPw.Env.xP, hb, hx0, xp, CFSG.KS.ONPw.cj]
  have hyp : concreteEnv.yP = yp sgen OPW.D := by
    simp only [CFSG.RankThree.PartOne.ONPw.Env.yP, hb, hy0, yp, CFSG.KS.ONPw.cj]
  have hkp : ∀ j < 4, concreteEnv.kpP j = kp sgen OPW.D j := by
    intro j hj
    simp only [CFSG.RankThree.PartOne.ONPw.Env.kpP, hb, hk j hj, kp, CFSG.KS.ONPw.cj]
  have hL61 : Lm 3 (yLetters.map fun l : Nat => (l : Int)) := by
    rw [← iy]
    exact pw_items.2 48 (by omega)
  have hlift : ∀ q < 16, ∀ j < 3, concreteEnv.liftImgP q j = bE sgen OPW.D q j := by
    intro q hq j hj
    have hw := pw_lifts.2 q hq j hj
    have hL : Lm 3 (((liftWords[q]!)[j]!).map fun l : Nat => (l : Int)) := by
      rw [hw]
      have h := pw_items.2 (3 * q + j) (by omega)
      rwa [← Nat.add_assoc] at h
    simp only [CFSG.RankThree.PartOne.ONPw.Env.liftImgP, bE, hV]
    rw [← hw]
    exact (wv_natW hP_get hL).symm
  have hImgs : ∀ q, ∀ k < 3, (concreteEnv.liftImgsP q).getD k 1 = concreteEnv.liftImgP q k := by
    intro q k hk
    simp only [CFSG.RankThree.PartOne.ONPw.Env.liftImgsP]
    interval_cases k <;> rfl
  have hby : ∀ q < 16, concreteEnv.byP q = bY sgen OPW.D q := by
    intro q hq
    simp only [CFSG.RankThree.PartOne.ONPw.Env.byP, bY]
    rw [iy]
    exact (wv_natW (fun k hk => (hImgs q k hk).trans (hlift q hq k hk)) hL61).symm
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [hb, hz, hy0]
    exact W.1
  · rw [hyp, W.2.1, hV, iy]
    exact wv_natW hP_get hL61
  · intro j hj
    rw [hxp, hkp j hj]
    change xp sgen OPW.D * kp sgen OPW.D j = kp sgen OPW.D j * xp sgen OPW.D
    have c := (W.2.2.1 j hj).eq
    have e : ∀ a c : Equiv.Perm (Fin 245520), (sI sgen OPW.D 12)⁻¹ * a * sI sgen OPW.D 12 *
        ((sI sgen OPW.D 12)⁻¹ * c * sI sgen OPW.D 12) =
        (sI sgen OPW.D 12)⁻¹ * (a * c) * sI sgen OPW.D 12 := by
      intro a c
      group
    simp only [xp, kp, CFSG.KS.ONPw.cj]
    rw [e, e, c]
  · obtain ⟨j, hj, h⟩ := (CFSG.KS.ONPw.pw_hd rp_on pw_items
      CertificateChecks.KernelSpor.ONPw.pw_hd).1
    refine ⟨j, hj, ?_⟩
    rw [hz, hkp j hj]
    exact h
  · rw [hx0]
    exact W.2.2.2.1
  · rw [hxp]
    exact xp_pow7 W.2.2.2.1
  · rw [evalFP_wF]
    have h := W.2.2.2.2
    simp only [fWP] at h ⊢
    rw [hP_get 0 (by omega), hP_get 2 (by omega), hkp 1 (by omega), hkp 2 (by omega),
      hkp 3 (by omega)]
    exact h
  · intro q hq l hl hc
    have hq16 : q < 16 := hq
    have hc' : l * bY sgen OPW.D q * l⁻¹ = yp sgen OPW.D := by
      rw [← hby q hq16, ← hyp]
      exact hc
    rcases pw_surv pw_treeH sgen_mem7 sep_pv W.2.1 (xp_pow7 W.2.2.2.1) pw_recs pw_paths_all hq16
      hl hc' with ⟨i, hi, h⟩ | h
    · refine Or.inl ⟨i, hi, fun j hj => ?_⟩
      rw [hlift q hq16 j hj, hxp, hP_get j hj]
      exact h j hj
    · refine Or.inr ?_
      rw [evalFP_wF]
      simp only [fWP] at h ⊢
      rw [hlift q hq16 0 (by omega), hlift q hq16 2 (by omega), hkp 1 (by omega),
        hkp 2 (by omega), hkp 3 (by omega)]
      exact h
  · exact pw_lifts.1

end Facts

end CertificateChecks.KernelSpor.ONPw

end
