module

public import Certificates.Kernel.HSStd.PumpH43Checks
public import Certificates.Kernel.HSStd.PumpU3Glue
public import CFSG.Certificates.Kernel.ConjOrbSound
public import CFSG.Certificates.Kernel.Spor.HNAOrbSound
public import CFSG.Certificates.Kernel.Misc.ArrEnumOps
public import CFSG.Certificates.Kernel.Spor.PackFld

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelHSStd.PumpH43

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin
open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
open CFSG.EvenSporadicStandard.HSStd.FiveY CFSG.EvenSporadicStandard.HSStd.PumpTC7
open CFSG.ComponentClassification.HarrisLit.P1 (Row)
open CertificateChecks.KernelHSStd.PumpU3 (and_of enumOKL_of_enumOK)
open CFSG.KS.HNA (commP commutatorA_unpack)
open CFSG.KS.PinvS (permOK_pinvS)
open CFSG.Certificates.Native (rawInvs)

theorem arrCertOKL_of {act : ℕ → Array ℕ → Array ℕ} {ngen : ℕ}
    {valid : Array ℕ → Bool} {key : Array ℕ → ℕ} {root : Array ℕ} {c : ArrCert}
    (h : arrCertOK act ngen valid key root c = true) :
    arrCertOKL act ngen valid key root c = true := by
  simp only [arrCertOK, arrCertOKL, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  exact ⟨h.1, List.isChain_iff_pairwise.2 h.2⟩

theorem hps : ∀ p ∈ keys43, p < 80 := by decide

theorem nums' : D0.N = 720 ∧ D3.N = 720 ∧ D9.N = 720 ∧ C10.ng = 2 ∧ C10.N = 720 ∧ Q.ng = 2 ∧
    Q.N = 74880 ∧ Q.r0 < Q.N ∧ I0 0 < C10.N := by
  have h := nums
  simp only [Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq] at h
  tauto

theorem isOrd3_unpack {p : ℕ} (hp : PP 80 7 p) : isOrd3 (unpack 80 7 p) = ord3 p := by
  have h2 := hp.mul hp
  have h3 := hp.mul h2
  rw [isOrd3, idA_eq sz, eqA_PP hp (PP.id sz), compA_PP hp hp, compA_PP hp h2,
    eqA_PP h3 (PP.id sz)]
  rfl

theorem derOK_of {r : Row} {pairs : List (List Int × List Int)} {CG : ℕ → ℕ} {ng N : ℕ}
    {G T E S : ℕ → ℕ} {SK : List ℕ} (hs : (cgArr r).size = 2)
    (hcg : ∀ k < 2, (cgArr r)[k]! = unpack 80 7 (CG k)) (hg : derGensK CG pairs ng G = true)
    (hpG : ∀ k < ng, pk (G k) = true) (hk : bfsK 80 7 ng G N T E S = true)
    (hK : keysSK 80 7 keys43 N T SK = true) (hN : N = 720) : derOK43 r pairs = true := by
  unfold derGensK at hg
  obtain ⟨hg1, hw⟩ := and_of hg
  obtain ⟨hg2, hl⟩ := and_of hg1
  obtain ⟨hp0, hp1⟩ := and_of hg2
  have hl' : pairs.length = ng := Nat.eq_of_beq_eq_true hl
  have hpk : ∀ k < 2, pk (CG k) = true := fun k hk => by
    interval_cases k
    exacts [hp0, hp1]
  have hperm : allN 2 (fun j => permOK 80 7 (mask 7) (80 * 7) (CG j) (inv CG j)) = true :=
    CFSG.KS.PackFld.allN_of_forall fun j hj => hpk j hj
  have hS : (cgArr r).size = 2 ∧ ∀ j < 2, (cgArr r)[j]! = unpack 80 7 (CG j) := ⟨hs, hcg⟩
  have hwq : ∀ q < ng, (wordA 80 (cgArr r) (rawInvs 80 (cgArr r)) (pairs.getD q ([], [])).1 =
        unpack 80 7 (wv CG (pairs.getD q ([], [])).1) ∧
        lettersOK 2 (pairs.getD q ([], [])).1 = true) ∧
      (wordA 80 (cgArr r) (rawInvs 80 (cgArr r)) (pairs.getD q ([], [])).2 =
        unpack 80 7 (wv CG (pairs.getD q ([], [])).2) ∧
        lettersOK 2 (pairs.getD q ([], [])).2 = true) ∧
      G q = commP 80 7 (wv CG (pairs.getD q ([], [])).1) (wv CG (pairs.getD q ([], [])).2) := by
    intro q hq
    have h := allN_spec hw q hq
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    exact ⟨wordEqK_sound hS hperm h1, wordEqK_sound hS hperm h2, Nat.eq_of_beq_eq_true h3⟩
  have hwp : ∀ q < ng, ∀ i : Fin 2, PP 80 7 (wv CG (if i = 0 then (pairs.getD q ([], [])).1
      else (pairs.getD q ([], [])).2)) := by
    intro q hq i
    refine PP_of_permOK sz ?_
    have hl2 : ∀ wd, lettersOK 2 wd = true → permOK 80 7 (mask 7) (80 * 7) (wv CG wd)
        (pinvS 80 7 (mask 7) (wv CG wd)) = true := fun wd hwd =>
      CFSG.KC.Misc.ArrEnum.permB_wordK sz (j := 2) (fun h hh => hpk h hh)
        (fun h hh => CFSG.KC.Misc.ArrEnum.permB_pinvS sz (hpk h hh)) hwd
    split
    · exact hl2 _ (hwq q hq).1.2
    · exact hl2 _ (hwq q hq).2.1.2
  have hdc : (derComms r pairs).size = ng := by simp [derComms, hl']
  have hdg : ∀ q < ng, (derComms r pairs)[q]! = unpack 80 7 (G q) := by
    intro q hq
    have hq' : q < pairs.length := hl' ▸ hq
    have e : (derComms r pairs)[q]! = commutatorA 80
        (wordA 80 (cgArr r) (rawInvs 80 (cgArr r)) (pairs.getD q ([], [])).1)
        (wordA 80 (cgArr r) (rawInvs 80 (cgArr r)) (pairs.getD q ([], [])).2) := by
      simp [derComms, getElem!_def, hq', List.getD_eq_getElem?_getD]
    obtain ⟨⟨e1, -⟩, ⟨e2, -⟩, e3⟩ := hwq q hq
    rw [e, e1, e2, e3]
    exact (commutatorA_unpack (hwp q hq 0) (hwp q hq 1)).1
  have hok := enumOKL_of_enumOK (enumOK_of_bfsK_base (fuel := 800) hdc hdg hpG hk hps hK
    (by omega))
  have hpts := enumBfs_pts_base (fuel := 800) hdc hdg hk hps hK (by omega)
  have h1 : allLt (cgArr r).size (fun k => validA 80 (cgArr r)[k]!) = true := by
    rw [allLt_iff, hs]
    intro k hk
    rw [hcg k hk]
    exact validA_unpack (hpk k hk)
  have h2 : pairs.all (fun p => lettersOK (cgArr r).size p.1 && lettersOK (cgArr r).size p.2) =
      true := by
    rw [List.all_eq_true, hs]
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.getElem_of_mem hp
    have hq' : q < ng := hl' ▸ hq
    have e : pairs.getD q ([], []) = pairs[q] := List.getD_eq_getElem _ _ hq
    have := hwq q hq'
    rw [e] at this
    simp only [Bool.and_eq_true]
    exact ⟨this.1.2, this.2.1.2⟩
  have h3 : ((enumBfs 80 (derComms r pairs) keys43 800).pts.size == 720) = true := by
    rw [hpts, Array.size_ofFn, hN]
    rfl
  unfold derOK43 derCheck
  rw [h1, h2, hok, h3]
  rfl

theorem headD_filter_ofFn {α : Type} {N : ℕ} (f : Fin N → α) (p : α → Bool) (d : α) {i0 : ℕ}
    (hi : i0 < N) (hpre : ∀ i (h : i < i0), p (f ⟨i, by omega⟩) = false)
    (hp : p (f ⟨i0, hi⟩) = true) : ((List.ofFn f).filter p).headD d = f ⟨i0, hi⟩ := by
  have hlen : i0 < (List.ofFn f).length := by simpa using hi
  have e : List.ofFn f = (List.ofFn f).take i0 ++ (List.ofFn f).drop i0 :=
    (List.take_append_drop _ _).symm
  rw [e, List.drop_eq_getElem_cons hlen, List.filter_append]
  have hnil : ((List.ofFn f).take i0).filter p = [] := by
    rw [List.filter_eq_nil_iff]
    intro a ha
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha
    have hj' : j < i0 := by simp at hj; omega
    rw [List.getElem_take, List.getElem_ofFn]
    simp [hpre j hj']
  rw [hnil, List.nil_append, List.getElem_ofFn, List.filter_cons, hp]
  rfl

theorem survOK_of {r : Row} (hs : (cgArr r).size = 2)
    (hcg : ∀ k < 2, (cgArr r)[k]! = unpack 80 7 (C10.G k))
    (hgs : ∀ k < 2, gsP[k]! = unpack 80 7 (Q.G k)) : survOK43 r = true := by
  have n := nums'
  have hpd := permD
  simp only [Bool.and_eq_true] at hpd
  obtain ⟨⟨⟨⟨-, -⟩, -⟩, hpC⟩, hpQ⟩ := hpd
  have hng : (cgArr r).size = C10.ng := by rw [hs, n.2.2.2.1]
  have hget : ∀ k < C10.ng, (cgArr r)[k]! = unpack 80 7 (C10.G k) := fun k hk =>
    hcg k (n.2.2.2.1 ▸ hk)
  have hpG : ∀ k < C10.ng, pk (C10.G k) = true := fun k hk =>
    allN_spec hpC k (n.2.2.2.1 ▸ hk)
  have hpts := enumBfs_pts_base (fuel := 800) hng hget C10.ok hps kC10 (by rw [n.2.2.2.2.1]; omega)
  have hok := enumOKL_of_enumOK (enumOK_of_bfsK_base (fuel := 800) hng hget hpG C10.ok hps kC10
    (by rw [n.2.2.2.2.1]; omega))
  have hPT : ∀ i < C10.N, PP 80 7 (C10.T i) := PP_pts C10.ok hpG
  obtain ⟨hr12, hr3⟩ := and_of root
  obtain ⟨hr1', hr2⟩ := and_of hr12
  have hr1 := Nat.eq_of_beq_eq_true hr1'
  have hI := n.2.2.2.2.2.2.2.2
  have hx0 : ((enumBfs 80 (cgArr r) keys43 800).pts.toList.filter isOrd3).headD (idA 80) =
      unpack 80 7 (C10.T (I0 0)) := by
    rw [hpts, Array.toList_ofFn]
    refine headD_filter_ofFn _ _ _ hI (fun i hi => ?_) ?_
    · rw [isOrd3_unpack (hPT i (by omega))]
      have := allN_spec hr3 i hi
      simpa using this
    · rw [isOrd3_unpack (hPT _ hI)]
      exact hr2
  have hpx : PP 80 7 (C10.T (I0 0)) := hPT _ hI
  have hgsz : gsP.size = 2 := by simp [gsP, CFSG.ComponentClassification.HarrisLit.P1.L43.pgTbls]
  have horb' := CFSG.KC.ConjOrb.arrBfs_of_orb (ng := 2) (ngc := Q.ng) (fuel := 80000)
    (act := fun k a => conjA 80 gsP[k]! a) (root := unpack 80 7 (C10.T (I0 0))) (gs := gsP)
    (ps := keys43) (by rw [n.2.2.2.2.2.1]) hgs (fun _ _ _ => rfl)
    Q.h Q.cl Q.tr0 n.2.2.2.2.2.2.2.1 (by rw [hr1]) (validA_unpack (permOK_pinvS hpx.1 hpx.2))
    hps Q.k (by norm_num)
  have horb : arrCertOK (fun k a => conjA 80 gsP[k]! a) gsP.size (validA 80) (keyA 80 keys43)
      (unpack 80 7 (C10.T (I0 0))) (arrBfs (fun k a => conjA 80 gsP[k]! a) gsP.size
        (keyA 80 keys43) (unpack 80 7 (C10.T (I0 0))) 80000) = true ∧
      (∀ x, x ∈ (arrBfs (fun k a => conjA 80 gsP[k]! a) gsP.size (keyA 80 keys43)
        (unpack 80 7 (C10.T (I0 0))) 80000).pts ↔ ∃ i < Q.N, unpack 80 7 (Q.T i) = x) ∧
      (arrBfs (fun k a => conjA 80 gsP[k]! a) gsP.size (keyA 80 keys43)
        (unpack 80 7 (C10.T (I0 0))) 80000).pts.size = Q.N := by
    rw [hgsz]
    exact horb'
  have h2 : allLt gsP.size (fun k => validA 80 gsP[k]!) = true := by
    rw [allLt_iff, hgsz]
    intro k hk
    rw [hgs k hk]
    exact validA_unpack (allN_spec hpQ k hk)
  have h3 : isOrd3 (unpack 80 7 (C10.T (I0 0))) = true := by
    rw [isOrd3_unpack hpx]
    exact hr2
  have h4 := arrCertOKL_of horb.1
  have h5 : ((arrBfs (fun k a => conjA 80 gsP[k]! a) gsP.size (keyA 80 keys43)
      (unpack 80 7 (C10.T (I0 0))) 80000).pts.size == 74880) = true := by
    rw [horb.2.2, n.2.2.2.2.2.2.1]
    rfl
  have h6 : (enumBfs 80 (cgArr r) keys43 800).pts.toList.all (fun a => !isOrd3 a ||
      (arrBfs (fun k a => conjA 80 gsP[k]! a) gsP.size (keyA 80 keys43)
        (unpack 80 7 (C10.T (I0 0))) 80000).pts.toList.any (eqA 80 a)) = true := by
    rw [hpts, Array.toList_ofFn, List.all_eq_true]
    intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 ha
    rw [isOrd3_unpack (hPT i i.2)]
    have hw := allN_spec wQ i i.2
    cases e : ord3 (C10.T i)
    · rfl
    · rw [e] at hw
      simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hw
      obtain ⟨hlt, heq⟩ := hw
      have hmem := (horb.2.1 (unpack 80 7 (Q.T (QW i)))).2 ⟨_, hlt, rfl⟩
      have hc := (CFSG.KC.ConjOrb.closPt_spec (Q.cl _ hlt)).1
      simp only [Bool.not_true, Bool.false_or, List.any_eq_true, Array.mem_toList_iff]
      refine ⟨_, hmem, ?_⟩
      rw [heq, eqA_unpack (heq ▸ hc) (heq ▸ hc), Nat.beq_refl]
  simp only [survOK43, survCheck]
  rw [hx0, hok, h2, h3, h4, h5, h6]
  rfl

@[expose] def rowAt (j : ℕ) : Row :=
  match rows43[j]? with
  | some r => r
  | none => ⟨⟨#[], false, 0, 0, [], [], []⟩, .noFive⟩

theorem cg0_0 : (cgArr (rowAt 0))[0]! = unpack 80 7 (CG0 0) := by decide +kernel
theorem cg0_1 : (cgArr (rowAt 0))[1]! = unpack 80 7 (CG0 1) := by decide +kernel
theorem cg3_0 : (cgArr (rowAt 3))[0]! = unpack 80 7 (CG3 0) := by decide +kernel
theorem cg3_1 : (cgArr (rowAt 3))[1]! = unpack 80 7 (CG3 1) := by decide +kernel
theorem cg9_0 : (cgArr (rowAt 9))[0]! = unpack 80 7 (CG9 0) := by decide +kernel
theorem cg9_1 : (cgArr (rowAt 9))[1]! = unpack 80 7 (CG9 1) := by decide +kernel
theorem cg10_0 : (cgArr (rowAt 10))[0]! = unpack 80 7 (C10.G 0) := by decide +kernel
theorem cg10_1 : (cgArr (rowAt 10))[1]! = unpack 80 7 (C10.G 1) := by decide +kernel
theorem gs_0 : gsP[0]! = unpack 80 7 (Q.G 0) := by decide +kernel
theorem gs_1 : gsP[1]! = unpack 80 7 (Q.G 1) := by decide +kernel

theorem two {P : ℕ → Prop} (h0 : P 0) (h1 : P 1) : ∀ k < 2, P k := by
  intro k hk
  interval_cases k
  exacts [h0, h1]

theorem find0 : derPairs.find? (fun p => p.1 == (rowAt 0).row.rep) = some (derPairs.getD 0 (#[], [])) := by
  decide +kernel
theorem find3 : derPairs.find? (fun p => p.1 == (rowAt 3).row.rep) = some (derPairs.getD 1 (#[], [])) := by
  decide +kernel
theorem find9 : derPairs.find? (fun p => p.1 == (rowAt 9).row.rep) = some (derPairs.getD 2 (#[], [])) := by
  decide +kernel

theorem rowOK_der {j q : ℕ} (hc : (rowAt j).row.centOrder = 2880)
    (hf : derPairs.find? (fun p => p.1 == (rowAt j).row.rep) = some (derPairs.getD q (#[], [])))
    (h : derOK43 (rowAt j) (pairsOf q) = true) : rowOK43 (rowAt j) = true := by
  unfold rowOK43
  rw [hc, hf]
  simp only [pairsOf] at h
  simp only [List.getD_eq_getElem?_getD] at h
  simp [h]

theorem permD' : (∀ k < D0.ng, pk (D0.G k) = true) ∧ (∀ k < D3.ng, pk (D3.G k) = true) ∧
    ∀ k < D9.ng, pk (D9.G k) = true := by
  have h := permD
  simp only [Bool.and_eq_true] at h
  exact ⟨allN_spec h.1.1.1.1, allN_spec h.1.1.1.2, allN_spec h.1.1.2⟩

theorem row0 : rowOK43 (rowAt 0) = true :=
  rowOK_der (by decide +kernel) find0 (derOK_of rfl (two cg0_0 cg0_1) gD0 permD'.1 D0.ok kD0
    nums'.1)

theorem row3 : rowOK43 (rowAt 3) = true :=
  rowOK_der (by decide +kernel) find3 (derOK_of rfl (two cg3_0 cg3_1) gD3 permD'.2.1 D3.ok kD3
    nums'.2.1)

theorem row9 : rowOK43 (rowAt 9) = true :=
  rowOK_der (by decide +kernel) find9 (derOK_of rfl (two cg9_0 cg9_1) gD9 permD'.2.2 D9.ok kD9
    nums'.2.2.1)

theorem row10 : rowOK43 (rowAt 10) = true := by
  have h := survOK_of (r := rowAt 10) rfl (two cg10_0 cg10_1) (two gs_0 gs_1)
  have hc : (rowAt 10).row.centOrder = 720 := by decide +kernel
  unfold rowOK43
  rw [hc]
  simp [h]

theorem row1 : rowOK43 (rowAt 1) = true := by decide +kernel
theorem row2 : rowOK43 (rowAt 2) = true := by decide +kernel
theorem row4 : rowOK43 (rowAt 4) = true := by decide +kernel
theorem row5 : rowOK43 (rowAt 5) = true := by decide +kernel
theorem row6 : rowOK43 (rowAt 6) = true := by decide +kernel
theorem row7 : rowOK43 (rowAt 7) = true := by decide +kernel
theorem row8 : rowOK43 (rowAt 8) = true := by decide +kernel

theorem rows43_length : rows43.length = 11 := by
  simp [rows43, CFSG.ComponentClassification.HarrisLit.P1.L43.l43Runs,
    CFSG.ComponentClassification.HarrisLit.P1.L43.runuD,
    CFSG.ComponentClassification.HarrisLit.P1.L43.runuS,
    CFSG.ComponentClassification.HarrisLit.P1.L43.runuDS]

theorem rowAt_eq {j : ℕ} (hj : j < rows43.length) : rows43[j] = rowAt j := by
  simp only [rowAt, List.getElem?_eq_getElem hj]

theorem all_rows : ∀ j < 11, rowOK43 (rowAt j) = true := by
  intro j hj
  interval_cases j
  exacts [row0, row1, row2, row3, row4, row5, row6, row7, row8, row9, row10]

theorem h43OK_true : h43OK = true := by
  have h1 : (rows43.length == 11) = true := by rw [rows43_length]; rfl
  have h2 : rows43.all rowOK43 = true := by
    rw [List.all_eq_true]
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
    rw [rowAt_eq hj]
    exact all_rows j (rows43_length ▸ hj)
  unfold h43OK
  rw [h1, h2]
  rfl

end CertificateChecks.KernelHSStd.PumpH43

end
