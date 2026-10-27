module

public import Certificates.Kernel.HSStd.U43VbBase
public import Certificates.Kernel.HSStd.U43VbRC
public import Certificates.Kernel.HSStd.U43VbRT
public import Certificates.Kernel.HSStd.U43VbRK0
public import Certificates.Kernel.HSStd.U43VbRK1
public import Certificates.Kernel.HSStd.U43VbCov
public import Certificates.Kernel.HSStd.U43VbSol
public import Certificates.Kernel.HSStd.U43Z4Glue
import CFSG.Certificates.Kernel.BfsPinUnpack
import CFSG.Certificates.Kernel.BfsPinSetSound
import CFSG.Certificates.Kernel.BfsPinAlg
import CFSG.Certificates.Kernel.Spor.PackWord
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Common.ForallChunks
import CFSG.Certificates.Kernel.Spor.MulHCSound
import CFSG.Certificates.Kernel.Spor.MulHFSound
import CFSG.Certificates.Kernel.Spor.PEnumRSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHSStd.U43Vb

open CFSG.EvenSporadicStandard.HSStd.U43 CFSG.EvenSporadicStandard.M24Std.CU43
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Schreier.Native
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KC.BfsPin
open CFSG.KC.U43Case
open CFSG.Monster.B.Co2.Native CFSG.LieType.Multipliers.U43
open CertificateChecks.KernelHSStd
open CertificateChecks.KernelSpor (U43CoverK.inP_tab U43CoverK.gen_of U43CoverK.tP)
open CertificateChecks.KernelHSStd.U43Z4 (fa slAll peAll classOK_of enum_of coverP_spec tabsOf_get)

#kc_forall_chunks peC_all (fun s => peCR s = true) 30 CertificateChecks.KernelHSStd.U43Vb.peCR 1
#kc_forall_chunks hsC_all (fun s => hsCF s = true) 10 CertificateChecks.KernelHSStd.U43Vb.hsCF 1
#kc_forall_chunks clC_all (fun s => clCR s = true) 30 CertificateChecks.KernelHSStd.U43Vb.clCR 1
#kc_forall_chunks peY_all (fun s => peYR s = true) 24 CertificateChecks.KernelHSStd.U43Vb.peYR 1
#kc_forall_chunks hsY_all (fun s => hsYF s = true) 8 CertificateChecks.KernelHSStd.U43Vb.hsYF 1
#kc_forall_chunks clY_all (fun s => clYR s = true) 8 CertificateChecks.KernelHSStd.U43Vb.clYR 1
#kc_forall_chunks peT_all (fun s => peT s = true) 36 CertificateChecks.KernelHSStd.U43Vb.peT 1
#kc_forall_chunks hsT_all (fun s => hsT s = true) 8 CertificateChecks.KernelHSStd.U43Vb.hsT 1
#kc_forall_chunks peK_all (fun s => peK s = true) 60 CertificateChecks.KernelHSStd.U43Vb.peK 1
#kc_forall_chunks hsK_all (fun s => hsK s = true) 8 CertificateChecks.KernelHSStd.U43Vb.hsK 1
#kc_forall_chunks cv_all (fun s => cv s = true) 8 CertificateChecks.KernelHSStd.U43Vb.cv 1

theorem sz : szOK 820 10 = true := by
  have h := kSz
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1

theorem cg_size : vbCg.size = 5 := by
  have h := kSz
  simp only [Bool.and_eq_true] at h
  exact Nat.eq_of_beq_eq_true h.1.2

theorem yg_size : vbYg.size = 2 := by
  have h := kSz
  simp only [Bool.and_eq_true] at h
  exact Nat.eq_of_beq_eq_true h.2

theorem inF {i : Nat} (hi : i < 13) : cK (VbP i) = true ∧ cK (VbI i) = true ∧
    invEqK 820 10 (mask 10) (820 * 10) (VbP i) (VbI i) = true := by
  have h := allN_spec kIn i hi
  simp only [bAnd_iff] at h
  exact h

theorem tkF {k : Nat} (hk : k < 8) : cK (TK k) = true ∧
    permOK 820 10 (mask 10) (820 * 10) (TK k) (TKI k) = true := by
  have h := allN_spec kTK k hk
  simp only [bAnd_iff] at h
  exact h

theorem tkiC {k : Nat} (hk : k < 8) : cK (TKI k) = true :=
  (PP_of_permOK sz (tkF hk).2).inv.1

theorem ppw_eq {p : Nat} (hp : cK p = true) : ∀ e,
    powA 820 (unpack 820 10 p) e = unpack 820 10 (ppw 820 10 p e) ∧ cK (ppw 820 10 p e) = true
  | 0 => ⟨idA_eq sz, (PP.id sz).1⟩
  | e + 1 => by
    obtain ⟨h1, h2⟩ := ppw_eq hp e
    change compA 820 (unpack 820 10 p) (powA 820 (unpack 820 10 p) e) =
      unpack 820 10 (pp 820 10 p (ppw 820 10 p e)) ∧ cK (pp 820 10 p (ppw 820 10 p e)) = true
    rw [h1, compA_unpack hp h2]
    exact ⟨rfl, canonK_pcomp hp h2⟩

theorem tArr_eq (k : Nat) : tArr k = unpack 820 10 (TK k) := by
  obtain ⟨a1, a2⟩ := ppw_eq (inF (i := 11) (by decide)).1 (k / 4)
  obtain ⟨b1, b2⟩ := ppw_eq (inF (i := 12) (by decide)).1 (k % 4)
  unfold tArr TK
  rw [eq_unpack_of_bindListK kBind.2.2.2.2.2.2.2.2.2.2.2.1,
    eq_unpack_of_bindListK kBind.2.2.2.2.2.2.2.2.2.2.2.2, a1, b1, compA_unpack a2 b2]
  rfl

theorem memCos_of {X k : Nat} {ks : List Nat} (hX : cK X = true) (hk : k ∈ ks) (hk8 : k < 8)
    (hs : siftK 820 10 (mask 10) (820 * 10) (pidn 820 10) KernelU43B.C.LR KernelU43B.C.TRI
      KernelU43B.C.BP 3 0 (pc X (TKI k)) = true) :
    memCos ks (tabT (unpack 820 10 X)) = true := by
  obtain ⟨-, tp⟩ := tkF hk8
  have hxi : cK (pc X (TKI k)) = true := canonK_pcomp hX (tkiC hk8)
  unfold memCos
  rw [List.any_eq_true]
  refine ⟨k, hk, ?_⟩
  rw [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨hk8, ?_⟩
  rw [natArr_tabT hX, tArr_eq, invCand_unpack tp,
    show pinvS 820 10 (mask 10) (TK k) = TKI k from rfl, compA_unpack hX (tkiC hk8)]
  have := U43CoverK.inP_tab hxi hs
  unfold U43CoverK.tP at this
  rwa [natArr_tabT hxi] at this

theorem cos_of {i : Nat} (h2 : 2 ≤ i) (h10 : i ≤ 10) :
    memCos dVb.ks (tabT (unpack 820 10 (VbP i))) = true := by
  have h := allN_spec kCos (i - 2) (by omega)
  rw [show Nat.add (i - 2) 2 = i by change i - 2 + 2 = i; omega] at h
  unfold cosK at h
  rw [CFSG.KC.BfsPin.strictB_app] at h
  simp only [bAnd_iff, Bool.or_eq_true, Nat.beq_eq] at h
  have hk : VbK i = 0 ∨ VbK i = 2 ∨ VbK i = 5 ∨ VbK i = 7 := by
    rcases h.1 with ((h0 | h0) | h0) | h0 <;> omega
  exact memCos_of (inF (i := i) (by omega)).1
    (by change _ ∈ [0, 2, 5, 7]; simp only [List.mem_cons, List.not_mem_nil]; omega)
    (by omega) h.2

theorem tT : dVb.Tt = tb 820 10 (VbP 0) := by
  have : reps[8]! = rep8 := rfl
  change tabOf reps[8]! = _
  rw [this, eq_unpack_of_bindListK kBind.1]
  rfl

theorem tY : dVb.y0 = tb 820 10 (VbP 1) := by
  change tabOf vbY0 = _
  rw [eq_unpack_of_bindListK kBind.2.1]
  rfl

theorem cg_tabs : TabsOK 820 10 5 (fun j => VbP (Nat.add j 2)) dVb.cg := by
  refine ⟨by change (tabsOf vbCg).size = 5; simp [tabsOf, cg_size], fun j hj => ?_⟩
  refine ⟨?_, (inF (i := j + 2) (by omega)).1⟩
  change (tabsOf vbCg)[j]! = _
  rw [tabsOf_get (by rw [cg_size]; exact hj)]
  obtain ⟨-, -, b0, b1, b2, b3, b4, -⟩ := kBind
  have hb : vbCg[j]! = unpack 820 10 (VbP (j + 2)) := by
    match j, hj with
    | 0, _ => exact eq_unpack_of_bindListK b0
    | 1, _ => exact eq_unpack_of_bindListK b1
    | 2, _ => exact eq_unpack_of_bindListK b2
    | 3, _ => exact eq_unpack_of_bindListK b3
    | 4, _ => exact eq_unpack_of_bindListK b4
  rw [hb]
  rfl

theorem yg_tabs : TabsOK 820 10 2 (fun j => VbP (Nat.add j 7)) dVb.yg := by
  refine ⟨by change (tabsOf vbYg).size = 2; simp [tabsOf, yg_size], fun j hj => ?_⟩
  refine ⟨?_, (inF (i := j + 7) (by omega)).1⟩
  change (tabsOf vbYg)[j]! = _
  rw [tabsOf_get (by rw [yg_size]; exact hj)]
  obtain ⟨-, -, -, -, -, -, -, b0, b1, -⟩ := kBind
  have hb : vbYg[j]! = unpack 820 10 (VbP (j + 7)) := by
    match j, hj with
    | 0, _ => exact eq_unpack_of_bindListK b0
    | 1, _ => exact eq_unpack_of_bindListK b1
  rw [hb]
  rfl

theorem gens_tabs : TabsOK 820 10 4 GG dVb.gensG := by
  refine ⟨rfl, fun j hj => ?_⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, ba, bb, -⟩ := kBind
  match j, hj with
  | 0, _ => exact ⟨by
      change tabOf tabA = _
      rw [eq_unpack_of_bindListK ba]; rfl, (inF (i := 9) (by decide)).1⟩
  | 1, _ => exact ⟨by
      change tabOf tabB = _
      rw [eq_unpack_of_bindListK bb]; rfl, (inF (i := 10) (by decide)).1⟩
  | 2, _ => exact ⟨by
      change tabOf (tArr 2) = _
      rw [tArr_eq]; rfl, (tkF (k := 2) (by decide)).1⟩
  | 3, _ => exact ⟨by
      change tabOf (tArr 5) = _
      rw [tArr_eq]; rfl, (tkF (k := 5) (by decide)).1⟩

theorem gensI : ∀ j < 4, invEqK 820 10 (mask 10) (820 * 10) (GG j) (GGI j) = true ∧
    canonK 820 10 (mask 10) (820 * 10) (GGI j) = true := by
  intro j hj
  match j, hj with
  | 0, _ => exact ⟨(inF (i := 9) (by decide)).2.2, (inF (i := 9) (by decide)).2.1⟩
  | 1, _ => exact ⟨(inF (i := 10) (by decide)).2.2, (inF (i := 10) (by decide)).2.1⟩
  | 2, _ => exact ⟨(tkF (k := 2) (by decide)).2, tkiC (k := 2) (by decide)⟩
  | 3, _ => exact ⟨(tkF (k := 5) (by decide)).2, tkiC (k := 5) (by decide)⟩

theorem cgI : ∀ j < 5, invEqK 820 10 (mask 10) (820 * 10) (VbP (Nat.add j 2)) (VbI (Nat.add j 2)) =
    true ∧ canonK 820 10 (mask 10) (820 * 10) (VbI (Nat.add j 2)) = true := fun j hj =>
  ⟨(inF (i := j + 2) (by omega)).2.2, (inF (i := j + 2) (by omega)).2.1⟩

theorem ygI : ∀ j < 2, invEqK 820 10 (mask 10) (820 * 10) (VbP (Nat.add j 7)) (VbI (Nat.add j 7)) =
    true ∧ canonK 820 10 (mask 10) (820 * 10) (VbI (Nat.add j 7)) = true := fun j hj =>
  ⟨(inF (i := j + 7) (by omega)).2.2, (inF (i := j + 7) (by omega)).2.1⟩

theorem cnt : VbC.cnt = 2880 ∧ VbY.cnt = 1944 ∧ VbKT.cnt = 4536 ∧ VbKY.cnt = 6720 ∧
    VbCY.cnt = 80 := by
  have h := kCnt
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem hd : penumHdK (pidn 820 10) VbC.cnt 50000 VbC.T VbC.PL = true ∧
    penumHdK (pidn 820 10) VbY.cnt 50000 VbY.T VbY.PL = true ∧
    penumHdK (VbP 0) VbKT.cnt 50000 VbKT.T VbKT.PL = true ∧
    penumHdK (VbP 1) VbKY.cnt 50000 VbKY.T VbKY.PL = true ∧
    penumHdK (VbP 1) VbCY.cnt 50000 VbCY.T VbCY.PL = true := by
  have h := kHd
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem recCs : mulClosureH 820 dVb.cg closureCap = hRec 820 10 VbC.cnt VbC.T VbC.PL ∧
    mulTreeOK 820 dVb.cg (hRec 820 10 VbC.cnt VbC.T VbC.PL).1 (hRec 820 10 VbC.cnt VbC.T VbC.PL).2.1
      (hRec 820 10 VbC.cnt VbC.T VbC.PL).2.2 = true ∧
    hkeysDistinct 820 (hRec 820 10 VbC.cnt VbC.T VbC.PL).1.toList = true ∧
    closedOK 820 (dVb.cg ++ dVb.cg.map (invT 820)) (hRec 820 10 VbC.cnt VbC.T VbC.PL).1 = true ∧
    ∀ i < VbC.cnt, canonK 820 10 (mask 10) (820 * 10) (VbC.T i) = true := by
  have hG : ∀ j < 5, VbC.G j = pidn 820 10 := fun j hj => by
    have h := allN_spec kHC j hj
    simp only [Bool.and_eq_true] at h
    exact Nat.eq_of_beq_eq_true h.2
  have hg : TabsOK 820 10 5 VbC.GI dVb.cg := TabsOK_congr (fun j hj => by
    have h := allN_spec kHC j hj
    simp only [Bool.and_eq_true] at h
    exact Nat.eq_of_beq_eq_true h.1) cg_tabs
  have hb := slAll (L := 96) (K := 30) (by rw [cnt.1]) (fun s hs => peC_all s hs)
  have pe' := CFSG.KS.PEnumR.penumPtK_of_R sz (fun j hj => (hg.2 j hj).2) hG hd.1 hb
  have hs' : ∀ i < VbC.cnt, hsortPtK 820 10 (mask 10) VbC.cnt VbC.T VbC.HS VbC.HSI i = true :=
    fun i hi => by
      rw [← hsortPtKF_eq]
      exact slAll (L := 288) (K := 10) (by rw [cnt.1]) (fun s hs => hsC_all s hs) i hi
  obtain ⟨e, ht, hdd⟩ := mulH_sound sz hG hg hd.1 pe' hs'
  have hT : ∀ i < VbC.cnt, canonK 820 10 (mask 10) (820 * 10) (VbC.T i) = true :=
    fun i hi => penumPt_canon (pe' i hi)
  have hinv : ∀ j < 5, invEqK 820 10 (mask 10) (820 * 10) (VbC.GI j) (GJC j) = true ∧
      canonK 820 10 (mask 10) (820 * 10) (GJC j) = true := fun j hj => by
    have h := allN_spec kHC j hj
    simp only [Bool.and_eq_true] at h
    rw [Nat.eq_of_beq_eq_true h.1]
    exact cgI j hj
  have hcl : ∀ c < VbC.cnt * (5 + 5), findPtK VbC.cnt VbC.T
      (prodQK 820 10 (mask 10) 10 VbC.T (bothK 5 VbC.GI GJC)) VbCCl c = true := fun c hc =>
    clRK_find hb hc (slAll (L := 960) (K := 30) (N := VbC.cnt * (5 + 5)) (by rw [cnt.1])
      (fun s hs => clC_all s hs) c hc)
  exact ⟨e, ht, hdd, closedOK_of hT (TabsOK_both hg hinv) hcl, hT⟩

theorem recYs : mulClosureH 820 dVb.yg closureCap = hRec 820 10 VbY.cnt VbY.T VbY.PL ∧
    mulTreeOK 820 dVb.yg (hRec 820 10 VbY.cnt VbY.T VbY.PL).1 (hRec 820 10 VbY.cnt VbY.T VbY.PL).2.1
      (hRec 820 10 VbY.cnt VbY.T VbY.PL).2.2 = true ∧
    hkeysDistinct 820 (hRec 820 10 VbY.cnt VbY.T VbY.PL).1.toList = true ∧
    closedOK 820 (dVb.yg ++ dVb.yg.map (invT 820)) (hRec 820 10 VbY.cnt VbY.T VbY.PL).1 = true ∧
    ∀ i < VbY.cnt, canonK 820 10 (mask 10) (820 * 10) (VbY.T i) = true := by
  have hG : ∀ j < 2, VbY.G j = pidn 820 10 := fun j hj => by
    have h := allN_spec kHY j hj
    simp only [Bool.and_eq_true] at h
    exact Nat.eq_of_beq_eq_true h.2
  have hg : TabsOK 820 10 2 VbY.GI dVb.yg := TabsOK_congr (fun j hj => by
    have h := allN_spec kHY j hj
    simp only [Bool.and_eq_true] at h
    exact Nat.eq_of_beq_eq_true h.1) yg_tabs
  have hb := slAll (L := 81) (K := 24) (by rw [cnt.2.1]) (fun s hs => peY_all s hs)
  have pe' := CFSG.KS.PEnumR.penumPtK_of_R sz (fun j hj => (hg.2 j hj).2) hG hd.2.1 hb
  have hs' : ∀ i < VbY.cnt, hsortPtK 820 10 (mask 10) VbY.cnt VbY.T VbY.HS VbY.HSI i = true :=
    fun i hi => by
      rw [← hsortPtKF_eq]
      exact slAll (L := 243) (K := 8) (by rw [cnt.2.1]) (fun s hs => hsY_all s hs) i hi
  obtain ⟨e, ht, hdd⟩ := mulH_sound sz hG hg hd.2.1 pe' hs'
  have hT : ∀ i < VbY.cnt, canonK 820 10 (mask 10) (820 * 10) (VbY.T i) = true :=
    fun i hi => penumPt_canon (pe' i hi)
  have hinv : ∀ j < 2, invEqK 820 10 (mask 10) (820 * 10) (VbY.GI j) (GJY j) = true ∧
      canonK 820 10 (mask 10) (820 * 10) (GJY j) = true := fun j hj => by
    have h := allN_spec kHY j hj
    simp only [Bool.and_eq_true] at h
    rw [Nat.eq_of_beq_eq_true h.1]
    exact ygI j hj
  have hcl : ∀ c < VbY.cnt * (2 + 2), findPtK VbY.cnt VbY.T
      (prodQK 820 10 (mask 10) 4 VbY.T (bothK 2 VbY.GI GJY)) VbYCl c = true := fun c hc =>
    clRK_find hb hc (slAll (L := 972) (K := 8) (N := VbY.cnt * (2 + 2)) (by rw [cnt.2.1])
      (fun s hs => clY_all s hs) c hc)
  exact ⟨e, ht, hdd, closedOK_of hT (TabsOK_both hg hinv) hcl, hT⟩

theorem gG_T : TabsOK 820 10 4 VbKT.G dVb.gensG ∧ TabsOK 820 10 4 VbKT.GI (dVb.gensG.map (invT 820)) ∧
    TabsOK 820 10 4 VbKY.G dVb.gensG ∧ TabsOK 820 10 4 VbKY.GI (dVb.gensG.map (invT 820)) := by
  have e : ∀ j < 4, VbKT.G j = GG j ∧ VbKT.GI j = GGI j ∧ VbKY.G j = GG j ∧ VbKY.GI j = GGI j :=
    fun j hj => by
      have h := allN_spec kHT j hj
      simp only [Bool.and_eq_true, Nat.beq_eq] at h
      exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩
  have hi := TabsOK_inv gens_tabs gensI
  exact ⟨TabsOK_congr (fun j hj => (e j hj).1) gens_tabs,
    TabsOK_congr (fun j hj => (e j hj).2.1) hi, TabsOK_congr (fun j hj => (e j hj).2.2.1) gens_tabs,
    TabsOK_congr (fun j hj => (e j hj).2.2.2) hi⟩

theorem cg_CY : TabsOK 820 10 5 VbCY.G dVb.cg ∧ TabsOK 820 10 5 VbCY.GI (dVb.cg.map (invT 820)) := by
  have e : ∀ j < 5, VbCY.G j = VbP (Nat.add j 2) ∧ VbCY.GI j = VbI (Nat.add j 2) := fun j hj => by
    have h := allN_spec kHCY j hj
    simp only [Bool.and_eq_true, Nat.beq_eq] at h
    exact h
  exact ⟨TabsOK_congr (fun j hj => (e j hj).1) cg_tabs,
    TabsOK_congr (fun j hj => (e j hj).2) (TabsOK_inv cg_tabs cgI)⟩

theorem cg_all : dVb.cg.all (fun g => memCos dVb.ks g && commTT 820 g dVb.Tt) = true := by
  rw [Array.all_eq_true]
  intro j hj
  have hj' : j < 5 := by rw [cg_tabs.1] at hj; exact hj
  rw [← getElem!_pos _ j hj, (cg_tabs.2 j hj').1, tT]
  have hc := kComm
  simp only [Bool.and_eq_true] at hc
  have hm := allN_spec hc.1 j hj'
  beta_reduce
  rw [cos_of (i := Nat.add j 2) (by change 2 ≤ j + 2; omega) (by change j + 2 ≤ 10; omega),
    Bool.true_and]
  exact (commTT_unpack (inF (i := j + 2) (by omega)).1 (inF (i := 0) (by decide)).1).trans hm

theorem yg_all : dVb.yg.all (fun g => memCos dVb.ks g && commTT 820 g dVb.y0) = true := by
  rw [Array.all_eq_true]
  intro j hj
  have hj' : j < 2 := by rw [yg_tabs.1] at hj; exact hj
  rw [← getElem!_pos _ j hj, (yg_tabs.2 j hj').1, tY]
  have hc := kComm
  simp only [Bool.and_eq_true] at hc
  have hm := allN_spec hc.2 j hj'
  beta_reduce
  rw [cos_of (i := Nat.add j 7) (by change 2 ≤ j + 7; omega) (by change j + 7 ≤ 10; omega),
    Bool.true_and]
  exact (commTT_unpack (inF (i := j + 7) (by omega)).1 (inF (i := 1) (by decide)).1).trans hm

theorem gG_all : dVb.gensG.all (memCos dVb.ks) = true := by
  have ht := kCosT
  simp only [Bool.and_eq_true] at ht
  rw [Array.all_eq_true]
  intro j hj
  have hj' : j < 4 := by rw [gens_tabs.1] at hj; exact hj
  rw [← getElem!_pos _ j hj, (gens_tabs.2 j hj').1]
  match j, hj' with
  | 0, _ => exact cos_of (i := 9) (by decide) (by decide)
  | 1, _ => exact cos_of (i := 10) (by decide) (by decide)
  | 2, _ => exact memCos_of (k := 2) (tkF (k := 2) (by decide)).1 (by decide) (by decide) ht.1
  | 3, _ => exact memCos_of (k := 5) (tkF (k := 5) (by decide)).1 (by decide) (by decide) ht.2

theorem cover_ok : CFSG.EvenSporadicStandard.HSStd.U43.coverOK dVb.cg dVb.y0 closureCap = true := by
  obtain ⟨eC, -, -, -, hTC⟩ := recCs
  obtain ⟨e, ht, -⟩ := conjH_sound (k := 5) (cap := 50000) sz cg_CY.1 cg_CY.2 tY hd.2.2.2.2
    (fun i hi => penumSl_spec cyPe i (Nat.zero_le _) (by omega) hi)
    (fun i hi => slK_spec cyHs i (Nat.zero_le _) (by omega) hi)
  have hk : closureCap = 50000 := rfl
  unfold CFSG.EvenSporadicStandard.HSStd.U43.coverOK
  rw [hk, e, ht, Bool.true_and, ← hk, eC, Array.all_eq_true]
  intro i hi
  have hi' : i < VbC.cnt := by simpa [hRec] using hi
  rw [← getElem!_pos _ i hi, hRec_get hi']
  have hc := hTC i hi'
  rw [show tabT (unpack 820 10 (VbC.T i)) = tb 820 10 (VbC.T i) from rfl, ordTest3_tb sz hc]
  cases ho : ord3P 820 10 (VbC.T i)
  · rfl
  · obtain ⟨hq, hq2⟩ := coverP_spec ((fa cv_all : ∀ s < 8, cv s = true) (i / 360)
      (Nat.div_lt_of_lt_mul (by have := cnt.1; omega)))
      i (Nat.mul_div_le i 360) (by
        have := Nat.lt_mul_div_succ i (show 0 < 360 by norm_num)
        change i < 360 * (i / 360) + 360
        rw [Nat.mul_succ] at this
        exact this) hi' ho
    rw [Bool.not_true, Bool.false_or]
    refine memT_of hq ?_
    rw [hq2]
    exact tblEq_self hc

theorem caseCheck_true : caseCheck dVb = true := by
  obtain ⟨c0, -, v0⟩ := inF (i := 0) (by decide)
  obtain ⟨c1, -, v1⟩ := inF (i := 1) (by decide)
  obtain ⟨eC, tC, dC, clC', -⟩ := recCs
  obtain ⟨eY, tY', dY, clY', hTY⟩ := recYs
  have hg := gG_T
  have hsol := kSol
  unfold solK at hsol
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hsol
  have hE : yEnum dVb = Array.ofFn (n := VbY.cnt) fun i => tb 820 10 (VbY.T i.val) := by
    unfold yEnum
    rw [eY]
    rfl
  have hsl := solList_tb sz hTY c0 c1 tT tY hE
  unfold caseCheck
  rw [show dVb.ysz = 1944 from rfl, show dVb.nsol = 12 from rfl, show dVb.sizeG = 13063680 from rfl]
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc]
  refine ⟨?_, ?_, gG_all, ?_, cg_all, ?_, cover_ok, yg_all, ?_, ?_, ?_, ?_⟩
  · rw [tT]
    exact permOK_unpack c0 v0
  · rw [tY]
    exact permOK_unpack c1 v1
  · exact classOK_of hg.1 hg.2.1 (fun j hj => by
      have h := allN_spec kHT j hj
      simp only [Bool.and_eq_true, Nat.beq_eq] at h
      rw [h.1.1.1, h.1.1.2]
      exact gensI j hj) tT hd.2.2.1
      (peAll (L := 126) (K := 36) (by rw [cnt.2.2.1]) (fun s hs => peT_all s hs))
      (slAll (L := 567) (K := 8) (by rw [cnt.2.2.1]) (fun s hs => hsT_all s hs))
      (by rw [cnt.2.2.1])
  · exact enum_of cg_tabs cgI eC tC dC clC' cnt.1
  · exact enum_of yg_tabs ygI eY tY' dY clY' cnt.2.1
  · exact classOK_of hg.2.2.1 hg.2.2.2 (fun j hj => by
      have h := allN_spec kHT j hj
      simp only [Bool.and_eq_true, Nat.beq_eq] at h
      rw [h.1.2, h.2]
      exact gensI j hj) tY hd.2.2.2.1
      (peAll (L := 112) (K := 60) (by rw [cnt.2.2.2.1]) (fun s hs => peK_all s hs))
      (slAll (L := 840) (K := 8) (by rw [cnt.2.2.2.1]) (fun s hs => hsK_all s hs))
      (by rw [cnt.2.2.2.1])
  · rw [hsl, List.length_map]
    exact hsol.1
  · rw [hsl, List.all_map, List.all_eq_true]
    intro p hp
    have hp1 : p.1 < VbY.cnt := by
      unfold solsP at hp
      simp only [List.mem_flatMap, List.mem_filter, List.mem_range, List.mem_map] at hp
      obtain ⟨i, ⟨hi, -⟩, j, -, rfl⟩ := hp
      exact hi
    have hp2 : p.2 < VbY.cnt := by
      unfold solsP at hp
      simp only [List.mem_flatMap, List.mem_filter, List.mem_range, List.mem_map] at hp
      obtain ⟨i, -, j, ⟨hj, -⟩, rfl⟩ := hp
      exact hj
    simp only [Function.comp_apply, beq_iff_eq]
    rw [cent5Of_tb sz hTY c0 tT hE (hTY _ hp1) (hTY _ hp2)]
    exact hsol.2 p hp

end CertificateChecks.KernelHSStd.U43Vb

end
