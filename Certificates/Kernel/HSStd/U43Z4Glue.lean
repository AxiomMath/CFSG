module

public import Certificates.Kernel.HSStd.U43Z4Base
public import Certificates.Kernel.HSStd.U43Z4RC
public import Certificates.Kernel.HSStd.U43Z4RT
public import Certificates.Kernel.HSStd.U43Z4RK0
public import Certificates.Kernel.HSStd.U43Z4RK1
public import Certificates.Kernel.HSStd.U43Z4Sol
public import Certificates.Kernel.HSStd.U43CaseKit
public import Certificates.Kernel.Sporadic.OddCore.U43CoverKF
import CFSG.Certificates.Kernel.BfsPinUnpack
import CFSG.Certificates.Kernel.BfsPinSetSound
import CFSG.Certificates.Kernel.BfsPinAlg
import CFSG.Certificates.Kernel.Spor.PackWord
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Common.ForallChunks
import CFSG.Certificates.Kernel.Spor.MulHCSound
import CFSG.Certificates.Kernel.Spor.MulHFSound
import CFSG.Certificates.Kernel.Spor.PEnumRSound
public import Certificates.Kernel.Sporadic.OddCore.CentGlue

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHSStd.U43Z4

open CFSG.EvenSporadicStandard.HSStd.U43 CFSG.EvenSporadicStandard.M24Std.CU43
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Schreier.Native
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KC.BfsPin
open CFSG.KC.U43Case
open CFSG.Monster.B.Co2.Native CFSG.LieType.Multipliers.U43
open CertificateChecks.KernelHSStd
open CertificateChecks.KernelSpor (U43CoverK.inP_tab U43CoverK.gen_of U43CoverK.tP)

#kc_forall_chunks peC_all (fun s => peC s = true) 30 CertificateChecks.KernelHSStd.U43Z4.peC 1
#kc_forall_chunks hsC_all (fun s => hsC s = true) 10 CertificateChecks.KernelHSStd.U43Z4.hsC 1
#kc_forall_chunks clC_all (fun s => clCs s = true) 24 CertificateChecks.KernelHSStd.U43Z4.clCs 1
#kc_forall_chunks peY_all (fun s => peY s = true) 24 CertificateChecks.KernelHSStd.U43Z4.peY 1
#kc_forall_chunks hsY_all (fun s => hsY s = true) 8 CertificateChecks.KernelHSStd.U43Z4.hsY 1
#kc_forall_chunks clY_all (fun s => clYs s = true) 8 CertificateChecks.KernelHSStd.U43Z4.clYs 1
#kc_forall_chunks peT_all (fun s => peT s = true) 36 CertificateChecks.KernelHSStd.U43Z4.peT 1
#kc_forall_chunks hsT_all (fun s => hsT s = true) 8 CertificateChecks.KernelHSStd.U43Z4.hsT 1
#kc_forall_chunks peK_all (fun s => peK s = true) 60 CertificateChecks.KernelHSStd.U43Z4.peK 1
#kc_forall_chunks hsK_all (fun s => hsK s = true) 8 CertificateChecks.KernelHSStd.U43Z4.hsK 1
#kc_forall_chunks cv_all (fun s => cv s = true) 8 CertificateChecks.KernelHSStd.U43Z4.cv 1

theorem fa {P : Nat → Prop} {K : Nat} (h : ∀ s < K, P s) : ∀ s < K, P s := h

theorem sz : szOK 820 10 = true := by
  have h := kSz
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1

theorem cg_size : z4Cg.size = 4 := by
  have h := kSz
  simp only [Bool.and_eq_true] at h
  exact Nat.eq_of_beq_eq_true h.1.2

theorem yg_size : z4Yg.size = 2 := by
  have h := kSz
  simp only [Bool.and_eq_true] at h
  exact Nat.eq_of_beq_eq_true h.2

theorem inF {i : Nat} (hi : i < 12) : cK (Z4P i) = true ∧ cK (Z4I i) = true ∧
    invEqK 820 10 (mask 10) (820 * 10) (Z4P i) (Z4I i) = true := by
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
  obtain ⟨a1, a2⟩ := ppw_eq (inF (i := 10) (by decide)).1 (k / 4)
  obtain ⟨b1, b2⟩ := ppw_eq (inF (i := 11) (by decide)).1 (k % 4)
  unfold tArr TK
  rw [eq_unpack_of_bindListK kBind.2.2.2.2.2.2.2.2.2.2.1,
    eq_unpack_of_bindListK kBind.2.2.2.2.2.2.2.2.2.2.2, a1, b1, compA_unpack a2 b2]
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

theorem cos_of {i : Nat} (h2 : 2 ≤ i) (h9 : i ≤ 9) :
    memCos dZ4.ks (tabT (unpack 820 10 (Z4P i))) = true := by
  have h := allN_spec kCos (i - 2) (by omega)
  rw [show Nat.add (i - 2) 2 = i by change i - 2 + 2 = i; omega] at h
  unfold cosK at h
  rw [CFSG.KC.BfsPin.strictB_app] at h
  simp only [bAnd_iff] at h
  have hk := Nat.blt_eq.mp h.1
  exact memCos_of (inF (i := i) (by omega)).1
    (by change _ ∈ [0, 1, 2, 3]; simp only [List.mem_cons, List.not_mem_nil]; omega)
    (by omega) h.2

theorem tT : dZ4.Tt = tb 820 10 (Z4P 0) := by
  have : reps[8]! = rep8 := rfl
  change tabOf reps[8]! = _
  rw [this, eq_unpack_of_bindListK kBind.1]
  rfl

theorem tY : dZ4.y0 = tb 820 10 (Z4P 1) := by
  change tabOf z4Y0 = _
  rw [eq_unpack_of_bindListK kBind.2.1]
  rfl

theorem tabsOf_get {a : Array (Array Nat)} {j : Nat} (hj : j < a.size) :
    (tabsOf a)[j]! = tabOf a[j]! := by
  unfold tabsOf
  rw [getElem!_pos _ j (by simpa using hj), Array.getElem_map, getElem!_pos a j hj]

theorem cg_tabs : TabsOK 820 10 4 (fun j => Z4P (Nat.add j 2)) dZ4.cg := by
  refine ⟨by change (tabsOf z4Cg).size = 4; simp [tabsOf, cg_size], fun j hj => ?_⟩
  refine ⟨?_, (inF (i := j + 2) (by omega)).1⟩
  change (tabsOf z4Cg)[j]! = _
  rw [tabsOf_get (by rw [cg_size]; exact hj)]
  obtain ⟨-, -, b0, b1, b2, b3, -⟩ := kBind
  have hb : z4Cg[j]! = unpack 820 10 (Z4P (j + 2)) := by
    match j, hj with
    | 0, _ => exact eq_unpack_of_bindListK b0
    | 1, _ => exact eq_unpack_of_bindListK b1
    | 2, _ => exact eq_unpack_of_bindListK b2
    | 3, _ => exact eq_unpack_of_bindListK b3
  rw [hb]
  rfl

theorem yg_tabs : TabsOK 820 10 2 (fun j => Z4P (Nat.add j 6)) dZ4.yg := by
  refine ⟨by change (tabsOf z4Yg).size = 2; simp [tabsOf, yg_size], fun j hj => ?_⟩
  refine ⟨?_, (inF (i := j + 6) (by omega)).1⟩
  change (tabsOf z4Yg)[j]! = _
  rw [tabsOf_get (by rw [yg_size]; exact hj)]
  obtain ⟨-, -, -, -, -, -, b0, b1, -⟩ := kBind
  have hb : z4Yg[j]! = unpack 820 10 (Z4P (j + 6)) := by
    match j, hj with
    | 0, _ => exact eq_unpack_of_bindListK b0
    | 1, _ => exact eq_unpack_of_bindListK b1
  rw [hb]
  rfl

theorem gens_tabs : TabsOK 820 10 3 GG dZ4.gensG := by
  refine ⟨rfl, fun j hj => ?_⟩
  obtain ⟨-, -, -, -, -, -, -, -, ba, bb, -⟩ := kBind
  match j, hj with
  | 0, _ => exact ⟨by
      change tabOf tabA = _
      rw [eq_unpack_of_bindListK ba]; rfl, (inF (i := 8) (by decide)).1⟩
  | 1, _ => exact ⟨by
      change tabOf tabB = _
      rw [eq_unpack_of_bindListK bb]; rfl, (inF (i := 9) (by decide)).1⟩
  | 2, _ => exact ⟨by
      change tabOf (tArr 1) = _
      rw [tArr_eq]; rfl, (tkF (k := 1) (by decide)).1⟩

theorem gensI : ∀ j < 3, invEqK 820 10 (mask 10) (820 * 10) (GG j) (GGI j) = true ∧
    canonK 820 10 (mask 10) (820 * 10) (GGI j) = true := by
  intro j hj
  match j, hj with
  | 0, _ => exact ⟨(inF (i := 8) (by decide)).2.2, (inF (i := 8) (by decide)).2.1⟩
  | 1, _ => exact ⟨(inF (i := 9) (by decide)).2.2, (inF (i := 9) (by decide)).2.1⟩
  | 2, _ => exact ⟨(tkF (k := 1) (by decide)).2, tkiC (k := 1) (by decide)⟩

theorem cgI : ∀ j < 4, invEqK 820 10 (mask 10) (820 * 10) (Z4P (Nat.add j 2)) (Z4I (Nat.add j 2)) =
    true ∧ canonK 820 10 (mask 10) (820 * 10) (Z4I (Nat.add j 2)) = true := fun j hj =>
  ⟨(inF (i := j + 2) (by omega)).2.2, (inF (i := j + 2) (by omega)).2.1⟩

theorem ygI : ∀ j < 2, invEqK 820 10 (mask 10) (820 * 10) (Z4P (Nat.add j 6)) (Z4I (Nat.add j 6)) =
    true ∧ canonK 820 10 (mask 10) (820 * 10) (Z4I (Nat.add j 6)) = true := fun j hj =>
  ⟨(inF (i := j + 6) (by omega)).2.2, (inF (i := j + 6) (by omega)).2.1⟩

theorem cnt : Z4C.cnt = 2880 ∧ Z4Y.cnt = 1944 ∧ Z4KT.cnt = 4536 ∧ Z4KY.cnt = 6720 ∧
    Z4CY.cnt = 80 := by
  have h := kCnt
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem hd : penumHdK (pidn 820 10) Z4C.cnt 50000 Z4C.T Z4C.PL = true ∧
    penumHdK (pidn 820 10) Z4Y.cnt 50000 Z4Y.T Z4Y.PL = true ∧
    penumHdK (Z4P 0) Z4KT.cnt 50000 Z4KT.T Z4KT.PL = true ∧
    penumHdK (Z4P 1) Z4KY.cnt 50000 Z4KY.T Z4KY.PL = true ∧
    penumHdK (Z4P 1) Z4CY.cnt 50000 Z4CY.T Z4CY.PL = true := by
  have h := kHd
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem slAll {K L N : Nat} {P : Nat → Bool} (hN : N ≤ L * K)
    (h : ∀ s < K, slK N P (Nat.mul L s) L = true) : ∀ i < N, P i = true := by
  intro i hi
  have hL : 0 < L := by
    rcases Nat.eq_zero_or_pos L with h0 | h0
    · rw [h0, Nat.zero_mul] at hN; omega
    · exact h0
  have hs : i / L < K := Nat.div_lt_of_lt_mul (by omega)
  exact slK_spec (h _ hs) i (Nat.mul_div_le i L) (by
    have := Nat.lt_mul_div_succ i hL
    change i < L * (i / L) + L
    rw [Nat.mul_succ] at this
    exact this) hi

theorem peAll {n w m nw k K L N : Nat} {conj : Bool} {G GI T PL POS SRT SRI : Nat → Nat}
    (hN : N ≤ L * K) (h : ∀ s < K, penumSlK n w m nw conj G GI k N T PL POS SRT SRI (Nat.mul L s) L =
      true) : ∀ i < N, penumPtK n w m nw conj G GI k N T PL POS SRT SRI i = true := by
  intro i hi
  have hL : 0 < L := by
    rcases Nat.eq_zero_or_pos L with h0 | h0
    · rw [h0, Nat.zero_mul] at hN; omega
    · exact h0
  have hs : i / L < K := Nat.div_lt_of_lt_mul (by omega)
  exact penumSl_spec (h _ hs) i (Nat.mul_div_le i L) (by
    have := Nat.lt_mul_div_succ i hL
    change i < L * (i / L) + L
    rw [Nat.mul_succ] at this
    exact this) hi

theorem recCs : mulClosureH 820 dZ4.cg closureCap = hRec 820 10 Z4C.cnt Z4C.T Z4C.PL ∧
    mulTreeOK 820 dZ4.cg (hRec 820 10 Z4C.cnt Z4C.T Z4C.PL).1 (hRec 820 10 Z4C.cnt Z4C.T Z4C.PL).2.1
      (hRec 820 10 Z4C.cnt Z4C.T Z4C.PL).2.2 = true ∧
    hkeysDistinct 820 (hRec 820 10 Z4C.cnt Z4C.T Z4C.PL).1.toList = true ∧
    closedOK 820 (dZ4.cg ++ dZ4.cg.map (invT 820)) (hRec 820 10 Z4C.cnt Z4C.T Z4C.PL).1 = true ∧
    ∀ i < Z4C.cnt, canonK 820 10 (mask 10) (820 * 10) (Z4C.T i) = true := by
  have hG : ∀ j < 4, Z4C.G j = pidn 820 10 := fun j hj => by
    have h := allN_spec kHC j hj
    simp only [Bool.and_eq_true] at h
    exact Nat.eq_of_beq_eq_true h.2
  have hg : TabsOK 820 10 4 Z4C.GI dZ4.cg := TabsOK_congr (fun j hj => by
    have h := allN_spec kHC j hj
    simp only [Bool.and_eq_true] at h
    exact Nat.eq_of_beq_eq_true h.1) cg_tabs
  have hb := slAll (L := 96) (K := 30) (by rw [cnt.1]) (fun s hs => peC_all s hs)
  have pe' := CFSG.KS.PEnumR.penumPtK_of_R sz (fun j hj => (hg.2 j hj).2) hG hd.1 hb
  have hs' : ∀ i < Z4C.cnt, hsortPtK 820 10 (mask 10) Z4C.cnt Z4C.T Z4C.HS Z4C.HSI i = true :=
    fun i hi => by
      rw [← hsortPtKF_eq]
      exact slAll (L := 288) (K := 10) (by rw [cnt.1]) (fun s hs => hsC_all s hs) i hi
  obtain ⟨e, ht, hdd⟩ := mulH_sound sz hG hg hd.1 pe' hs'
  have hT : ∀ i < Z4C.cnt, canonK 820 10 (mask 10) (820 * 10) (Z4C.T i) = true :=
    fun i hi => penumPt_canon (pe' i hi)
  have hinv : ∀ j < 4, invEqK 820 10 (mask 10) (820 * 10) (Z4C.GI j) (GJC j) = true ∧
      canonK 820 10 (mask 10) (820 * 10) (GJC j) = true := fun j hj => by
    have h := allN_spec kHC j hj
    simp only [Bool.and_eq_true] at h
    rw [Nat.eq_of_beq_eq_true h.1]
    exact cgI j hj
  have hcl : ∀ c < Z4C.cnt * (4 + 4), findPtK Z4C.cnt Z4C.T
      (prodQK 820 10 (mask 10) 8 Z4C.T (bothK 4 Z4C.GI GJC)) Z4CCl c = true := fun c hc =>
    clRK_find hb hc (slAll (L := 960) (K := 24) (N := Z4C.cnt * (4 + 4)) (by rw [cnt.1])
      (fun s hs => clC_all s hs) c hc)
  exact ⟨e, ht, hdd, closedOK_of hT (TabsOK_both hg hinv) hcl, hT⟩

theorem recYs : mulClosureH 820 dZ4.yg closureCap = hRec 820 10 Z4Y.cnt Z4Y.T Z4Y.PL ∧
    mulTreeOK 820 dZ4.yg (hRec 820 10 Z4Y.cnt Z4Y.T Z4Y.PL).1 (hRec 820 10 Z4Y.cnt Z4Y.T Z4Y.PL).2.1
      (hRec 820 10 Z4Y.cnt Z4Y.T Z4Y.PL).2.2 = true ∧
    hkeysDistinct 820 (hRec 820 10 Z4Y.cnt Z4Y.T Z4Y.PL).1.toList = true ∧
    closedOK 820 (dZ4.yg ++ dZ4.yg.map (invT 820)) (hRec 820 10 Z4Y.cnt Z4Y.T Z4Y.PL).1 = true ∧
    ∀ i < Z4Y.cnt, canonK 820 10 (mask 10) (820 * 10) (Z4Y.T i) = true := by
  have hG : ∀ j < 2, Z4Y.G j = pidn 820 10 := fun j hj => by
    have h := allN_spec kHY j hj
    simp only [Bool.and_eq_true] at h
    exact Nat.eq_of_beq_eq_true h.2
  have hg : TabsOK 820 10 2 Z4Y.GI dZ4.yg := TabsOK_congr (fun j hj => by
    have h := allN_spec kHY j hj
    simp only [Bool.and_eq_true] at h
    exact Nat.eq_of_beq_eq_true h.1) yg_tabs
  have hb := slAll (L := 81) (K := 24) (by rw [cnt.2.1]) (fun s hs => peY_all s hs)
  have pe' := CFSG.KS.PEnumR.penumPtK_of_R sz (fun j hj => (hg.2 j hj).2) hG hd.2.1 hb
  have hs' : ∀ i < Z4Y.cnt, hsortPtK 820 10 (mask 10) Z4Y.cnt Z4Y.T Z4Y.HS Z4Y.HSI i = true :=
    fun i hi => by
      rw [← hsortPtKF_eq]
      exact slAll (L := 243) (K := 8) (by rw [cnt.2.1]) (fun s hs => hsY_all s hs) i hi
  obtain ⟨e, ht, hdd⟩ := mulH_sound sz hG hg hd.2.1 pe' hs'
  have hT : ∀ i < Z4Y.cnt, canonK 820 10 (mask 10) (820 * 10) (Z4Y.T i) = true :=
    fun i hi => penumPt_canon (pe' i hi)
  have hinv : ∀ j < 2, invEqK 820 10 (mask 10) (820 * 10) (Z4Y.GI j) (GJY j) = true ∧
      canonK 820 10 (mask 10) (820 * 10) (GJY j) = true := fun j hj => by
    have h := allN_spec kHY j hj
    simp only [Bool.and_eq_true] at h
    rw [Nat.eq_of_beq_eq_true h.1]
    exact ygI j hj
  have hcl : ∀ c < Z4Y.cnt * (2 + 2), findPtK Z4Y.cnt Z4Y.T
      (prodQK 820 10 (mask 10) 4 Z4Y.T (bothK 2 Z4Y.GI GJY)) Z4YCl c = true := fun c hc =>
    clRK_find hb hc (slAll (L := 972) (K := 8) (N := Z4Y.cnt * (2 + 2)) (by rw [cnt.2.1])
      (fun s hs => clY_all s hs) c hc)
  exact ⟨e, ht, hdd, closedOK_of hT (TabsOK_both hg hinv) hcl, hT⟩

theorem gG_T : TabsOK 820 10 3 Z4KT.G dZ4.gensG ∧ TabsOK 820 10 3 Z4KT.GI (dZ4.gensG.map (invT 820)) ∧
    TabsOK 820 10 3 Z4KY.G dZ4.gensG ∧ TabsOK 820 10 3 Z4KY.GI (dZ4.gensG.map (invT 820)) := by
  have e : ∀ j < 3, Z4KT.G j = GG j ∧ Z4KT.GI j = GGI j ∧ Z4KY.G j = GG j ∧ Z4KY.GI j = GGI j :=
    fun j hj => by
      have h := allN_spec kHT j hj
      simp only [Bool.and_eq_true, Nat.beq_eq] at h
      exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩
  have hi := TabsOK_inv gens_tabs gensI
  exact ⟨TabsOK_congr (fun j hj => (e j hj).1) gens_tabs,
    TabsOK_congr (fun j hj => (e j hj).2.1) hi, TabsOK_congr (fun j hj => (e j hj).2.2.1) gens_tabs,
    TabsOK_congr (fun j hj => (e j hj).2.2.2) hi⟩

theorem cg_CY : TabsOK 820 10 4 Z4CY.G dZ4.cg ∧ TabsOK 820 10 4 Z4CY.GI (dZ4.cg.map (invT 820)) := by
  have e : ∀ j < 4, Z4CY.G j = Z4P (Nat.add j 2) ∧ Z4CY.GI j = Z4I (Nat.add j 2) := fun j hj => by
    have h := allN_spec kHCY j hj
    simp only [Bool.and_eq_true, Nat.beq_eq] at h
    exact h
  exact ⟨TabsOK_congr (fun j hj => (e j hj).1) cg_tabs,
    TabsOK_congr (fun j hj => (e j hj).2) (TabsOK_inv cg_tabs cgI)⟩

theorem permInv_all {k : Nat} {G GI : Nat → Nat} {A : Array Table} (hA : TabsOK 820 10 k G A)
    (hi : ∀ j < k, invEqK 820 10 (mask 10) (820 * 10) (G j) (GI j) = true ∧
      canonK 820 10 (mask 10) (820 * 10) (GI j) = true) : A.all permInvOK = true := by
  rw [Array.all_eq_true]
  intro j hj
  have hj' : j < k := by rw [hA.1] at hj; exact hj
  obtain ⟨hg, hc⟩ := hA.2 j hj'
  rw [← getElem!_pos _ j hj, hg]
  exact U43CoverK.gen_of hc (hi j hj').2 (hi j hj').1

theorem classOK_of {k cnt sizeG csz : Nat} {G GI T PL POS SRT SRI HS HSI : Nat → Nat} {X : Nat}
    {A : Array Table} {x : Table} (hA : TabsOK 820 10 k G A) (hAI : TabsOK 820 10 k GI (A.map (invT 820)))
    (hi : ∀ j < k, invEqK 820 10 (mask 10) (820 * 10) (G j) (GI j) = true ∧
      canonK 820 10 (mask 10) (820 * 10) (GI j) = true)
    (hx : x = tabT (unpack 820 10 X)) (hh : penumHdK X cnt 50000 T PL = true)
    (hp : ∀ i < cnt, penumPtK 820 10 (mask 10) (820 * 10) true G GI k cnt T PL POS SRT SRI i = true)
    (hs : ∀ i < cnt, hsortPtK 820 10 (mask 10) cnt T HS HSI i = true) (hsz : sizeG ≤ csz * cnt) :
    CFSG.EvenSporadicStandard.HSStd.U43.classOK A x closureCap sizeG csz = true := by
  obtain ⟨e, ht, hdd⟩ := conjH_sound sz hA hAI hx hh hp hs
  unfold CFSG.EvenSporadicStandard.HSStd.U43.classOK
  have hk : closureCap = 50000 := rfl
  rw [hk, e, permInv_all hA hi, ht, hdd, hRec_size]
  simp only [Bool.true_and, decide_eq_true_eq]
  exact hsz

theorem cg_all : dZ4.cg.all (fun g => memCos dZ4.ks g && commTT 820 g dZ4.Tt) = true := by
  rw [Array.all_eq_true]
  intro j hj
  have hj' : j < 4 := by rw [cg_tabs.1] at hj; exact hj
  rw [← getElem!_pos _ j hj, (cg_tabs.2 j hj').1, tT]
  have hc := kComm
  simp only [Bool.and_eq_true] at hc
  have hm := allN_spec hc.1 j hj'
  beta_reduce
  rw [cos_of (i := Nat.add j 2) (by change 2 ≤ j + 2; omega) (by change j + 2 ≤ 9; omega),
    Bool.true_and]
  exact (commTT_unpack (inF (i := j + 2) (by omega)).1 (inF (i := 0) (by decide)).1).trans hm

theorem yg_all : dZ4.yg.all (fun g => memCos dZ4.ks g && commTT 820 g dZ4.y0) = true := by
  rw [Array.all_eq_true]
  intro j hj
  have hj' : j < 2 := by rw [yg_tabs.1] at hj; exact hj
  rw [← getElem!_pos _ j hj, (yg_tabs.2 j hj').1, tY]
  have hc := kComm
  simp only [Bool.and_eq_true] at hc
  have hm := allN_spec hc.2 j hj'
  beta_reduce
  rw [cos_of (i := Nat.add j 6) (by change 2 ≤ j + 6; omega) (by change j + 6 ≤ 9; omega),
    Bool.true_and]
  exact (commTT_unpack (inF (i := j + 6) (by omega)).1 (inF (i := 1) (by decide)).1).trans hm

theorem gG_all : dZ4.gensG.all (memCos dZ4.ks) = true := by
  rw [Array.all_eq_true]
  intro j hj
  have hj' : j < 3 := by rw [gens_tabs.1] at hj; exact hj
  rw [← getElem!_pos _ j hj, (gens_tabs.2 j hj').1]
  match j, hj' with
  | 0, _ => exact cos_of (i := 8) (by decide) (by decide)
  | 1, _ => exact cos_of (i := 9) (by decide) (by decide)
  | 2, _ => exact memCos_of (k := 1) (tkF (k := 1) (by decide)).1 (by decide) (by decide) kCosT

theorem enum_of {k cnt m : Nat} {G GI T PL : Nat → Nat} {A : Array Table}
    (hA : TabsOK 820 10 k G A)
    (hi : ∀ j < k, invEqK 820 10 (mask 10) (820 * 10) (G j) (GI j) = true ∧
      canonK 820 10 (mask 10) (820 * 10) (GI j) = true)
    (e : mulClosureH 820 A closureCap = hRec 820 10 cnt T PL)
    (ht : mulTreeOK 820 A (hRec 820 10 cnt T PL).1 (hRec 820 10 cnt T PL).2.1
      (hRec 820 10 cnt T PL).2.2 = true)
    (hdd : hkeysDistinct 820 (hRec 820 10 cnt T PL).1.toList = true)
    (hcl : closedOK 820 (A ++ A.map (invT 820)) (hRec 820 10 cnt T PL).1 = true) (hm : cnt = m) :
    CFSG.EvenSporadicStandard.HSStd.U43.enumOK A closureCap m = true := by
  unfold CFSG.EvenSporadicStandard.HSStd.U43.enumOK
  rw [e, permInv_all hA hi, ht, hcl, hdd, hRec_size, hm]
  simp

theorem coverP_spec {NC NQ lo len : Nat} {C Q W : Nat → Nat}
    (h : coverP 820 10 NC C NQ Q W lo len = true) :
    ∀ i, lo ≤ i → i < lo + len → i < NC → ord3P 820 10 (C i) = true → W i < NQ ∧ Q (W i) = C i := by
  intro i h1 h2 h3 h4
  unfold coverP at h
  rw [List.all_eq_true] at h
  have h5 := h (i - lo) (List.mem_range.2 (by omega))
  rw [CFSG.KC.BfsPin.strictB_app, show Nat.add lo (i - lo) = i by change lo + (i - lo) = i; omega]
    at h5
  rw [show Nat.blt i NC = true from Nat.blt_eq.mpr h3, h4] at h5
  simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h5
  exact h5

theorem cover_ok : CFSG.EvenSporadicStandard.HSStd.U43.coverOK dZ4.cg dZ4.y0 closureCap = true := by
  obtain ⟨eC, -, -, -, hTC⟩ := recCs
  obtain ⟨e, ht, -⟩ := conjH_sound (k := 4) (cap := 50000) sz cg_CY.1 cg_CY.2 tY hd.2.2.2.2
    (fun i hi => penumSl_spec cyPe i (Nat.zero_le _) (by omega) hi)
    (fun i hi => slK_spec cyHs i (Nat.zero_le _) (by omega) hi)
  have hk : closureCap = 50000 := rfl
  unfold CFSG.EvenSporadicStandard.HSStd.U43.coverOK
  rw [hk, e, ht, Bool.true_and, ← hk, eC, Array.all_eq_true]
  intro i hi
  have hi' : i < Z4C.cnt := by simpa [hRec] using hi
  rw [← getElem!_pos _ i hi, hRec_get hi']
  have hc := hTC i hi'
  rw [show tabT (unpack 820 10 (Z4C.T i)) = tb 820 10 (Z4C.T i) from rfl, ordTest3_tb sz hc]
  cases ho : ord3P 820 10 (Z4C.T i)
  · rfl
  · obtain ⟨hq, hq2⟩ := coverP_spec ((fa cv_all : ∀ s < 8, cv s = true) (i / 360) (Nat.div_lt_of_lt_mul (by have := cnt.1; omega)))
      i (Nat.mul_div_le i 360) (by
        have := Nat.lt_mul_div_succ i (show 0 < 360 by norm_num)
        change i < 360 * (i / 360) + 360
        rw [Nat.mul_succ] at this
        exact this) hi' ho
    rw [Bool.not_true, Bool.false_or]
    refine memT_of hq ?_
    rw [hq2]
    exact tblEq_self hc

theorem caseCheck_true : caseCheck dZ4 = true := by
  obtain ⟨c0, -, v0⟩ := inF (i := 0) (by decide)
  obtain ⟨c1, -, v1⟩ := inF (i := 1) (by decide)
  obtain ⟨eC, tC, dC, clC', -⟩ := recCs
  obtain ⟨eY, tY', dY, clY', hTY⟩ := recYs
  have hg := gG_T
  have hsol := kSol
  unfold solK at hsol
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hsol
  have hE : yEnum dZ4 = Array.ofFn (n := Z4Y.cnt) fun i => tb 820 10 (Z4Y.T i.val) := by
    unfold yEnum
    rw [eY]
    rfl
  have hsl := solList_tb sz hTY c0 c1 tT tY hE
  unfold caseCheck
  rw [show dZ4.ysz = 1944 from rfl, show dZ4.nsol = 12 from rfl, show dZ4.sizeG = 13063680 from rfl]
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
    have hp1 : p.1 < Z4Y.cnt := by
      unfold solsP at hp
      simp only [List.mem_flatMap, List.mem_filter, List.mem_range, List.mem_map] at hp
      obtain ⟨i, ⟨hi, -⟩, j, -, rfl⟩ := hp
      exact hi
    have hp2 : p.2 < Z4Y.cnt := by
      unfold solsP at hp
      simp only [List.mem_flatMap, List.mem_filter, List.mem_range, List.mem_map] at hp
      obtain ⟨i, -, j, ⟨hj, -⟩, rfl⟩ := hp
      exact hj
    simp only [Function.comp_apply, beq_iff_eq]
    rw [cent5Of_tb sz hTY c0 tT hE (hTY _ hp1) (hTY _ hp2)]
    exact hsol.2 p hp

end CertificateChecks.KernelHSStd.U43Z4

end
