module

public import Certificates.Kernel.Sporadic.OddCore.S8147KC0
public import Certificates.Kernel.Sporadic.OddCore.S8147KC3
public import Certificates.Kernel.Sporadic.OddCore.S8147KC4
public import Certificates.Kernel.Sporadic.OddCore.S8147KC
public import Certificates.Kernel.Sporadic.OddCore.S8147KD
public import Certificates.Kernel.Sporadic.OddCore.S8147C
public import CFSG.Certificates.Kernel.BfsPinAlg
public import CFSG.Certificates.Kernel.BfsPinSliceSound
public import CFSG.Certificates.Kernel.BfsPinBaseSound
public import CFSG.Certificates.Kernel.BfsPinSetSound
public import CFSG.Certificates.Kernel.Spor.PcompFacts
public import CFSG.Certificates.Kernel.B3S3KSound
public import CFSG.Certificates.Kernel.Misc.ArrEnumUnpack
public import CFSG.Certificates.Kernel.Spor.HNAOrbSound
public import CFSG.Certificates.Kernel.PermToolSound
public import CFSG.Certificates.Kernel.Spor.CardBaseSep
public import CFSG.Certificates.Kernel.Spor.EnumBaseSound
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
public import CFSG.RankThree.Native.SuzFiveCheckInputs
import all CFSG.RankThree.Native.SuzFiveData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.S8147

open CFSG.RankThree.Native CFSG.Sporadic.SuzOddCore CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Monster.B.Fischer CFSG.Monster.B.Mathieu CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim
open CFSG.KC.BfsPin CFSG.KC.Misc.ArrEnum CFSG.KS.HNA CFSG.KC.PermTool CFSG.KS.EnumBase
open CFSG.KS.PEnum (r32)
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.OddCore

theorem szk : szOK 1782 11 = true := by quickRfl

theorem upk_size (P : Nat) : (unpack 1782 11 P).size = 1782 := by simp [unpack]

theorem upk_get {P x : Nat} (hx : x < 1782) : (unpack 1782 11 P)[x]! = pg 11 (mask 11) P x :=
  unpack_get' hx

theorem pB {P : Nat} (h : PP 1782 11 P) : permB 1782 11 P = true := permB_of_pp h

theorem eqU {P Q : Nat} (hP : PP 1782 11 P) (hQ : PP 1782 11 Q) :
    eqA 1782 (unpack 1782 11 P) (unpack 1782 11 Q) = Nat.beq P Q := eqA_PP hP hQ

theorem cmpU {P Q : Nat} (hP : PP 1782 11 P) (hQ : PP 1782 11 Q) :
    compA 1782 (unpack 1782 11 P) (unpack 1782 11 Q) = unpack 1782 11 (pcomp 1782 11 (mask 11) P Q) :=
  compA_PP hP hQ

theorem idU : idA 1782 = unpack 1782 11 (pidn 1782 11) := idA_eq szk

theorem powU {P : Nat} (hP : PP 1782 11 P) (e : Nat) :
    powArr 1782 (unpack 1782 11 P) e = unpack 1782 11 (CFSG.KC.B3S3K.pw 1782 11 P e) :=
  pow_unpack' szk (pB hP) e

theorem pwPP {P : Nat} (hP : PP 1782 11 P) (e : Nat) : PP 1782 11 (CFSG.KC.B3S3K.pw 1782 11 P e) :=
  pp_ppow szk hP e

theorem invU {P : Nat} (hP : PP 1782 11 P) :
    invCand 1782 (unpack 1782 11 P) = unpack 1782 11 (pinvS 1782 11 (mask 11) P) := invCand_PP hP

theorem validU {P : Nat} (hP : PP 1782 11 P) : validA 1782 (unpack 1782 11 P) = true :=
  validA_unpack (CFSG.KS.PinvS.permOK_pinvS hP.1 hP.2)

theorem commAU {P Q : Nat} (hP : PP 1782 11 P) (hQ : PP 1782 11 Q) :
    commA 1782 (unpack 1782 11 P) (unpack 1782 11 Q) =
      Nat.beq (pcomp 1782 11 (mask 11) P Q) (pcomp 1782 11 (mask 11) Q P) := by
  unfold commA
  rw [cmpU hP hQ, cmpU hQ hP, eqU (hP.mul hQ) (hQ.mul hP)]

theorem conjU {P Q : Nat} (hP : PP 1782 11 P) (hQ : PP 1782 11 Q) :
    conjA 1782 (unpack 1782 11 P) (unpack 1782 11 Q) = unpack 1782 11 (cnjK P Q) :=
  conj_unpack' szk (pB hP) (pB hQ)

theorem cnjPP {P Q : Nat} (hP : PP 1782 11 P) (hQ : PP 1782 11 Q) : PP 1782 11 (cnjK P Q) :=
  hP.mul (hQ.mul hP.inv)

theorem commU {P Q : Nat} (hP : PP 1782 11 P) (hQ : PP 1782 11 Q) :
    commutatorA 1782 (unpack 1782 11 P) (unpack 1782 11 Q) = unpack 1782 11 (commP 1782 11 P Q) :=
  (commutatorA_unpack hP hQ).1

theorem commPP {P Q : Nat} (hP : PP 1782 11 P) (hQ : PP 1782 11 Q) : PP 1782 11 (commP 1782 11 P Q) :=
  (commutatorA_unpack hP hQ).2

theorem inM_C {P : Nat} (hc : canonK 1782 11 (mask 11) (1782 * 11) P = true) :
    suzFiveInM (unpack 1782 11 P) = msift P := by
  unfold suzFiveInM
  exact inM_eq rfl hc

theorem inT_U {P : Nat} (hP : PP 1782 11 P) : suzFiveInT (unpack 1782 11 P) = inTK P := by
  unfold suzFiveInT inTK
  rw [inM_C hP.1, Suz2306.vArr_eq, compA_unpack canonV hP.1, inM_C (canonK_pcomp canonV hP.1),
    CFSG.KS.EnumBase.bIf_eq]
  cases msift P <;> simp

theorem fiveArr_eq {k : Nat} (hk : k < 18) : suzFiveArr k = unpack 1782 11 (SFvT.F k) := by
  have h := CFSG.KC.Misc.HexFlat.hexTable_sound SFvT.all k hk
  rw [← SFvT.eq] at h
  exact h

theorem fv_PP {k : Nat} (hk : k < 18) : PP 1782 11 (SFvT.F k) :=
  PP_of_permOK szk (allN_spec fvP k hk)

theorem line_eq {i : Nat} (hi : i < 6) : suzFiveLineArr i = unpack 1782 11 (SFvT.F i) := by
  unfold suzFiveLineArr
  rw [show suzFiveLineIdx[i]! = i by interval_cases i <;> rfl]
  exact fiveArr_eq (by omega)

theorem keys_lt : ∀ p ∈ suzFiveKeys, p < 1782 := by decide

theorem enumF {ng N L K fuel : Nat} {gs : Array (Array Nat)} {G T E S C SKT : Nat → Nat}
    (hs : gs.size = ng) (hg : ∀ k < ng, gs[k]! = unpack 1782 11 (G k)) (hNL : N = L * K)
    (hL : 0 < L)
    (hh : (szOK 1782 11 && allN ng (fun k => canonK 1782 11 (mask 11) (Nat.mul 1782 11) (G k)) &&
      Nat.beq (T 0) (pidn 1782 11) && Nat.beq (C 0) 1 && Nat.beq (C K) N) = true)
    (hd : distinctK N T S = true)
    (hk : keysSK 1782 11 [0, 1, 2, 3, 4, 8, 5, 6] N T (CFSG.KS.HNA.listUp SKT N) = true)
    (hp : allN ng (fun k => permOK 1782 11 (mask 11) (1782 * 11) (G k)
      (pinvS 1782 11 (mask 11) (G k))) = true)
    (hsl : ∀ s < K, bAnd(canonSl 1782 11 T L s, runSl 1782 11 ng G T E L C s) = true)
    (hf : N ≤ fuel) :
    enumOK 1782 gs suzFiveKeys (enumBfs 1782 gs suzFiveKeys fuel) = true ∧
      (enumBfs 1782 gs suzFiveKeys fuel).pts.size = N ∧
      (∀ i < N, (enumBfs 1782 gs suzFiveKeys fuel).pts[i]! = unpack 1782 11 (T i)) ∧
      ∀ i < N, PP 1782 11 (T i) := by
  simp only [Bool.and_eq_true] at hh
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hh
  have hcs : ∀ s < K, canonSl 1782 11 T L s = true := fun s hs => by
    have := hsl s hs
    rw [bAnd_eq, Bool.and_eq_true] at this
    exact this.1
  have hrs : ∀ s < K, runSl 1782 11 ng G T E L C s = true := fun s hs => by
    have := hsl s hs
    rw [bAnd_eq, Bool.and_eq_true] at this
    exact this.2
  have hb : bfsK 1782 11 ng G N T E S = true :=
    bfsK_of_slices hNL hL h1 h2 hcs h3 hd (Nat.eq_of_beq_eq_true h4) (Nat.eq_of_beq_eq_true h5) hrs
  have hpp : ∀ k < ng, permOK 1782 11 (mask 11) (1782 * 11) (G k)
      (pinvS 1782 11 (mask 11) (G k)) = true := fun k hk => allN_spec hp k hk
  obtain ⟨e1, e2, e3⟩ := CFSG.KC.B3S3K.enum_of (n := 1782) (w := 11) ⟨hs, hg⟩ hpp hb keys_lt hk hf
  exact ⟨e1, e2, e3, PP_pts hb hpp⟩

theorem enumO {m ng N L K fuel : Nat} {gs : Array (Array Nat)} {G T E S C : Nat → Nat}
    (hs : gs.size = ng) (hg : ∀ k < ng, gs[k]! = unpack m 3 (G k)) (hNL : N = L * K)
    (hL : 0 < L)
    (hh : (szOK m 3 && allN ng (fun k => canonK m 3 (mask 3) (Nat.mul m 3) (G k)) &&
      Nat.beq (T 0) (pidn m 3) && Nat.beq (C 0) 1 && Nat.beq (C K) N) = true)
    (hd : distinctK N T S = true)
    (hp : allN ng (fun k => permOK m 3 (mask 3) (m * 3) (G k) (pinvS m 3 (mask 3) (G k))) = true)
    (hsl : ∀ s < K, bAnd(canonSl m 3 T L s, runSl m 3 ng G T E L C s) = true) (hf : N ≤ fuel) :
    enumOK m gs (List.range m) (enumBfs m gs (List.range m) fuel) = true ∧
      (enumBfs m gs (List.range m) fuel).pts.size = N := by
  simp only [Bool.and_eq_true] at hh
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hh
  have hcs : ∀ s < K, canonSl m 3 T L s = true := fun s hs => by
    have := hsl s hs
    rw [bAnd_eq, Bool.and_eq_true] at this
    exact this.1
  have hrs : ∀ s < K, runSl m 3 ng G T E L C s = true := fun s hs => by
    have := hsl s hs
    rw [bAnd_eq, Bool.and_eq_true] at this
    exact this.2
  have hb : bfsK m 3 ng G N T E S = true :=
    bfsK_of_slices hNL hL h1 h2 hcs h3 hd (Nat.eq_of_beq_eq_true h4) (Nat.eq_of_beq_eq_true h5) hrs
  have hpp : ∀ k < ng, permOK m 3 (mask 3) (m * 3) (G k) (pinvS m 3 (mask 3) (G k)) = true :=
    fun k hk => allN_spec hp k hk
  refine ⟨enumOK_of_bfsK hs hg hpp hb hf, ?_⟩
  rw [enumBfs_pts hs hg hb hf, Array.size_ofFn]

theorem toList_eq {a : Array (Array Nat)} {N : Nat} {T : Nat → Nat} (hs : a.size = N)
    (h : ∀ i < N, a[i]! = unpack 1782 11 (T i)) :
    a.toList = (List.range N).map fun i => unpack 1782 11 (T i) := by
  apply List.ext_getElem
  · rw [Array.length_toList, hs, List.length_map, List.length_range]
  · intro i h1 h2
    have hi : i < N := by rwa [Array.length_toList, hs] at h1
    rw [Array.getElem_toList, List.getElem_map, List.getElem_range, ← h i hi,
      getElem!_pos a i (by rw [hs]; exact hi)]

theorem memK_any {a : Array (Array Nat)} {N : Nat} {T : Nat → Nat} (hs : a.size = N)
    (h : ∀ i < N, a[i]! = unpack 1782 11 (T i)) (hT : ∀ i < N, PP 1782 11 (T i)) {X : Nat}
    (hX : PP 1782 11 X) (hm : memK N T X = true) : a.toList.any (eqA 1782 (unpack 1782 11 X)) = true := by
  rw [toList_eq hs h, List.any_map, List.any_eq_true]
  unfold memK at hm
  rw [anyNP_eq, List.any_eq_true] at hm
  obtain ⟨i, hi, e⟩ := hm
  refine ⟨i, hi, ?_⟩
  rw [Function.comp_apply, eqU hX (hT i (List.mem_range.1 hi))]
  exact e

theorem qArrs_size : suzFiveQArrs.size = 2 := by simp [suzFiveQArrs, suzFiveSylowIdx]

theorem qArrs_get {k : Nat} (hk : k < 2) : suzFiveQArrs[k]! = unpack 1782 11 (SFQ.G k) := by
  unfold suzFiveQArrs
  rw [getElem!_pos _ k (by simp [suzFiveSylowIdx]; omega), Array.getElem_map]
  have e : suzFiveSylowIdx[k]'(by simpa [suzFiveSylowIdx] using hk) = k := by
    interval_cases k <;> rfl
  rw [e, fiveArr_eq (by omega), ← Nat.eq_of_beq_eq_true (allN_spec gQ k hk)]

theorem qArrs_fv {k : Nat} (hk : k < 2) : suzFiveQArrs[k]! = unpack 1782 11 (SFvT.F k) := by
  rw [qArrs_get hk, Nat.eq_of_beq_eq_true (allN_spec gQ k hk)]

theorem lines_get {j : Nat} (hj : j < 6) : suzFiveLines[j]! = unpack 1782 11 (SFvT.F j) := by
  unfold suzFiveLines
  rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
  exact line_eq hj

theorem qEnum : enumOK 1782 suzFiveQArrs suzFiveKeys suzFiveQCert = true ∧
    suzFiveQCert.pts.size = 25 ∧
    (∀ i < 25, suzFiveQCert.pts[i]! = unpack 1782 11 (SFQ.T i)) ∧ ∀ i < 25, PP 1782 11 (SFQ.T i) :=
  enumF (L := 25) (K := 1) (E := SFQ.E) qArrs_size (fun k hk => qArrs_get hk) (by norm_num)
    (by norm_num) hQ dQ kQ pQ
    (fun s hs => by
      have e : s = 0 := by omega
      subst e
      exact sQ) (by norm_num)

theorem qCheck : suzFiveQCheck suzFiveQCert suzFiveLines = true := by
  obtain ⟨e1, e2, e3, e4⟩ := qEnum
  have hF : ∀ j < 6, PP 1782 11 (SFvT.F j) := fun j hj => fv_PP (by omega)
  unfold suzFiveQCheck
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨e1, e2⟩, ?_⟩, qArrs_size⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [qArrs_fv (by norm_num), qArrs_fv (by norm_num), commAU (hF 0 (by norm_num)) (hF 1 (by norm_num))]
    exact qComm
  · rw [qArrs_fv (by norm_num), inM_C (hF 0 (by norm_num)).1]
    have := qInM
    rw [bAnd_eq, Bool.and_eq_true] at this
    exact this.1
  · rw [qArrs_fv (by norm_num), inM_C (hF 1 (by norm_num)).1]
    have := qInM
    rw [bAnd_eq, Bool.and_eq_true] at this
    exact this.2
  · rw [CFSG.Monster.B.Co2.allLt_iff]
    intro k hk
    rw [e3 k hk, powU (e4 k hk), idU, eqU (pwPP (e4 k hk) 5) (PP.id szk)]
    exact allN_spec qPow k hk
  · rw [CFSG.Monster.B.Co2.allLt_iff]
    intro k hk
    have h := allN_spec qCover k hk
    rw [CFSG.KS.EnumBase.strictB_eq, bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true,
      Nat.blt_eq, Nat.blt_eq] at h
    obtain ⟨hj, he, hq⟩ := h
    rw [Bool.or_eq_true]
    right
    rw [List.any_eq_true]
    refine ⟨Nat.div (r32 SFQW k) 8, List.mem_range.2 hj, ?_⟩
    rw [List.any_eq_true]
    refine ⟨Nat.mod (r32 SFQW k) 8, List.mem_range.2 he, ?_⟩
    rw [e3 k hk, lines_get hj, powU (hF _ hj), eqU (e4 k hk) (pwPP (hF _ hj) _)]
    exact hq
  · rw [CFSG.Monster.B.Co2.allLt_iff]
    intro j hj
    rw [CFSG.Monster.B.Co2.allLt_iff]
    intro j' hj'
    rw [Bool.or_eq_true]
    by_cases e : j = j'
    · exact Or.inl (beq_iff_eq.2 e)
    · right
      rw [CFSG.Monster.B.Co2.allLt_iff]
      intro f hf
      have h0 := allN_spec (allN_spec qDist j' hj') f hf
      rw [CFSG.KS.EnumBase.strictB_eq] at h0
      have h := allN_spec h0 j hj
      rw [CFSG.KS.EnumBase.bIf_eq, if_neg (by rw [beq_eq]; simpa using e)] at h
      rw [lines_get hj, lines_get hj', powU (hF j' hj'), eqU (hF j hj) (pwPP (hF j' hj') f)]
      unfold nB at h
      rw [CFSG.KS.EnumBase.bIf_eq] at h
      cases hb : Nat.beq (SFvT.F j) (CFSG.KC.B3S3K.pw 1782 11 (SFvT.F j') f)
      · rfl
      · rw [hb, if_pos rfl] at h
        exact absurd h Bool.false_ne_true
  · rw [CFSG.Monster.B.Co2.allLt_iff]
    intro j hj
    have h := allN_spec qLines j hj
    rw [bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true] at h
    obtain ⟨h1, h2, h3⟩ := h
    rw [lines_get hj, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
    refine ⟨⟨⟨validU (hF j hj), ?_⟩, ?_⟩, memK_any e2 e3 e4 (hF j hj) h3⟩
    · rw [powU (hF j hj), idU, eqU (pwPP (hF j hj) 5) (PP.id szk)]
      exact h1
    · rw [idU, eqU (hF j hj) (PP.id szk)]
      unfold nB at h2
      rw [CFSG.KS.EnumBase.bIf_eq] at h2
      cases hb : Nat.beq (SFvT.F j) (pidn 1782 11)
      · rfl
      · rw [hb, if_pos rfl] at h2
        exact absurd h2 Bool.false_ne_true

theorem cIdx_get {i : Nat} (hi : i < 6) : suzFiveCentIdx[i]! = #[6 + 2 * i, 7 + 2 * i] := by
  interval_cases i <;> rfl

theorem cArrs_size {i : Nat} (hi : i < 6) : (suzFiveCArrs i).size = 2 := by
  unfold suzFiveCArrs
  rw [Array.size_map, cIdx_get hi]
  rfl

theorem cArrs_fv {i k : Nat} (hi : i < 6) (hk : k < 2) :
    (suzFiveCArrs i)[k]! = unpack 1782 11 (SFvT.F (Nat.add (6 + 2 * i) k)) := by
  unfold suzFiveCArrs
  rw [cIdx_get hi, getElem!_pos _ k (by simp; omega), Array.getElem_map]
  have e : (#[6 + 2 * i, 7 + 2 * i] : Array Nat)[k]'(by simp; omega) = Nat.add (6 + 2 * i) k := by
    interval_cases k
    · rfl
    · change 7 + 2 * i = 6 + 2 * i + 1
      omega
  rw [e, fiveArr_eq (by change 6 + 2 * i + k < 18; omega)]

theorem cCheck_of {i N : Nat} {G T : Nat → Nat} (hi : i < 6)
    (hG : ∀ k < 2, G k = SFvT.F (Nat.add (6 + 2 * i) k))
    (he : enumOK 1782 (suzFiveCArrs i) suzFiveKeys (suzFiveCCert i) = true ∧
      (suzFiveCCert i).pts.size = N ∧
      (∀ j < N, (suzFiveCCert i).pts[j]! = unpack 1782 11 (T j)) ∧ ∀ j < N, PP 1782 11 (T j))
    (hN : suzFiveCentOrders[i]! = N)
    (hk : allN 2 (fun k => bAnd(Nat.beq (pcomp 1782 11 (mask 11) (G k) (SFvT.F i))
      (pcomp 1782 11 (mask 11) (SFvT.F i) (G k)), inTK (G k))) = true)
    (hm : memK N T (SFvT.F i) = true) :
    suzFiveCCheck (suzFiveCArrs i) (suzFiveLineArr i) (suzFiveCCert i) suzFiveCentOrders[i]! =
      true := by
  obtain ⟨e1, e2, e3, e4⟩ := he
  have hX := fv_PP (k := i) (by omega)
  unfold suzFiveCCheck
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨e1, by rw [e2, hN]⟩, ?_⟩, by rw [line_eq hi]; exact validU hX⟩, ?_⟩
  · rw [CFSG.Monster.B.Co2.allLt_iff]
    intro k hk2
    rw [cArrs_size hi] at hk2
    have h := allN_spec hk k hk2
    rw [bAnd_eq, Bool.and_eq_true] at h
    have hGk : PP 1782 11 (G k) := by
      rw [hG k hk2]
      exact fv_PP (by change 6 + 2 * i + k < 18; omega)
    rw [cArrs_fv hi hk2, ← hG k hk2, line_eq hi, Bool.and_eq_true, commAU hGk hX, inT_U hGk]
    exact h
  · rw [line_eq hi]
    exact memK_any e2 e3 e4 hX hm

@[expose] def Good (st : SuzFiveBfsState) : Prop :=
  ∀ K, st.2.getD K [] = ((List.range st.1.size).filter fun k => suzFiveKey st.1[k]! == K).reverse

theorem push_lt' {a : Array (Array Nat)} {x : Array Nat} {k : Nat} (hk : k < a.size) :
    (a.push x)[k]! = a[k]! := by
  rw [getElem!_pos (a.push x) k (by simp; omega), Array.getElem_push_lt hk, getElem!_pos a k hk]

theorem push_eq' {a : Array (Array Nat)} {x : Array Nat} : (a.push x)[a.size]! = x := by
  rw [getElem!_pos (a.push x) a.size (by simp), Array.getElem_push_eq]

theorem good_add {st : SuzFiveBfsState} (h : Good st) (p : Array Nat) : Good (suzFiveAdd st p) := by
  intro K
  unfold suzFiveAdd
  dsimp only
  rw [Std.HashMap.getD_insert, Array.size_push, List.range_succ, List.filter_append,
    List.reverse_append]
  have e1 : ((List.range st.1.size).filter fun k => suzFiveKey (st.1.push p)[k]! == K) =
      ((List.range st.1.size).filter fun k => suzFiveKey st.1[k]! == K) :=
    List.filter_congr fun k hk => by rw [push_lt' (List.mem_range.1 hk)]
  rw [e1, List.filter_singleton, push_eq', ← h K]
  by_cases hK : suzFiveKey p = K
  · subst hK
    simp [h (suzFiveKey p)]
  · have hb : (suzFiveKey p == K) = false := by simpa using hK
    rw [hb]
    simp

theorem good_empty : Good ((#[], ∅) : SuzFiveBfsState) := by
  intro K
  simp

theorem key_eq_of_eqA {a b : Array Nat} (h : eqA 1782 a b = true) : suzFiveKey a = suzFiveKey b := by
  unfold suzFiveKey keyA
  congr 1
  apply List.map_congr_left
  intro x hx
  have hx' : x < 1782 := by simp at hx; omega
  exact beq_iff_eq.1 (allLt_spec h hx')

theorem seen_iff {st : SuzFiveBfsState} (h : Good st) (p : Array Nat) :
    suzFiveSeen st p = true ↔ ∃ k < st.1.size, eqA 1782 st.1[k]! p = true := by
  unfold suzFiveSeen
  rw [h (suzFiveKey p), List.any_eq_true]
  constructor
  · rintro ⟨k, hk, e⟩
    rw [List.mem_reverse, List.mem_filter, List.mem_range] at hk
    exact ⟨k, hk.1, e⟩
  · rintro ⟨k, hk, e⟩
    refine ⟨k, ?_, e⟩
    rw [List.mem_reverse, List.mem_filter, List.mem_range]
    exact ⟨hk, beq_iff_eq.2 (key_eq_of_eqA e)⟩

@[expose] def stepF (x : Array Nat) (st : SuzFiveBfsState) (m : Array Nat) : SuzFiveBfsState :=
  if suzFiveSeen st (compA 1782 m x) then st else suzFiveAdd st (compA 1782 m x)

theorem visit_lit (a b c d x : Array Nat) (st : SuzFiveBfsState) :
    suzFiveVisit #[a, b, c, d] st x = stepF x (stepF x (stepF x (stepF x st a) b) c) d := by
  unfold suzFiveVisit
  rw [← Array.foldl_toList]
  rfl

theorem stepF_new {st : SuzFiveBfsState} (h : Good st) {m x : Array Nat}
    (hn : ∀ k < st.1.size, eqA 1782 st.1[k]! (compA 1782 m x) = false) :
    stepF x st m = suzFiveAdd st (compA 1782 m x) := by
  unfold stepF
  rw [if_neg]
  intro hs
  obtain ⟨k, hk, e⟩ := (seen_iff h _).1 hs
  rw [hn k hk] at e
  exact Bool.false_ne_true e

theorem stepF_prefix (x : Array Nat) (st : SuzFiveBfsState) (m : Array Nat) :
    ∃ L : Array (Array Nat), (stepF x st m).1 = st.1 ++ L := by
  unfold stepF
  split
  · exact ⟨#[], by simp⟩
  · exact ⟨#[compA 1782 m x], by simp [suzFiveAdd]⟩

theorem stepF_good {st : SuzFiveBfsState} (h : Good st) (x m : Array Nat) : Good (stepF x st m) := by
  unfold stepF
  split
  · exact h
  · exact good_add h _

theorem visit_prefix (x : Array Nat) (ms : Array (Array Nat)) :
    ∀ st : SuzFiveBfsState, ∃ L : Array (Array Nat), (suzFiveVisit ms st x).1 = st.1 ++ L := by
  intro st
  change ∃ L : Array (Array Nat), (ms.foldl (fun st m => stepF x st m) st).1 = st.1 ++ L
  rw [← Array.foldl_toList]
  induction ms.toList generalizing st with
  | nil => exact ⟨#[], by simp⟩
  | cons m ms ih =>
    rw [List.foldl_cons]
    obtain ⟨L1, e1⟩ := stepF_prefix x st m
    obtain ⟨L2, e2⟩ := ih (stepF x st m)
    refine ⟨L1 ++ L2, ?_⟩
    rw [e2, e1, Array.append_assoc]

theorem loop_prefix (ms : Array (Array Nat)) :
    ∀ fuel pos (st : SuzFiveBfsState), ∃ L : Array (Array Nat),
      (suzFiveBfsLoop ms fuel pos st).1 = st.1 ++ L := by
  intro fuel
  induction fuel with
  | zero => intro pos st; exact ⟨#[], by simp [suzFiveBfsLoop]⟩
  | succ f ih =>
    intro pos st
    rw [suzFiveBfsLoop]
    split
    · next hp =>
      obtain ⟨L1, e1⟩ := visit_prefix st.1[pos] ms st
      obtain ⟨L2, e2⟩ := ih (pos + 1) (suzFiveVisit ms st st.1[pos])
      exact ⟨L1 ++ L2, by rw [e2, e1, Array.append_assoc]⟩
    · exact ⟨#[], by simp⟩

theorem upk_inj {p q : Nat} (hp : canonK 1782 11 (mask 11) (1782 * 11) p = true)
    (hq : canonK 1782 11 (mask 11) (1782 * 11) q = true)
    (h : unpack 1782 11 p = unpack 1782 11 q) : p = q := by
  obtain ⟨-, hw, hp1, -⟩ := CFSG.KS.PF.canon_facts hp
  obtain ⟨-, -, hq1, -⟩ := CFSG.KS.PF.canon_facts hq
  refine CFSG.KS.PF.eq_of_fields (CFSG.KS.PF.w_pos hw) hp1 hq1 fun i hi => ?_
  rw [← upk_get hi, ← upk_get hi, h]

theorem pcomp_id {M : Nat} (hM : PP 1782 11 M) : pcomp 1782 11 (mask 11) M (pidn 1782 11) = M := by
  obtain ⟨-, hw, hp1, -⟩ := CFSG.KS.PF.canon_facts (hM.mul (PP.id szk)).1
  obtain ⟨-, -, hq1, -⟩ := CFSG.KS.PF.canon_facts hM.1
  refine CFSG.KS.PF.eq_of_fields (CFSG.KS.PF.w_pos hw) hp1 hq1 fun i hi => ?_
  rw [CFSG.KS.PF.pg_pcomp (by norm_num) hi, CFSG.KS.PF.pg_pidn (by norm_num) (by norm_num) hi]

theorem nB_eq (b : Bool) : nB b = !b := by cases b <;> rfl

theorem preChk_spec {G0 G1 : Nat} (h : preChk G0 G1 = true) :
    Nat.beq (pidn 1782 11) G0 = false ∧ Nat.beq (pidn 1782 11) G1 = false ∧
    Nat.beq (pidn 1782 11) (pinvS 1782 11 (mask 11) G0) = false ∧
    Nat.beq (pidn 1782 11) (pinvS 1782 11 (mask 11) G1) = false ∧ Nat.beq G0 G1 = false ∧
    Nat.beq G0 (pinvS 1782 11 (mask 11) G0) = false ∧ Nat.beq G0 (pinvS 1782 11 (mask 11) G1) = false ∧
    Nat.beq G1 (pinvS 1782 11 (mask 11) G0) = false ∧ Nat.beq G1 (pinvS 1782 11 (mask 11) G1) = false ∧
    Nat.beq (pinvS 1782 11 (mask 11) G0) (pinvS 1782 11 (mask 11) G1) = false := by
  unfold preChk at h
  simp only [CFSG.KS.EnumBase.strictB_eq, bAnd_eq, Bool.and_eq_true, nB_eq, Bool.not_eq_true'] at h
  exact h

theorem ne_of_beq {P Q : Nat} (hP : PP 1782 11 P) (hQ : PP 1782 11 Q) (h : Nat.beq P Q = false) :
    unpack 1782 11 P ≠ unpack 1782 11 Q := by
  intro e
  rw [upk_inj hP.1 hQ.1 e, Nat.beq_refl] at h
  exact absurd h (by decide)

theorem eqA_ne {P Q : Nat} (hP : PP 1782 11 P) (hQ : PP 1782 11 Q) (h : Nat.beq P Q = false) :
    eqA 1782 (unpack 1782 11 P) (unpack 1782 11 Q) = false := by
  rw [eqU hP hQ]
  exact h

theorem beq_comm' {P Q : Nat} (h : Nat.beq P Q = false) : Nat.beq Q P = false := by
  rw [Bool.eq_false_iff] at h ⊢
  intro e
  exact h (by rw [Nat.eq_of_beq_eq_true e, Nat.beq_refl])

theorem contains_false {a : Array (Array Nat)} {x : Array Nat} (h : ∀ y ∈ a, y ≠ x) :
    a.contains x = false := by
  rw [Bool.eq_false_iff]
  intro hc
  exact h x (Array.contains_iff_mem.1 hc) rfl

theorem mults_gen {i : Nat} {a0 a1 b0 b1 : Array Nat} (hc : suzFiveCArrs i = #[a0, a1])
    (h0 : invCand 1782 a0 = b0) (h1 : invCand 1782 a1 = b1) (d01 : a0 ≠ a1) (d00 : a0 ≠ b0)
    (d01' : a0 ≠ b1) (d10 : a1 ≠ b0) (d11 : a1 ≠ b1) (dbb : b0 ≠ b1) :
    suzFiveMults i = #[a0, a1, b0, b1] := by
  unfold suzFiveMults
  rw [hc]
  have s1 : (#[] : Array (Array Nat)).contains a0 = false :=
    contains_false (by simp only [List.mem_toArray, List.not_mem_nil, false_imp_iff, forall_const])
  have s2 : (#[a0] : Array (Array Nat)).contains a1 = false :=
    contains_false (by
      simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false]
      rintro y rfl
      exact d01)
  have s3 : (#[a0, a1] : Array (Array Nat)).contains b0 = false :=
    contains_false (by
      simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false]
      rintro y (rfl | rfl)
      · exact d00
      · exact d10)
  have s4 : (#[a0, a1, b0] : Array (Array Nat)).contains b1 = false :=
    contains_false (by
      simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false]
      rintro y (rfl | rfl | rfl)
      · exact d01'
      · exact d11
      · exact dbb)
  rw [← Array.foldl_toList, Array.toList_append, Array.toList_map, List.toList_toArray]
  simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, h0, h1,
    List.foldl_cons, List.foldl_nil, s1, Bool.false_eq_true, ↓reduceIte, List.push_toArray, s2, s3,
    s4]

theorem mults_eq {i G0 G1 : Nat}
    (hc : suzFiveCArrs i = #[unpack 1782 11 G0, unpack 1782 11 G1]) (hP0 : PP 1782 11 G0)
    (hP1 : PP 1782 11 G1) (hpre : preChk G0 G1 = true) :
    suzFiveMults i = #[unpack 1782 11 G0, unpack 1782 11 G1,
      unpack 1782 11 (pinvS 1782 11 (mask 11) G0), unpack 1782 11 (pinvS 1782 11 (mask 11) G1)] := by
  obtain ⟨-, -, -, -, h01, h0i0, h0i1, h1i0, h1i1, hi0i1⟩ := preChk_spec hpre
  exact mults_gen hc (invU hP0) (invU hP1) (ne_of_beq hP0 hP1 h01) (ne_of_beq hP0 hP0.inv h0i0)
    (ne_of_beq hP0 hP1.inv h0i1) (ne_of_beq hP1 hP0.inv h1i0) (ne_of_beq hP1 hP1.inv h1i1)
    (ne_of_beq hP0.inv hP1.inv hi0i1)

theorem loop_succ (ms : Array (Array Nat)) (f pos : Nat) (st : SuzFiveBfsState)
    (h : pos < st.1.size) :
    suzFiveBfsLoop ms (f + 1) pos st = suzFiveBfsLoop ms f (pos + 1) (suzFiveVisit ms st st.1[pos]) := by
  rw [suzFiveBfsLoop, dif_pos h]

theorem add_fst (st : SuzFiveBfsState) (p : Array Nat) : (suzFiveAdd st p).1 = st.1.push p := rfl

theorem visit1 {z a0 a1 b0 b1 : Array Nat} {st : SuzFiveBfsState} (hg : Good st) (hst : st.1 = #[z])
    (c0 : compA 1782 a0 z = a0) (c1 : compA 1782 a1 z = a1) (c2 : compA 1782 b0 z = b0)
    (c3 : compA 1782 b1 z = b1)
    (d1 : eqA 1782 z a0 = false) (d2 : eqA 1782 z a1 = false) (d3 : eqA 1782 a0 a1 = false)
    (d4 : eqA 1782 z b0 = false) (d5 : eqA 1782 a0 b0 = false) (d6 : eqA 1782 a1 b0 = false)
    (d7 : eqA 1782 z b1 = false) (d8 : eqA 1782 a0 b1 = false) (d9 : eqA 1782 a1 b1 = false)
    (d10 : eqA 1782 b0 b1 = false) :
    (suzFiveVisit #[a0, a1, b0, b1] st z).1 = #[z, a0, a1, b0, b1] ∧
      Good (suzFiveVisit #[a0, a1, b0, b1] st z) := by
  rw [visit_lit]
  have e1 : stepF z st a0 = suzFiveAdd st a0 := by
    rw [stepF_new hg, c0]
    intro k hk
    rw [hst] at hk ⊢
    have : k = 0 := by simpa using hk
    subst this
    rw [c0]
    exact d1
  have g1 : Good (suzFiveAdd st a0) := good_add hg a0
  have f1 : (suzFiveAdd st a0).1 = #[z, a0] := by rw [add_fst, hst]; rfl
  have e2 : stepF z (suzFiveAdd st a0) a1 = suzFiveAdd (suzFiveAdd st a0) a1 := by
    rw [stepF_new g1, c1]
    intro k hk
    rw [f1] at hk ⊢
    rw [c1]
    have : k < 2 := by simpa using hk
    interval_cases k
    · exact d2
    · exact d3
  have g2 := good_add g1 a1
  have f2 : (suzFiveAdd (suzFiveAdd st a0) a1).1 = #[z, a0, a1] := by rw [add_fst, f1]; rfl
  have e3 : stepF z (suzFiveAdd (suzFiveAdd st a0) a1) b0 =
      suzFiveAdd (suzFiveAdd (suzFiveAdd st a0) a1) b0 := by
    rw [stepF_new g2, c2]
    intro k hk
    rw [f2] at hk ⊢
    rw [c2]
    have : k < 3 := by simpa using hk
    interval_cases k
    · exact d4
    · exact d5
    · exact d6
  have g3 := good_add g2 b0
  have f3 : (suzFiveAdd (suzFiveAdd (suzFiveAdd st a0) a1) b0).1 = #[z, a0, a1, b0] := by
    rw [add_fst, f2]; rfl
  have e4 : stepF z (suzFiveAdd (suzFiveAdd (suzFiveAdd st a0) a1) b0) b1 =
      suzFiveAdd (suzFiveAdd (suzFiveAdd (suzFiveAdd st a0) a1) b0) b1 := by
    rw [stepF_new g3, c3]
    intro k hk
    rw [f3] at hk ⊢
    rw [c3]
    have : k < 4 := by simpa using hk
    interval_cases k
    · exact d7
    · exact d8
    · exact d9
    · exact d10
  rw [e1, e2, e3, e4]
  exact ⟨by rw [add_fst, f3]; rfl, good_add g3 b1⟩

theorem bfs_gen {ms : Array (Array Nat)} {fuel : Nat} {z a0 a1 b0 b1 : Array Nat}
    (hms : ms = #[a0, a1, b0, b1]) (hF : 2 ≤ fuel)
    (c0 : compA 1782 a0 z = a0) (c1 : compA 1782 a1 z = a1) (c2 : compA 1782 b0 z = b0)
    (c3 : compA 1782 b1 z = b1)
    (d1 : eqA 1782 z a0 = false) (d2 : eqA 1782 z a1 = false) (d3 : eqA 1782 a0 a1 = false)
    (d4 : eqA 1782 z b0 = false) (d5 : eqA 1782 a0 b0 = false) (d6 : eqA 1782 a1 b0 = false)
    (d7 : eqA 1782 z b1 = false) (d8 : eqA 1782 a0 b1 = false) (d9 : eqA 1782 a1 b1 = false)
    (d10 : eqA 1782 b0 b1 = false) :
    ∃ L : Array (Array Nat), (suzFiveBfsLoop ms fuel 0 (suzFiveAdd (#[], ∅) z)).1 =
      #[z, a0, a1, b0, b1] ++ L := by
  obtain ⟨F, rfl⟩ : ∃ F, fuel = F + 1 + 1 := ⟨fuel - 2, by omega⟩
  have g0 : Good (suzFiveAdd ((#[], ∅) : SuzFiveBfsState) z) := good_add good_empty z
  have f0 : (suzFiveAdd ((#[], ∅) : SuzFiveBfsState) z).1 = #[z] := rfl
  rw [loop_succ ms (F + 1) 0 _ (by rw [f0]; simp)]
  have ez : (suzFiveAdd ((#[], ∅) : SuzFiveBfsState) z).1[0]'(by rw [f0]; simp) = z := by
    simp only [f0]
    rfl
  rw [ez]
  obtain ⟨v1, g1⟩ := visit1 (st := suzFiveAdd ((#[], ∅) : SuzFiveBfsState) z) g0 f0 c0 c1 c2 c3
    d1 d2 d3 d4 d5 d6 d7 d8 d9 d10
  rw [hms]
  rw [loop_succ _ F 1 _ (by rw [v1]; simp)]
  obtain ⟨L1, e1⟩ := visit_prefix ((suzFiveVisit #[a0, a1, b0, b1]
    (suzFiveAdd ((#[], ∅) : SuzFiveBfsState) z) z).1[1]'(by rw [v1]; simp)) #[a0, a1, b0, b1]
    (suzFiveVisit #[a0, a1, b0, b1] (suzFiveAdd ((#[], ∅) : SuzFiveBfsState) z) z)
  obtain ⟨L2, e2⟩ := loop_prefix #[a0, a1, b0, b1] F 2 (suzFiveVisit #[a0, a1, b0, b1]
    (suzFiveVisit #[a0, a1, b0, b1] (suzFiveAdd ((#[], ∅) : SuzFiveBfsState) z) z)
    ((suzFiveVisit #[a0, a1, b0, b1]
      (suzFiveAdd ((#[], ∅) : SuzFiveBfsState) z) z).1[1]'(by rw [v1]; simp)))
  refine ⟨L1 ++ L2, ?_⟩
  rw [e2, e1, v1, Array.append_assoc]

end CertificateChecks.KernelSpor.S8147

end
