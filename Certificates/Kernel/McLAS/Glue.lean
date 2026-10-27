module

public import Certificates.Kernel.McLAS.Tabs
public import Certificates.Kernel.Census.McLChain
public import Certificates.Kernel.Sporadic.OddCore.CentGlue
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue3
public import Certificates.Data.Kernel.McLAS.Slices
public import Certificates.Data.Kernel.McLAS.Pair
public import CFSG.Sporadic.Recognition.LyonsLocalMcLInputs
public import CFSG.Certificates.Kernel.Spor.SiftEq
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.PcompFacts
import CFSG.Certificates.Kernel.Spor.RawOrbHead
public import CFSG.Certificates.Kernel.Spor.RawSlSound
import CFSG.Certificates.Kernel.Spor.RawOrbGrp

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMcLAS

open CFSG.Sporadic.Recognition.McLAS CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.KC.Enum CFSG.KS CFSG.KS.Raw
open CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KC.BfsPin CFSG.Monster.B.Co2.Native
open CFSG.KS.McLAS CFSG.KC.Misc.HexFlat CFSG.Sporadic.Schreier

abbrev Cn (X : Nat) : Prop := canonK 275 9 (mask 9) (275 * 9) X = true

theorem k_base : bAnd(szOK 275 9, bAnd(canonK 275 9 (mask 9) (275 * 9) idK,
    bAnd(CFSG.KS.Prim.idK 275 9 (mask 9),
    bAnd(allN 11 (fun k => bAnd(canonK 275 9 (mask 9) (275 * 9) (TT.F k),
      canonK 275 9 (mask 9) (275 * 9) (TTI k))),
    bAnd(allN 22 (fun k => bAnd(canonK 275 9 (mask 9) (275 * 9) (NT.F k),
      canonK 275 9 (mask 9) (275 * 9) (NTI k))),
    bAnd(allN 15 (fun k => bAnd(canonK 275 9 (mask 9) (275 * 9) (TL.F k),
      canonK 275 9 (mask 9) (275 * 9) (TLI k))),
    bAnd(canonK 275 9 (mask 9) (275 * 9) (PT.F 0), canonK 275 9 (mask 9) (275 * 9) (PTI 0)))))))) =
    true := by
  quickRfl

theorem base : szOK 275 9 = true ∧ Cn idK ∧ CFSG.KS.Prim.idK 275 9 (mask 9) = true ∧
    allN 11 (fun k => bAnd(canonK 275 9 (mask 9) (275 * 9) (TT.F k),
      canonK 275 9 (mask 9) (275 * 9) (TTI k))) = true ∧
    allN 22 (fun k => bAnd(canonK 275 9 (mask 9) (275 * 9) (NT.F k),
      canonK 275 9 (mask 9) (275 * 9) (NTI k))) = true ∧
    allN 15 (fun k => bAnd(canonK 275 9 (mask 9) (275 * 9) (TL.F k),
      canonK 275 9 (mask 9) (275 * 9) (TLI k))) = true ∧
    Cn (PT.F 0) ∧ Cn (PTI 0) := by
  simpa only [bAnd_iff] using k_base

theorem hn : szOK 275 9 = true := base.1

theorem hidc : Cn idK := base.2.1

theorem hidA : idA 275 = unpack 275 9 idK := (idK_sound base.2.2.1).symm

theorem hid : idT 275 = tabT (unpack 275 9 idK) := by rw [idT_tabT, hidA]

theorem perm_parts : allN 11 (fun k => invEqK 275 9 (mask 9) (275 * 9) (TT.F k) (TTI k)) = true ∧
    allN 22 (fun k => invEqK 275 9 (mask 9) (275 * 9) (NT.F k) (NTI k)) = true ∧
    allN 15 (fun k => invEqK 275 9 (mask 9) (275 * 9) (TL.F k) (TLI k)) = true ∧
    invEqK 275 9 (mask 9) (275 * 9) (PT.F 0) (PTI 0) = true := by
  simpa only [bAnd_iff] using perms

theorem TTc {k : Nat} (hk : k < 11) : Cn (TT.F k) :=
  ((bAnd_iff _ _).1 (allN_spec base.2.2.2.1 k hk)).1
theorem TTIc {k : Nat} (hk : k < 11) : Cn (TTI k) :=
  ((bAnd_iff _ _).1 (allN_spec base.2.2.2.1 k hk)).2
theorem NTc {k : Nat} (hk : k < 22) : Cn (NT.F k) :=
  ((bAnd_iff _ _).1 (allN_spec base.2.2.2.2.1 k hk)).1
theorem NTIc {k : Nat} (hk : k < 22) : Cn (NTI k) :=
  ((bAnd_iff _ _).1 (allN_spec base.2.2.2.2.1 k hk)).2
theorem TLc {k : Nat} (hk : k < 15) : Cn (TL.F k) :=
  ((bAnd_iff _ _).1 (allN_spec base.2.2.2.2.2.1 k hk)).1
theorem TLIc {k : Nat} (hk : k < 15) : Cn (TLI k) :=
  ((bAnd_iff _ _).1 (allN_spec base.2.2.2.2.2.1 k hk)).2

theorem TTinv {k : Nat} (hk : k < 11) : invEqK 275 9 (mask 9) (275 * 9) (TT.F k) (TTI k) = true :=
  allN_spec perm_parts.1 k hk
theorem NTinv {k : Nat} (hk : k < 22) : invEqK 275 9 (mask 9) (275 * 9) (NT.F k) (NTI k) = true :=
  allN_spec perm_parts.2.1 k hk
theorem TLinv {k : Nat} (hk : k < 15) : invEqK 275 9 (mask 9) (275 * 9) (TL.F k) (TLI k) = true :=
  allN_spec perm_parts.2.2.1 k hk

theorem tabTT {k : Nat} (hk : k < 11) : threeTbl k = tabT (unpack 275 9 (TT.F k)) := by
  rw [← threeTbl_eq hk, tabT_natArr]
theorem tabNT {k : Nat} (hk : k < 22) : nrmTbl k = tabT (unpack 275 9 (NT.F k)) := by
  rw [← nrmTbl_eq hk, tabT_natArr]
theorem tabTL {k : Nat} (hk : k < 15) : tlTbl k = tabT (unpack 275 9 (TL.F k)) := by
  rw [← tlTbl_eq hk, tabT_natArr]
theorem tabPT : pairTbl = tabT (unpack 275 9 (PT.F 0)) := by
  rw [← pairTbl_eq, tabT_natArr]

theorem mclStrongArrs_get (j : Nat) (hj : j < 13) :
    mclStrongArrs[j]! = unpack 275 9 (CertificateChecks.KernelCensus.McLS.F j) := by
  unfold mclStrongArrs
  rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn, CertificateChecks.KernelCensus.McLS.eq]
  exact hexTable_sound CertificateChecks.KernelCensus.McLS.all j hj

theorem fs : ∀ j < 13, CertificateChecks.KernelCensus.McLS.F j =
    CertificateChecks.KernelCensus.McLC.S j := by decide +kernel

theorem binds : Binds 275 9 CertificateChecks.KernelCensus.McLC.S 13 5
    CertificateChecks.KernelCensus.McLC.BP mclStrongArrs PairMcL.baseArr := by
  refine ⟨by norm_num, by norm_num, by norm_num, by simp [mclStrongArrs], fun j hj => ?_,
    by decide +kernel, by decide +kernel⟩
  rw [← fs j hj]
  exact mclStrongArrs_get j hj

theorem hperm : allN 13 (fun j => permOK 275 9 (mask 9) (275 * 9)
    (CertificateChecks.KernelCensus.McLC.S j) (CertificateChecks.KernelCensus.McLC.SI j)) =
    true := by
  quickRfl

@[expose] noncomputable def sK (X : Nat) : Bool :=
  siftK 275 9 (mask 9) (275 * 9) (pidn 275 9) CertificateChecks.KernelCensus.McLC.LR
    CertificateChecks.KernelCensus.McLC.TRI CertificateChecks.KernelCensus.McLC.BP 5 0 X

theorem sift_eq {X : Nat} (hX : Cn X) : mclSift (tabT (unpack 275 9 X)) = sK X := by
  unfold mclSift PairMcL.levels
  rw [natArr_tabT hX]
  obtain ⟨-, -, h2, h3⟩ := CFSG.KS.PF.canon_facts hX
  exact CFSG.KS.Raw.siftK_eq binds hperm CertificateChecks.KernelCensus.McLC.hl rfl h2
    (CFSG.KS.Raw.Orb.allN_iff.2 fun i hi => Nat.blt_eq.mpr (h3 i hi))

theorem fixedPtCount_eq {X : Nat} (hX : Cn X) : fixedPtCount 275 (tabT (unpack 275 9 X)) = fixK X := by
  unfold fixedPtCount fixK cntBelowK
  rw [cntK_eq, countP_range_lt _ (by norm_num : 275 ≤ 64 * 5), ← List.countP_eq_length_filter]
  apply List.countP_congr
  intro i hi
  have hi' : i < 275 := List.mem_range.1 hi
  rw [ap_tabT _ (unpack_lt hX), CFSG.KS.Raw.Orb.unpack_get hi']
  by_cases e : pg 9 (mask 9) X i = i
  · simp [e, Nat.beq_refl]
  · simp only [e, beq_iff_eq, false_iff]
    exact fun h => e (Nat.eq_of_beq_eq_true h)

theorem pows (X : Nat) : Pows 275 9 X (fun e => pwK e X) := by
  refine ⟨rfl, fun e => ?_⟩
  change strictN (pwK e X) (fun a => pcK X a) = _
  rw [strictN_app']
  rfl

theorem ordTest_eq {X : Nat} (hX : Cn X) (m : Nat) :
    ordTest 275 m (tabT (unpack 275 9 X)) =
      (Nat.beq (pwK m X) idK && (divParts m).all fun e => !Nat.beq (pwK e X) idK) :=
  ordTest_unpack (pows X) hidA hidc hX m

theorem pairSel_eq {A X : Nat} (hA : Cn A) (hX : Cn X) :
    pairSel (tabT (unpack 275 9 A)) (tabT (unpack 275 9 X)) = pairSelK A X := by
  unfold pairSel pairSelK
  rw [ordTest_eq hX, fixedPtCount_eq hX, hid, tblEq_unpack hX hidc, tblEq_unpack hX hA,
    compT_unpack hA hA, tblEq_unpack hX (canonK_pcomp hA hA)]
  have hd : divParts 3 = [1] := by decide
  have e5 : (fixK X == 5) = Nat.beq (fixK X) 5 := by
    by_cases h : fixK X = 5
    · rw [h]
      rfl
    · rw [beq_false_of_ne h]
      exact (Bool.eq_false_iff.2 fun h' => h (Nat.eq_of_beq_eq_true h')).symm
  have ep : pcK A A = pcomp 275 9 (mask 9) A A := rfl
  rw [hd, e5, ep]
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  cases Nat.beq (pwK 3 X) idK <;> cases Nat.beq (pwK 1 X) idK <;> cases Nat.beq (fixK X) 5 <;>
    cases Nat.beq X idK <;> cases Nat.beq X A <;> cases Nat.beq X (pcomp 275 9 (mask 9) A A) <;> rfl

theorem all_hRec {cnt : Nat} {T PL : Nat → Nat} {p : Table → Bool}
    (h : ∀ i < cnt, p (tabT (unpack 275 9 (T i))) = true) :
    (hRec 275 9 cnt T PL).1.all p = true := by
  rw [Array.all_eq_true]
  intro i hi
  simp only [hRec, Array.size_ofFn] at hi
  simp only [hRec, Array.getElem_ofFn]
  exact h i hi

theorem rec_spec {conj : Bool} {k cnt NS : Nat} {G GI T PL POS SRT SRI HS HSI : Nat → Nat}
    (hc : cnt ≤ 200 * NS)
    (h : ∀ s < NS, recSlK conj G GI k cnt T PL POS SRT SRI HS HSI (Nat.mul s 200) 200 = true) :
    (∀ i < cnt, penumPtK 275 9 (mask 9) (275 * 9) conj G GI k cnt T PL POS SRT SRI i = true) ∧
      (∀ i < cnt, hsortPtK 275 9 (mask 9) cnt T HS HSI i = true) := by
  have key : ∀ i < cnt, (i / 200) * 200 ≤ i ∧ i < (i / 200) * 200 + 200 ∧ i / 200 < NS :=
    fun i hi => ⟨Nat.div_mul_le_self i 200, by omega, by omega⟩
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := key i hi
    have hs := (bAnd_iff _ _).1 (h (i / 200) h3)
    exact penumSl_spec hs.1 i h1 h2 hi
  · obtain ⟨h1, h2, h3⟩ := key i hi
    have hs := (bAnd_iff _ _).1 (h (i / 200) h3)
    exact slK_spec hs.2 i h1 h2 hi

theorem join4 {f : Nat → Bool} {a b c d : Nat} (h0 : ∀ s < a, f s = true)
    (h1 : ∀ s < b, f (Nat.add a s) = true) (h2 : ∀ s < c, f (Nat.add (a + b) s) = true)
    (h3 : ∀ s < d, f (Nat.add (a + b + c) s) = true) : ∀ s < a + b + c + d, f s = true := by
  intro s hs
  by_cases e0 : s < a
  · exact h0 s e0
  have add_sub : ∀ x, x ≤ s → Nat.add x (s - x) = s := fun x hx => by
    change x + (s - x) = s
    omega
  by_cases e1 : s < a + b
  · have h := h1 (s - a) (by omega)
    rwa [add_sub a (by omega)] at h
  by_cases e2 : s < a + b + c
  · have h := h2 (s - (a + b)) (by omega)
    rwa [add_sub (a + b) (by omega)] at h
  · have h := h3 (s - (a + b + c)) (by omega)
    rwa [add_sub (a + b + c) (by omega)] at h

end CertificateChecks.KernelMcLAS

end
