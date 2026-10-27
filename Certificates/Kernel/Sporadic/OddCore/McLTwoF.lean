module

public import Certificates.Kernel.Sporadic.OddCore.McLTwo
public import Certificates.Kernel.Sporadic.OddCore.MulHGlue
public import Certificates.Kernel.Census.McLN
public import CFSG.Certificates.Kernel.J2CoverSound
public import CFSG.Sporadic.Recognition.McLASThreeLocalInputs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.McLTwo

open CFSG.Sporadic.Recognition.McLAS CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.KC.Enum CFSG.KS CFSG.KS.Raw
open CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KC.BfsPin CertificateChecks.KernelCensus

theorem base : szOK 275 9 = true ∧ canonK 275 9 (mask 9) (275 * 9) (pidn 275 9) = true ∧
    CFSG.KS.Prim.idK 275 9 (mask 9) = true ∧
    allN 7 (fun j => bAnd(cK (McLTwoH.F j), bAnd(Nat.beq (McLTwoS.GI j) (McLTwoH.F j),
      bAnd(Nat.beq (McLTwoS.G j) (pidn 275 9), bAnd(cK (McLTwoSI j),
        invEqK 275 9 (mask 9) (275 * 9) (McLTwoH.F j) (McLTwoSI j)))))) = true ∧
    McLTwoS.cnt = 128 ∧ penumHdK (pidn 275 9) McLTwoS.cnt 200 McLTwoS.T McLTwoS.PL = true := by
  have h := base_ok
  simp only [bAnd_iff] at h
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := h
  exact ⟨a1, a2, a3, a4, Nat.eq_of_beq_eq_true a5, a6⟩

theorem gen {j : Nat} (hj : j < 7) : canonK 275 9 (mask 9) (275 * 9) (McLTwoH.F j) = true ∧
    McLTwoS.GI j = McLTwoH.F j ∧ McLTwoS.G j = pidn 275 9 ∧
    canonK 275 9 (mask 9) (275 * 9) (McLTwoSI j) = true ∧
    invEqK 275 9 (mask 9) (275 * 9) (McLTwoH.F j) (McLTwoSI j) = true := by
  have h := allN_spec base.2.2.2.1 j hj
  simp only [bAnd_iff] at h
  obtain ⟨a1, a2, a3, a4, a5⟩ := h
  exact ⟨a1, Nat.eq_of_beq_eq_true a2, Nat.eq_of_beq_eq_true a3, a4, a5⟩

theorem tab {j : Nat} (hj : j < 7) : sylTwoGens[j]! = tabT (unpack 275 9 (McLTwoH.F j)) := by
  have h := CFSG.KC.Misc.HexFlat.hexT_sound McLTwoH.all (by norm_num) j hj
  rw [← McLTwoH.eq] at h
  unfold sylTwoGens
  rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
  change sylTwoTbl j = _
  unfold sylTwoTbl
  rw [← h, tabT_natArr]

theorem s_tabs : TabsOK 275 9 7 McLTwoS.GI sylTwoGens := by
  refine ⟨by simp [sylTwoGens], fun j hj => ?_⟩
  rw [(gen hj).2.1]
  exact ⟨tab hj, (gen hj).1⟩

theorem s_invs : ∀ j < 7, invEqK 275 9 (mask 9) (275 * 9) (McLTwoS.GI j) (McLTwoSI j) = true ∧
    canonK 275 9 (mask 9) (275 * 9) (McLTwoSI j) = true := fun j hj => by
  rw [(gen hj).2.1]
  exact ⟨(gen hj).2.2.2.2, (gen hj).2.2.2.1⟩

theorem s_pe : ∀ i < McLTwoS.cnt, penumPtK 275 9 (mask 9) (275 * 9) true McLTwoS.G McLTwoS.GI 7
    McLTwoS.cnt McLTwoS.T McLTwoS.PL McLTwoS.POS McLTwoS.SRT McLTwoS.SRI i = true :=
  fun i hi => penumSl_spec sE i (Nat.zero_le _) (by omega) hi

theorem s_hs : ∀ i < McLTwoS.cnt,
    hsortPtK 275 9 (mask 9) McLTwoS.cnt McLTwoS.T McLTwoS.HS McLTwoS.HSI i = true :=
  fun i hi => slK_spec sH i (Nat.zero_le _) (by omega) hi

theorem s_cl : ∀ c < McLTwoS.cnt * (7 + 7), findPtK McLTwoS.cnt McLTwoS.T
    (prodQK 275 9 (mask 9) (7 + 7) McLTwoS.T (bothK 7 McLTwoS.GI McLTwoSI)) McLTwoCl c = true :=
  fun c hc => slK_spec sCl c (Nat.zero_le _) (by change c < Nat.mul McLTwoS.cnt 14; omega)
    (by change c < Nat.mul McLTwoS.cnt 14; omega)

theorem sift_eq {X : Nat} (hX : canonK 275 9 (mask 9) (275 * 9) X = true) :
    mclSift (tabT (unpack 275 9 X)) =
      siftK 275 9 (mask 9) (275 * 9) (pidn 275 9) McLC.LR McLC.TRI McLC.BP 5 0 X := by
  unfold mclSift
  rw [natArr_tabT hX]
  exact CFSG.KC.J2Cover.siftK_eq McLK.binds McLK.hperm McLC.hl hX

theorem closure_eq : mulClosureH 275 sylTwoGens 200 = hRec 275 9 McLTwoS.cnt McLTwoS.T McLTwoS.PL ∧
    mulTreeOK 275 sylTwoGens (hRec 275 9 McLTwoS.cnt McLTwoS.T McLTwoS.PL).1
      (hRec 275 9 McLTwoS.cnt McLTwoS.T McLTwoS.PL).2.1
      (hRec 275 9 McLTwoS.cnt McLTwoS.T McLTwoS.PL).2.2 = true ∧
    hkeysDistinct 275 (hRec 275 9 McLTwoS.cnt McLTwoS.T McLTwoS.PL).1.toList = true :=
  mulH_sound base.1 (fun j hj => (gen hj).2.2.1) s_tabs base.2.2.2.2.2 s_pe s_hs

theorem hT : ∀ i < McLTwoS.cnt, canonK 275 9 (mask 9) (275 * 9) (McLTwoS.T i) = true :=
  fun i hi => penumPt_canon (s_pe i hi)

theorem sub_ok : subEnumOK 275 200 128 mclSift sylTwoGens = true := by
  obtain ⟨e, ht, hd⟩ := closure_eq
  unfold subEnumOK
  simp only [Bool.and_eq_true]
  rw [e]
  refine ⟨⟨⟨⟨?_, ht⟩, closedOK_of hT (TabsOK_both s_tabs s_invs) s_cl⟩, hd⟩, ?_⟩
  · rw [Array.all_eq_true]
    intro j hj
    have hj' : j < 7 := by simpa [sylTwoGens] using hj
    have hx := tab hj'
    rw [getElem!_pos sylTwoGens j hj] at hx
    obtain ⟨c1, -, -, c4, c5⟩ := gen hj'
    rw [hx]
    simp only [Bool.and_eq_true]
    refine ⟨⟨permOK_unpack c1 c5, ?_⟩, ?_⟩
    · rw [sift_eq c1]
      exact allN_spec sift_ok j hj'
    · rw [invT_unpack (lt_of_canonK c4) c5]
      exact invOK_unpack c1 c4 c5
  · rw [hRec_size, base.2.2.2.2.1]
    exact beq_self_eq_true 128

theorem inv_ok : sylTwoEnum.all (fun e => invOK 275 e (invT 275 e)) = true := by
  have e' : sylTwoEnum = (hRec 275 9 McLTwoS.cnt McLTwoS.T McLTwoS.PL).1 := by
    unfold sylTwoEnum
    rw [closure_eq.1]
  rw [e', Array.all_eq_true]
  intro i hi
  have hi' : i < McLTwoS.cnt := by simpa [hRec] using hi
  have h := allN_spec sInv i (by rw [← base.2.2.2.2.1]; exact hi')
  simp only [bAnd_iff] at h
  simp only [hRec, Array.getElem_ofFn]
  rw [invT_unpack (lt_of_canonK h.1) h.2]
  exact invOK_unpack (hT i hi') h.1 h.2

end CertificateChecks.KernelSpor.McLTwo

end
