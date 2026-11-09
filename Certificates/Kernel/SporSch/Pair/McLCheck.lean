
module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.SporSch.Pair.GenNF
public import CFSG.Certificates.Kernel.SporSch.PairClSound
public import CFSG.Certificates.Kernel.Spor.PrimSound
public import CFSG.Certificates.Kernel.Spor.RawPos
public import CFSG.Certificates.Kernel.Spor.Loops
public import CFSG.Sporadic.Schreier.PairMcLCheckInputs
meta import CFSG.Sporadic.Schreier.PairMcLCheckInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.PMcLWords

@[expose] def D : List (List Int) :=
  [[-2, -2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 2], [-2, -2, 1, -2, -2, -2, 1, 2, 2, 2, 1, 2, 2],
    [4, 3, 1, 4, 3], [1, 3, 1, 4, 1, 3, 1], [6, -5, 6, 5, 5, 6, 5, 5, 5],
    [-2, -2, 1, -2, 1, 2, 1, 2, 2, 1, 2, 1, 2], [3, -8, 4, 8], [-9, -5, 6, 9],
    [-10, 7, -10, 7, 10, 7, 10], [-5, 9, 6, 5], [7, -12, 10, 12]]

end CertificateChecks.KernelSporSch.PMcLWords

#ks_chars CertificateChecks.KernelSporSch.PMcLText CFSG.Sporadic.Schreier.mclStrongHex

#ks_rawchain CertificateChecks.KernelSporSch.PMcL 275 9 0 CFSG.Sporadic.Schreier.mclStrongArrs
  CFSG.Sporadic.Schreier.PairMcL.baseArr 2 CertificateChecks.KernelSporSch.PMcLWords.D

namespace CertificateChecks.KernelSporSch.PMcLCheck

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative CFSG.Sporadic.Schreier.PairMcL
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CertificateChecks.KernelSporSch

theorem tab : hexTabK PMcLText.chars 4 275 9 13 PMcL.S = true := by quickRfl

@[expose] noncomputable def Q (i s : Nat) : Prop :=
  schPK 275 9 PMcL.S PMcL.SI PMcL.LR PMcL.TR PMcL.TRI 13 2 PMcL.BP 5 i (s * 55) 55 = true

theorem sp0_0 : Q 0 0 := by unfold Q; quickRfl
theorem sp0_1 : Q 0 1 := by unfold Q; quickRfl
theorem sp0_2 : Q 0 2 := by unfold Q; quickRfl
theorem sp0_3 : Q 0 3 := by unfold Q; quickRfl
theorem sp0_4 : Q 0 4 := by unfold Q; quickRfl
theorem sp1_0 : Q 1 0 := by unfold Q; quickRfl
theorem sp1_1 : Q 1 1 := by unfold Q; quickRfl
theorem sp1_2 : Q 1 2 := by unfold Q; quickRfl
theorem sp1_3 : Q 1 3 := by unfold Q; quickRfl
theorem sp1_4 : Q 1 4 := by unfold Q; quickRfl
theorem sp2_0 : Q 2 0 := by unfold Q; quickRfl
theorem sp2_1 : Q 2 1 := by unfold Q; quickRfl
theorem sp2_2 : Q 2 2 := by unfold Q; quickRfl
theorem sp2_3 : Q 2 3 := by unfold Q; quickRfl
theorem sp2_4 : Q 2 4 := by unfold Q; quickRfl
theorem sp3_0 : Q 3 0 := by unfold Q; quickRfl
theorem sp3_1 : Q 3 1 := by unfold Q; quickRfl
theorem sp3_2 : Q 3 2 := by unfold Q; quickRfl
theorem sp3_3 : Q 3 3 := by unfold Q; quickRfl
theorem sp3_4 : Q 3 4 := by unfold Q; quickRfl
theorem sp4_0 : Q 4 0 := by unfold Q; quickRfl
theorem sp4_1 : Q 4 1 := by unfold Q; quickRfl
theorem sp4_2 : Q 4 2 := by unfold Q; quickRfl
theorem sp4_3 : Q 4 3 := by unfold Q; quickRfl
theorem sp4_4 : Q 4 4 := by unfold Q; quickRfl

theorem hsL {i : Nat} (h0 : Q i 0) (h1 : Q i 1) (h2 : Q i 2) (h3 : Q i 3) (h4 : Q i 4) :
    ∀ s < 5, Q i s :=
  forall_lt_succ (forall_lt_succ (forall_lt_succ (forall_lt_succ (forall_lt_succ forall_lt_zero
    h0) h1) h2) h3) h4

theorem hsP : ∀ i < 5, ∀ s < 5, Q i s :=
  forall_lt_succ (forall_lt_succ (forall_lt_succ (forall_lt_succ (forall_lt_succ forall_lt_zero
    (hsL sp0_0 sp0_1 sp0_2 sp0_3 sp0_4)) (hsL sp1_0 sp1_1 sp1_2 sp1_3 sp1_4))
    (hsL sp2_0 sp2_1 sp2_2 sp2_3 sp2_4)) (hsL sp3_0 sp3_1 sp3_2 sp3_3 sp3_4))
    (hsL sp4_0 sp4_1 sp4_2 sp4_3 sp4_4)

theorem perm : allN 13 (fun j => permOK 275 9 (mask 9) (275 * 9) (PMcL.S j) (PMcL.SI j)) = true := by
  quickRfl

theorem arr_eq (j : Nat) (hj : j < 13) : mclStrongArrs[j]! = unpack 275 9 (PMcL.S j) := by
  have h := hexTabK_sound tab j hj
  rw [← PMcLText.eq] at h
  rw [mclStrongArrs, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
  exact h

theorem binds : Binds 275 9 PMcL.S 13 5 PMcL.BP mclStrongArrs baseArr :=
  ⟨by decide, by decide, by decide, by simp [mclStrongArrs], arr_eq, by decide, by decide⟩

theorem words_eq : mclWords = CFSG.Sporadic.Schreier.Co3.Native.wordsArr 2 13 PMcLWords.D := by
  decide

theorem o1 : ordWK 275 9 bs [PMcL.S 0] 2 = true := by quickRfl
theorem o2 : ordWK 275 9 bs [PMcL.S 1] 5 = true := by quickRfl
theorem o3 : ordWK 275 9 bs [PMcL.S 1, PMcL.S 0] 11 = true := by quickRfl
theorem o4 : ordWK 275 9 bs [PMcL.S 1, PMcL.S 1, PMcL.S 1, PMcL.S 1, PMcL.S 0, PMcL.S 1, PMcL.S 0] 5 =
    true := by quickRfl

theorem wA_eq : wA = [unpack 275 9 (PMcL.S 0)] := by
  rw [wA, arr_eq 0 (by omega)]

theorem wB_eq : wB = [unpack 275 9 (PMcL.S 1)] := by
  rw [wB, arr_eq 1 (by omega)]

set_option maxHeartbeats 2000000 in
theorem facts : (rawChainOK 275 (mclStrongArrs.extract 0 2) mclStrongArrs baseArr mclWords 4 = true ∧
      rawOrbitSizes 275 mclStrongArrs baseArr = [275, 112, 81, 45, 8])
    ∧ (ordB bs wA 2 = true ∧ ordB bs wB 5 = true ∧ ordB bs (patW wA wB [false, true]) 11 = true ∧
      ordB bs (patW wA wB commPat) 5 = true) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [words_eq]
    exact rawChainPK_sound (NS := 5) (CH := 55) binds PMcL.head PMcL.hl (by decide) hsP
  · rw [rawOrbitSizesK_sound binds perm PMcL.hl]
    decide +kernel
  · have e3 : patW [unpack 275 9 (PMcL.S 0)] [unpack 275 9 (PMcL.S 1)] [false, true] =
        [PMcL.S 1, PMcL.S 0].map (unpack 275 9) := rfl
    have e4 : patW [unpack 275 9 (PMcL.S 0)] [unpack 275 9 (PMcL.S 1)] commPat =
        [PMcL.S 1, PMcL.S 1, PMcL.S 1, PMcL.S 1, PMcL.S 0, PMcL.S 1, PMcL.S 0].map (unpack 275 9) :=
      rfl
    have e1 : [unpack 275 9 (PMcL.S 0)] = [PMcL.S 0].map (unpack 275 9) := rfl
    have e2 : [unpack 275 9 (PMcL.S 1)] = [PMcL.S 1].map (unpack 275 9) := rfl
    rw [wA_eq, wB_eq, e3, e4, e1, e2]
    exact ⟨ordWK_sound o1, ordWK_sound o2, ordWK_sound o3, ordWK_sound o4⟩

end CertificateChecks.KernelSporSch.PMcLCheck

end
