
module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.SporSch.Pair.GenNF
public import CFSG.Certificates.Kernel.SporSch.PairClSound
public import CFSG.Certificates.Kernel.Spor.PrimSound
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

#ks_rawchain CertificateChecks.KernelSporSch.PMcL 275 9 16 CFSG.Sporadic.Schreier.mclStrongArrs
  CFSG.Sporadic.Schreier.PairMcL.baseArr 2 CertificateChecks.KernelSporSch.PMcLWords.D

#kss_nfclos CertificateChecks.KernelSporSch.PMcLC CertificateChecks.KernelSporSch.PMcL 275 9 5
  CFSG.Sporadic.Schreier.PairMcL.levels CFSG.Sporadic.Schreier.PairMcL.bs
  CFSG.Sporadic.Schreier.PairMcL.gens CFSG.Sporadic.Schreier.PairMcL.gensInv
  CFSG.Sporadic.Schreier.PairMcL.cl 30000 10 32 32

namespace CertificateChecks.KernelSporSch.PMcLCheck

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative CFSG.Sporadic.Schreier.PairMcL
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CertificateChecks.KernelSporSch

theorem tab : hexTabK PMcLText.chars 4 275 9 13 PMcL.S = true := by quickRfl

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

theorem gbind : allN 2 (fun l => bAnd(Nat.beq (PMcLC.G l) (PMcL.S l), Nat.beq (PMcLC.GI l) (PMcL.SI l))) =
    true := by quickRfl

theorem gperm : allN 2 (fun l => permOK 275 9 (mask 9) (275 * 9) (PMcLC.G l) (PMcLC.GI l)) = true := by
  quickRfl

private theorem get0_pair {α : Type} [Inhabited α] (a b : α) : #[a, b][0]! = a := rfl

private theorem get1_pair {α : Type} [Inhabited α] (a b : α) : #[a, b][1]! = b := rfl

theorem gens_eq (l : Nat) (hl : l < 2) :
    gens[l]! = unpack 275 9 (PMcLC.G l) ∧ gensInv[l]! = unpack 275 9 (PMcLC.GI l) := by
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 (allN_spec gbind l hl)
  rw [Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2]
  have hS := arr_eq l (by omega)
  have hI := (invEqK_sound (allN_spec perm l (by omega))).1
  have hsz : mclStrongArrs.size = 13 := by simp [mclStrongArrs]
  refine ⟨?_, ?_⟩
  · rw [gens]
    rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
    · rw [get0_pair]
      exact hS
    · rw [get1_pair]
      exact hS
  · rw [← hI, ← hS]
    have hm : (rawInvs 275 mclStrongArrs)[l]! = invCand 275 mclStrongArrs[l]! := by
      rw [rawInvs, getElem!_pos (mclStrongArrs.map (invCand 275)) l (by simp [hsz]; omega),
        getElem!_pos mclStrongArrs l (by omega), Array.getElem_map]
    rw [← hm, gensInv]
    rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
    · exact get0_pair _ _
    · exact get1_pair _ _

theorem hg : gens.size = 2 ∧ gensInv.size = 2 ∧
    ∀ l < 2, gens[l]! = unpack 275 9 (PMcLC.G l) ∧ gensInv[l]! = unpack 275 9 (PMcLC.GI l) :=
  ⟨rfl, rfl, gens_eq⟩

@[expose] noncomputable def RP0 : List Nat := [PMcL.S 0]

theorem rep0_eq : wA = RP0.map (unpack 275 9) := wA_eq

theorem canon0 : canonL 275 9 RP0 = true := by quickRfl
theorem ltbs : ltL 275 bs = true := by quickRfl
theorem st0 : startNF 275 9 PMcL.LR PMcL.TRI 5 bs RP0 (rowGet PMcLC.XT0 108 0) = true := by quickRfl
theorem k0 : Nat.beq (nfKey 275 9 PMcL.LR PMcL.TR 5 bs (nfX 5 (rowGet PMcLC.XT0 108 0)))
    (wordKey 275 9 bs RP0) = true := by quickRfl
theorem c00 : Nat.beq (PMcLC.C0 0) 1 = true := by quickRfl
theorem c0N : Nat.beq (PMcLC.C0 (Nat.mul PMcLC.nS0 32)) PMcLC.c0 = true := by quickRfl
theorem sSz : Nat.beq PMcLC.c0 22275 = true := by quickRfl
theorem o0 : ordWK 275 9 bs RP0 2 = true := by quickRfl

theorem ok0 : ClosNFOK 275 9 13 5 PMcL.BP PMcL.S PMcL.SI PMcL.LR PMcL.TR PMcL.TRI bs 2 PMcLC.G PMcLC.GI
    RP0 PMcLC.c0 30000 PMcLC.nS0 32 10 PMcLC.nB0 32 (rowGet PMcLC.XT0 108) (rowGet PMcLC.WT0 40)
    PMcLC.C0 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    fun l hl => allN_spec gperm l hl, canon0, ltbs, st0, k0, PMcLC.hnf0,
    Nat.eq_of_beq_eq_true c00, Nat.eq_of_beq_eq_true c0N, PMcLC.hrun0⟩

theorem cl_eq : cl = [(wA, closureOf wA)] := rfl

set_option maxHeartbeats 2000000 in
theorem facts : (rawChainOK 275 (mclStrongArrs.extract 0 2) mclStrongArrs baseArr mclWords 4 = true ∧
      rawOrbitSizes 275 mclStrongArrs baseArr = [275, 112, 81, 45, 8])
    ∧ (ordB bs wA 2 = true ∧ ordB bs wB 5 = true ∧ ordB bs (patW wA wB [false, true]) 11 = true ∧
      ordB bs (patW wA wB commPat) 5 = true)
    ∧ ((∀ c ∈ cl, ordB bs c.1 2 = true) ∧
      (∀ c ∈ cl, closureOK levels bs gens gensInv c.1 c.2.1 c.2.2.1 c.2.2.2 = true) ∧
      keysDistinctNF 275 levels bs (cl.map fun c => c.2.1) = true ∧
      (cl.map fun c => c.2.1.size).sum = 22275) := by
  have srt := keysK_sound
    (cs := [(PMcLC.c0, nfKeyX 275 9 PMcL.LR PMcL.TR 5 bs PMcLC.XT0 108)]) (by decide) (by decide)
    PMcLC.hsrt
  have hD0 := nodup_of_strictInc_mergeSort srt
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at hD0
  have cl0 := closNF_sound (bs := bs) (rep := wA) binds perm PMcL.hl rfl hg rep0_eq ok0 hD0
  refine ⟨⟨?_, ?_⟩, ?_, ⟨?_, ?_, ?_, ?_⟩⟩
  · rw [words_eq]
    exact rawChainK_sound (NS := 18) (CH := 16) binds PMcL.head PMcL.hl (by decide) PMcL.hs
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
  · intro c hc
    rw [cl_eq] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    subst hc
    rw [rep0_eq]
    exact ordWK_sound o0
  · intro c hc
    rw [cl_eq] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    subst hc
    exact cl0.1
  · rw [cl_eq]
    unfold keysDistinctNF
    simp only [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [closureOf, PairMcL.levels, cl0.2.2]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at srt
    exact srt
  · rw [cl_eq]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    rw [closureOf, PairMcL.levels, cl0.2.1]
    exact Nat.eq_of_beq_eq_true sSz

end CertificateChecks.KernelSporSch.PMcLCheck

end
