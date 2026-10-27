module

public import Certificates.Kernel.SporSch.Pair.J2Chain
public import Certificates.Kernel.SporSch.Pair.GenNF
public import CFSG.Certificates.Kernel.SporSch.PairClSound
public import CFSG.Certificates.Kernel.Spor.PrimSound
meta import CFSG.Sporadic.Schreier.PairJ2CheckInputs
public import Certificates.Kernel.SporSch.Pair.Nil
meta import Certificates.Kernel.SporSch.Pair.Nil
import CFSG.Certificates.Kernel.Common.Harness
public import Std.Tactic.BVDecide.Normalize.Prop

public section

set_option maxRecDepth 400000

meta def CertificateChecks.KernelSporSch.j2Rep0 : List (Array Nat) :=
  CFSG.Sporadic.Schreier.PairJ2.reps[0]!

meta def CertificateChecks.KernelSporSch.j2Rep1 : List (Array Nat) :=
  CFSG.Sporadic.Schreier.PairJ2.reps[1]!

meta def CertificateChecks.KernelSporSch.j2NoX : List (Array Nat) := []

namespace CertificateChecks.KernelSporSch.PJ2W

open CertificateChecks.KernelSporSch

@[expose] def RPnil : List Nat := []

@[expose] noncomputable def RP0 : List Nat := [PJ2.S 0]

@[expose] noncomputable def RP1 : List Nat :=
  [PJ2.S 1, PJ2.S 1, PJ2.S 0, PJ2.S 1, PJ2.S 0, PJ2.S 1, PJ2.S 1, PJ2.S 0, PJ2.S 1, PJ2.S 0,
    PJ2.S 1, PJ2.S 1, PJ2.S 0, PJ2.S 1, PJ2.S 0, PJ2.S 1, PJ2.S 1, PJ2.S 0, PJ2.S 1, PJ2.S 0,
    PJ2.S 1, PJ2.S 1, PJ2.S 0, PJ2.S 1, PJ2.S 0, PJ2.S 1, PJ2.S 1, PJ2.S 0, PJ2.S 1, PJ2.S 0]

end CertificateChecks.KernelSporSch.PJ2W

#kss_nfclos CertificateChecks.KernelSporSch.PJ2C CertificateChecks.KernelSporSch.PJ2 315 9 3
  CFSG.Sporadic.Schreier.PairJ2.levels CFSG.Sporadic.Schreier.PairJ2.bs
  CFSG.Sporadic.Schreier.PairJ2.gens CFSG.Sporadic.Schreier.PairJ2.gensInv
  CFSG.Sporadic.Schreier.PairJ2.cl 3000 10 16 32

#kss_cnt3 CertificateChecks.KernelSporSch.PJ2K2 CertificateChecks.KernelSporSch.PJ2 315 9
  CFSG.Sporadic.Schreier.PairJ2.levels CFSG.Sporadic.Schreier.PairJ2.bs 2
  CertificateChecks.KernelSporSch.j2NoX CertificateChecks.KernelSporSch.PJ2W.RPnil
  CertificateChecks.KernelSporSch.PairNil.noConds

#kss_cnt3 CertificateChecks.KernelSporSch.PJ2K30 CertificateChecks.KernelSporSch.PJ2 315 9
  CFSG.Sporadic.Schreier.PairJ2.levels CFSG.Sporadic.Schreier.PairJ2.bs 3
  CertificateChecks.KernelSporSch.j2Rep0 CertificateChecks.KernelSporSch.PJ2W.RP0
  CFSG.Sporadic.Schreier.PairJ2.conds

#kss_cnt3 CertificateChecks.KernelSporSch.PJ2K31 CertificateChecks.KernelSporSch.PJ2 315 9
  CFSG.Sporadic.Schreier.PairJ2.levels CFSG.Sporadic.Schreier.PairJ2.bs 3
  CertificateChecks.KernelSporSch.j2Rep1 CertificateChecks.KernelSporSch.PJ2W.RP1
  CFSG.Sporadic.Schreier.PairJ2.conds

namespace CertificateChecks.KernelSporSch.PJ2Check

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative CFSG.Sporadic.Schreier.PairJ2
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.PJ2W

theorem gbind : allN 2 (fun l => bAnd(Nat.beq (PJ2C.G l) (PJ2.S l), Nat.beq (PJ2C.GI l) (PJ2.SI l))) =
    true := by quickRfl

theorem gperm : allN 2 (fun l => permOK 315 9 (mask 9) (315 * 9) (PJ2C.G l) (PJ2C.GI l)) = true := by
  quickRfl

private theorem get0_pair {α : Type} [Inhabited α] (a b : α) : #[a, b][0]! = a := rfl

private theorem get1_pair {α : Type} [Inhabited α] (a b : α) : #[a, b][1]! = b := rfl

theorem gens_eq (l : Nat) (hl : l < 2) :
    gens[l]! = unpack 315 9 (PJ2C.G l) ∧ gensInv[l]! = unpack 315 9 (PJ2C.GI l) := by
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 (allN_spec gbind l hl)
  rw [Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2]
  have hS := PJ2.arr_eq l (by omega)
  have hI := (invEqK_sound (allN_spec PJ2.perm l (by omega))).1
  have hsz : (j2StrongArrs ()).size = 7 := by simp [j2StrongArrs]
  refine ⟨?_, ?_⟩
  · rw [gens]
    rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
    · rw [get0_pair]
      exact hS
    · rw [get1_pair]
      exact hS
  · rw [← hI, ← hS]
    have hm : (rawInvs 315 (j2StrongArrs ()))[l]! = invCand 315 (j2StrongArrs ())[l]! := by
      rw [rawInvs, getElem!_pos ((j2StrongArrs ()).map (invCand 315)) l (by simp [hsz]; omega),
        getElem!_pos (j2StrongArrs ()) l (by omega), Array.getElem_map]
    rw [← hm, gensInv]
    rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
    · exact get0_pair _ _
    · exact get1_pair _ _

theorem hg : gens.size = 2 ∧ gensInv.size = 2 ∧
    ∀ l < 2, gens[l]! = unpack 315 9 (PJ2C.G l) ∧ gensInv[l]! = unpack 315 9 (PJ2C.GI l) :=
  ⟨rfl, rfl, gens_eq⟩

theorem rep0_eq : wA = RP0.map (unpack 315 9) := PJ2.wA_eq

theorem rep1_eq : (List.replicate 6 (patW wA wB commPat)).flatten = RP1.map (unpack 315 9) := by
  rw [PJ2.wA_eq, PJ2.wB_eq]
  rfl

theorem canon0 : canonL 315 9 RP0 = true := by quickRfl
theorem canon1 : canonL 315 9 RP1 = true := by quickRfl
theorem ltbs : ltL 315 bs = true := by quickRfl
theorem st0 : startNF 315 9 PJ2.LR PJ2.TRI 3 bs RP0 (rowGet PJ2C.XT0 76 0) = true := by quickRfl
theorem st1 : startNF 315 9 PJ2.LR PJ2.TRI 3 bs RP1 (rowGet PJ2C.XT1 76 0) = true := by quickRfl
theorem k0 : Nat.beq (nfKey 315 9 PJ2.LR PJ2.TR 3 bs (nfX 3 (rowGet PJ2C.XT0 76 0)))
    (wordKey 315 9 bs RP0) = true := by quickRfl
theorem k1 : Nat.beq (nfKey 315 9 PJ2.LR PJ2.TR 3 bs (nfX 3 (rowGet PJ2C.XT1 76 0)))
    (wordKey 315 9 bs RP1) = true := by quickRfl
theorem c00 : Nat.beq (PJ2C.C0 0) 1 = true := by quickRfl
theorem c10 : Nat.beq (PJ2C.C1 0) 1 = true := by quickRfl
theorem c0N : Nat.beq (PJ2C.C0 (Nat.mul PJ2C.nS0 16)) PJ2C.c0 = true := by quickRfl
theorem c1N : Nat.beq (PJ2C.C1 (Nat.mul PJ2C.nS1 16)) PJ2C.c1 = true := by quickRfl

theorem ok0 : ClosNFOK 315 9 7 3 PJ2.BP PJ2.S PJ2.SI PJ2.LR PJ2.TR PJ2.TRI bs 2 PJ2C.G PJ2C.GI RP0
    PJ2C.c0 3000 PJ2C.nS0 16 10 PJ2C.nB0 32 (rowGet PJ2C.XT0 76) (rowGet PJ2C.WT0 40) PJ2C.C0 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    fun l hl => allN_spec gperm l hl, canon0, ltbs, st0, k0, PJ2C.hnf0,
    Nat.eq_of_beq_eq_true c00, Nat.eq_of_beq_eq_true c0N, PJ2C.hrun0⟩

theorem ok1 : ClosNFOK 315 9 7 3 PJ2.BP PJ2.S PJ2.SI PJ2.LR PJ2.TR PJ2.TRI bs 2 PJ2C.G PJ2C.GI RP1
    PJ2C.c1 3000 PJ2C.nS1 16 10 PJ2C.nB1 32 (rowGet PJ2C.XT1 76) (rowGet PJ2C.WT1 40) PJ2C.C1 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    fun l hl => allN_spec gperm l hl, canon1, ltbs, st1, k1, PJ2C.hnf1,
    Nat.eq_of_beq_eq_true c10, Nat.eq_of_beq_eq_true c1N, PJ2C.hrun1⟩

theorem o0 : ordWK 315 9 bs RP0 2 = true := by quickRfl
theorem o1 : ordWK 315 9 bs RP1 2 = true := by quickRfl

theorem canonNil : canonL 315 9 RPnil = true := by quickRfl

theorem hsz : rcnt (PJ2.LR 1) * rcnt (PJ2.LR 2) < 2 ^ 20 := by
  have h1 : Nat.beq (rcnt (PJ2.LR 1)) 160 = true := by quickRfl
  have h2 : Nat.beq (rcnt (PJ2.LR 2)) 12 = true := by quickRfl
  rw [Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2]
  decide

theorem s2 : Nat.beq (sumN 315 (fun k => Nat.mod (PJ2K2.CS k) 1048576)) 2835 = true := by quickRfl
theorem s3 : Nat.beq (sumN 315 (fun k => Nat.mod (PJ2K30.CS k) 1048576)) 17360 = true := by quickRfl
theorem sTot : Nat.beq (Nat.add (Nat.mul PJ2C.c0 (sumN 315 (fun k => Nat.div (PJ2K30.CS k) 1048576)))
    (Nat.mul PJ2C.c1 (sumN 315 (fun k => Nat.div (PJ2K31.CS k) 1048576)))) 1209600 = true := by quickRfl
theorem sSz : Nat.beq (Nat.add PJ2C.c0 PJ2C.c1) 2835 = true := by quickRfl

theorem cl_eq : cl = [(wA, closureOf wA),
    ((List.replicate 6 (patW wA wB commPat)).flatten,
      closureOf (List.replicate 6 (patW wA wB commPat)).flatten)] := rfl

set_option maxHeartbeats 2000000 in
theorem facts : (rawChainOK 315 ((j2StrongArrs ()).extract 0 2) (j2StrongArrs ()) baseArr (j2Words ()) 1 =
        true ∧ rawOrbitSizes 315 (j2StrongArrs ()) baseArr = [315, 160, 12])
    ∧ (ordB bs wA 2 = true ∧ ordB bs wB 3 = true ∧ ordB bs (patW wA wB [false, true]) 7 = true ∧
      ordB bs (patW wA wB commPat) 12 = true)
    ∧ (countW (fun w => ordB bs w 2) blocks [] = 2835 ∧
      countW (fun w => ordB bs w 3) blocks [] = 17360)
    ∧ ((∀ c ∈ cl, ordB bs c.1 2 = true) ∧
      (∀ c ∈ cl, closureOK levels bs gens gensInv c.1 c.2.1 c.2.2.1 c.2.2.2 = true) ∧
      keysDistinctNF 315 levels bs (cl.map fun c => c.2.1) = true ∧
      (cl.map fun c => c.2.1.size).sum = 2835)
    ∧ ((cl.map fun c => c.2.1.size *
      countW (fun y => ordB bs y 3 && condsOK bs c.1 y conds) blocks []).sum = 1209600) := by
  have srt := keysK_sound
    (cs := [(PJ2C.c0, nfKeyX 315 9 PJ2.LR PJ2.TR 3 bs PJ2C.XT0 76),
      (PJ2C.c1, nfKeyX 315 9 PJ2.LR PJ2.TR 3 bs PJ2C.XT1 76)]) (by decide) (by decide) PJ2C.hsrt
  have hD := nodup_of_strictInc_mergeSort srt
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at hD
  have cl0 := closNF_sound (bs := bs) (rep := wA) PJ2.binds PJ2.perm PJ2.hl rfl hg rep0_eq ok0
    (List.nodup_append.1 hD).1
  have cl1 := closNF_sound (bs := bs) (rep := (List.replicate 6 (patW wA wB commPat)).flatten)
    PJ2.binds PJ2.perm PJ2.hl rfl hg rep1_eq ok1 (List.nodup_append.1 hD).2.1
  have n2 := cnt3_sound (bs := bs) (XP := RPnil) (conds := PairNil.noConds) PJ2.binds PJ2.perm PJ2.hl rfl
    canonNil hsz PJ2K2.hk
  have n30 := cnt3_sound (bs := bs) PJ2.binds PJ2.perm PJ2.hl rfl canon0 hsz PJ2K30.hk
  have n31 := cnt3_sound (bs := bs) PJ2.binds PJ2.perm PJ2.hl rfl canon1 hsz PJ2K31.hk
  refine ⟨⟨PJ2.chain, PJ2.orbits⟩, PJ2.ords, ⟨?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [PairJ2.blocks, PairJ2.groups, PairJ2.levels, n2.1]
    exact Nat.eq_of_beq_eq_true s2
  · rw [PairJ2.blocks, PairJ2.groups, PairJ2.levels, n30.1]
    exact Nat.eq_of_beq_eq_true s3
  · intro c hc
    rw [cl_eq] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · rw [rep0_eq]
      exact ordWK_sound o0
    · rw [rep1_eq]
      exact ordWK_sound o1
  · intro c hc
    rw [cl_eq] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact cl0.1
    · exact cl1.1
  · rw [cl_eq]
    unfold keysDistinctNF
    simp only [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [closureOf, closureOf, PairJ2.levels, cl0.2.2, cl1.2.2]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at srt
    exact srt
  · rw [cl_eq]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    rw [closureOf, closureOf, PairJ2.levels, cl0.2.1, cl1.2.1]
    exact Nat.eq_of_beq_eq_true sSz
  · rw [cl_eq]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    rw [closureOf, closureOf, PairJ2.levels, cl0.2.1, cl1.2.1, PairJ2.blocks, PairJ2.groups, rep1_eq, rep0_eq, PairJ2.levels,
      n30.2, n31.2]
    exact Nat.eq_of_beq_eq_true sTot

end CertificateChecks.KernelSporSch.PJ2Check

end
