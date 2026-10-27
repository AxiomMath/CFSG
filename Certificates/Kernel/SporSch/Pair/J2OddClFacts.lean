module

public import Certificates.Kernel.SporSch.Pair.J2OddCl
public import Certificates.Data.SmithB45J2ClsData
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.PrimSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.PJ2C260410G

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative CFSG.Sporadic.Schreier.PairJ2
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Quasithin.J2Cls
open CertificateChecks.KernelSporSch

theorem gbind : allN 2 (fun l => bAnd(Nat.beq (PJ2C260410.G l) (PJ2.S l),
    Nat.beq (PJ2C260410.GI l) (PJ2.SI l))) = true := by quickRfl

theorem gperm :
    allN 2 (fun l => permOK 315 9 (mask 9) (315 * 9) (PJ2C260410.G l) (PJ2C260410.GI l)) = true := by
  quickRfl

theorem gens_eq (l : Nat) (hl : l < 2) :
    gens[l]! = unpack 315 9 (PJ2C260410.G l) ∧ gensInv[l]! = unpack 315 9 (PJ2C260410.GI l) := by
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 (allN_spec gbind l hl)
  rw [Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2]
  have hS := PJ2.arr_eq l (by omega)
  have hI := (invEqK_sound (allN_spec PJ2.perm l (by omega))).1
  have hsz : (j2StrongArrs ()).size = 7 := by simp [j2StrongArrs]
  refine ⟨?_, ?_⟩
  · rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
    · exact hS
    · exact hS
  · rw [← hI, ← hS]
    have hm : (rawInvs 315 (j2StrongArrs ()))[l]! = invCand 315 (j2StrongArrs ())[l]! := by
      rw [rawInvs, getElem!_pos ((j2StrongArrs ()).map (invCand 315)) l (by simp [hsz]; omega),
        getElem!_pos (j2StrongArrs ()) l (by omega), Array.getElem_map]
    rw [← hm]
    rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
    · rfl
    · rfl

theorem hg : gens.size = 2 ∧ gensInv.size = 2 ∧
    ∀ l < 2, gens[l]! = unpack 315 9 (PJ2C260410.G l) ∧ gensInv[l]! = unpack 315 9 (PJ2C260410.GI l) :=
  ⟨rfl, rfl, gens_eq⟩

@[expose] noncomputable def pRP (p : List Bool) : List Nat :=
  p.reverse.map fun b => bif b then PJ2.S 1 else PJ2.S 0

@[expose] noncomputable def RP3A : List Nat := (List.replicate 5 (pRP p15A)).flatten

@[expose] noncomputable def RP3B : List Nat := [PJ2.S 1]

@[expose] noncomputable def RP5A : List Nat := (List.replicate 3 (pRP p15A)).flatten

@[expose] noncomputable def RP5C : List Nat := pRP p5C

theorem patW_eq (p : List Bool) : patW wA wB p = (pRP p).map (unpack 315 9) := by
  rw [PJ2.wA_eq, PJ2.wB_eq, patW, pRP, List.map_map]
  generalize p.reverse = l
  induction l with
  | nil => rfl
  | cons c l ih => cases c <;> simp [ih]

theorem rep3A : w3A = RP3A.map (unpack 315 9) := by
  rw [w3A, w15A, RP3A, patW_eq, List.map_flatten, List.map_replicate]

theorem rep3B : wB = RP3B.map (unpack 315 9) := PJ2.wB_eq

theorem rep5A : w5A = RP5A.map (unpack 315 9) := by
  rw [w5A, w15A, RP5A, patW_eq, List.map_flatten, List.map_replicate]

theorem rep5C : w5C = RP5C.map (unpack 315 9) := by
  rw [w5C, RP5C, patW_eq]

theorem ltbs : ltL 315 bs = true := by quickRfl

theorem ok0 : ClosNFOK 315 9 7 3 PJ2.BP PJ2.S PJ2.SI PJ2.LR PJ2.TR PJ2.TRI bs 2 PJ2C260410.G
    PJ2C260410.GI RP3A PJ2C260410.c0 100000 PJ2C260410.nS0 16 10 PJ2C260410.nB0 32
    (rowGet PJ2C260410.XT0 76) (rowGet PJ2C260410.WT0 40) PJ2C260410.C0 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    fun l hl => allN_spec gperm l hl, by quickRfl, ltbs, by quickRfl, by quickRfl, PJ2C260410.hnf0,
    Nat.eq_of_beq_eq_true (by quickRfl), Nat.eq_of_beq_eq_true (by quickRfl), PJ2C260410.hrun0⟩

theorem ok1 : ClosNFOK 315 9 7 3 PJ2.BP PJ2.S PJ2.SI PJ2.LR PJ2.TR PJ2.TRI bs 2 PJ2C260410.G
    PJ2C260410.GI RP3B PJ2C260410.c1 100000 PJ2C260410.nS1 16 10 PJ2C260410.nB1 32
    (rowGet PJ2C260410.XT1 76) (rowGet PJ2C260410.WT1 40) PJ2C260410.C1 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    fun l hl => allN_spec gperm l hl, by quickRfl, ltbs, by quickRfl, by quickRfl, PJ2C260410.hnf1,
    Nat.eq_of_beq_eq_true (by quickRfl), Nat.eq_of_beq_eq_true (by quickRfl), PJ2C260410.hrun1⟩

theorem ok2 : ClosNFOK 315 9 7 3 PJ2.BP PJ2.S PJ2.SI PJ2.LR PJ2.TR PJ2.TRI bs 2 PJ2C260410.G
    PJ2C260410.GI RP5A PJ2C260410.c2 100000 PJ2C260410.nS2 16 10 PJ2C260410.nB2 32
    (rowGet PJ2C260410.XT2 76) (rowGet PJ2C260410.WT2 40) PJ2C260410.C2 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    fun l hl => allN_spec gperm l hl, by quickRfl, ltbs, by quickRfl, by quickRfl, PJ2C260410.hnf2,
    Nat.eq_of_beq_eq_true (by quickRfl), Nat.eq_of_beq_eq_true (by quickRfl), PJ2C260410.hrun2⟩

theorem ok3 : ClosNFOK 315 9 7 3 PJ2.BP PJ2.S PJ2.SI PJ2.LR PJ2.TR PJ2.TRI bs 2 PJ2C260410.G
    PJ2C260410.GI RP5C PJ2C260410.c3 100000 PJ2C260410.nS3 16 10 PJ2C260410.nB3 32
    (rowGet PJ2C260410.XT3 76) (rowGet PJ2C260410.WT3 40) PJ2C260410.C3 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    fun l hl => allN_spec gperm l hl, by quickRfl, ltbs, by quickRfl, by quickRfl, PJ2C260410.hnf3,
    Nat.eq_of_beq_eq_true (by quickRfl), Nat.eq_of_beq_eq_true (by quickRfl), PJ2C260410.hrun3⟩

@[expose] def clKey (nf : Array Nat) : Nat := imgKey 315 (baseImgs bs (nfWord PairJ2.levels nf))

@[expose] def ClFact (w : List (Array Nat)) (c : Nat) : Prop :=
  closureOK PairJ2.levels bs gens gensInv w (CFSG.Quasithin.J2Cls.closureOf w).1
      (CFSG.Quasithin.J2Cls.closureOf w).2.1 (CFSG.Quasithin.J2Cls.closureOf w).2.2 = true ∧
    (CFSG.Quasithin.J2Cls.closureOf w).1.size = c ∧ ((CFSG.Quasithin.J2Cls.closureOf w).1.toList.map clKey).Nodup

theorem keys_nodup :
    ((List.range PJ2C260410.c0).map (nfKeyX 315 9 PJ2.LR PJ2.TR 3 bs PJ2C260410.XT0 76)).Nodup ∧
    ((List.range PJ2C260410.c1).map (nfKeyX 315 9 PJ2.LR PJ2.TR 3 bs PJ2C260410.XT1 76)).Nodup ∧
    ((List.range PJ2C260410.c2).map (nfKeyX 315 9 PJ2.LR PJ2.TR 3 bs PJ2C260410.XT2 76)).Nodup ∧
    ((List.range PJ2C260410.c3).map (nfKeyX 315 9 PJ2.LR PJ2.TR 3 bs PJ2C260410.XT3 76)).Nodup := by
  have srt := keysK_sound
    (cs := [(PJ2C260410.c0, nfKeyX 315 9 PJ2.LR PJ2.TR 3 bs PJ2C260410.XT0 76),
      (PJ2C260410.c1, nfKeyX 315 9 PJ2.LR PJ2.TR 3 bs PJ2C260410.XT1 76),
      (PJ2C260410.c2, nfKeyX 315 9 PJ2.LR PJ2.TR 3 bs PJ2C260410.XT2 76),
      (PJ2C260410.c3, nfKeyX 315 9 PJ2.LR PJ2.TR 3 bs PJ2C260410.XT3 76)])
    (by decide) (by decide) PJ2C260410.hsrt
  have hD := nodup_of_strictInc_mergeSort srt
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at hD
  obtain ⟨h0, h123, -⟩ := List.nodup_append.1 hD
  obtain ⟨h1, h23, -⟩ := List.nodup_append.1 h123
  obtain ⟨h2, h3, -⟩ := List.nodup_append.1 h23
  exact ⟨h0, h1, h2, h3⟩

theorem clFact_of {w : List (Array Nat)} {RP : List Nat} {c c' nS nB : Nat}
    {X W C : Nat → Nat} (hrep : w = RP.map (unpack 315 9))
    (h : ClosNFOK 315 9 7 3 PJ2.BP PJ2.S PJ2.SI PJ2.LR PJ2.TR PJ2.TRI bs 2 PJ2C260410.G
      PJ2C260410.GI RP c 100000 nS 16 10 nB 32 X W C)
    (hD : ((List.range c).map fun i => nfKey 315 9 PJ2.LR PJ2.TR 3 bs (nfX 3 (X i))).Nodup)
    (hc : c = c') : ClFact w c' := by
  have cl := closNF_sound (bs := bs) (rep := w) PJ2.binds PJ2.perm PJ2.hl rfl hg hrep h hD
  subst hc
  refine ⟨?_, ?_, ?_⟩
  · rw [CFSG.Quasithin.J2Cls.closureOf, PairJ2.levels]
    exact cl.1
  · rw [CFSG.Quasithin.J2Cls.closureOf, PairJ2.levels]
    exact cl.2.1
  · have e : (CFSG.Quasithin.J2Cls.closureOf w).1.toList.map clKey =
        (List.range c).map fun i => nfKey 315 9 PJ2.LR PJ2.TR 3 bs (nfX 3 (X i)) := by
      rw [CFSG.Quasithin.J2Cls.closureOf, PairJ2.levels]
      exact cl.2.2
    rw [e]
    exact hD

theorem clFacts : ClFact w3A 560 ∧ ClFact wB 16800 ∧ ClFact w5A 2016 ∧ ClFact w5C 12096 := by
  obtain ⟨h0, h1, h2, h3⟩ := keys_nodup
  exact ⟨clFact_of rep3A ok0 h0 rfl, clFact_of rep3B ok1 h1 rfl, clFact_of rep5A ok2 h2 rfl,
    clFact_of rep5C ok3 h3 rfl⟩

end CertificateChecks.KernelSporSch.PJ2C260410G

end
