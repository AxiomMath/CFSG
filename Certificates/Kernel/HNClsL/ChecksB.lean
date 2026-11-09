module

public import Certificates.Kernel.HNClsL.Snaps
public import Certificates.Data.Kernel.HNClsLRun
public import CFSG.Certificates.Kernel.Common.Each
public import CFSG.Certificates.Kernel.Common.ForallTree
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option profiler true

namespace CFSG.KD.HNClsL.ClsB

open CFSG.KD.HNClsL CFSG.KC.HNClsL CFSG.KC.SlpPc CFSG.KC.Ord

@[expose] noncomputable def FS (j i : Nat) : Nat :=
  nthD CFSG.KD.OrdHN.ONE (nthD List.nil SB.FPL j) i

@[expose] noncomputable def GS (j i : Nat) : Nat :=
  nthD CFSG.KD.OrdHN.ONE (nthD List.nil SB.GPL j) i

@[expose] noncomputable def LM (c : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (nthD CFSG.KD.OrdHN.ONE SB.RV (Nat.sub c 37)) (lt c)
    (Nat.blt c 37)

@[expose] noncomputable def EM (c : Nat) : List Nat :=
  Bool.rec (motive := fun _ => List Nat) (nthD List.nil SB.RXL (Nat.sub c 37)) [c] (Nat.blt c 37)

@[expose] noncomputable def rC (k : Nat) : Bool :=
  slpR CFSG.KC.LL.HN.mm LM EM SB.RA SB.RB k

@[expose] noncomputable def mE (j : Nat) : Bool :=
  andB (allL (fun c => gdL c 419) (nthD List.nil SB.MWL j))
    ((nthD List.nil SB.MWL j).flatMap EM == nthD List.nil poolB j)

@[expose] noncomputable def fC (j i : Nat) : Bool :=
  Nat.beq (wordGo CFSG.KC.LL.HN.mm LM (((nthD List.nil SB.MWL j).drop (32 * i)).take 32) (FS j i))
    (FS j (i + 1))

@[expose] noncomputable def gC (j i : Nat) : Bool :=
  Nat.beq (wordGo CFSG.KC.LL.HN.mm LM (((nthD List.nil SB.IWL j).drop (32 * i)).take 32)
    (GS j i)) (GS j (i + 1))

@[expose] noncomputable def iE (j : Nat) : Bool :=
  andB (allL (fun c => gdL c 419) (nthD List.nil SB.IWL j))
    ((nthD List.nil SB.IWL j).flatMap EM == invWA (nthD List.nil poolB j) List.nil)

@[expose] noncomputable def fE (j : Nat) : Bool :=
  andB (Nat.ble (nthD List.nil SB.MWL j).length (32 * ((nthD List.nil SB.FPL j).length - 1)))
    (andB (Nat.beq (FS j 0) CFSG.KD.OrdHN.ONE)
      (Nat.beq (FS j ((nthD List.nil SB.FPL j).length - 1)) (nthD CFSG.KD.OrdHN.ONE SB.PM j)))

@[expose] noncomputable def gE (j : Nat) : Bool :=
  andB (Nat.ble (nthD List.nil SB.IWL j).length
      (32 * ((nthD List.nil SB.GPL j).length - 1)))
    (andB (Nat.beq (GS j 0) CFSG.KD.OrdHN.ONE)
      (Nat.beq (GS j ((nthD List.nil SB.GPL j).length - 1)) (nthD CFSG.KD.OrdHN.ONE SB.GL j)))

@[expose] noncomputable def fwA : Nat → Bool := fC 0
@[expose] noncomputable def fwB : Nat → Bool := fC 1
@[expose] noncomputable def fwC : Nat → Bool := fC 2
@[expose] noncomputable def fwD : Nat → Bool := fC 3
@[expose] noncomputable def fwE : Nat → Bool := fC 4
@[expose] noncomputable def fwF : Nat → Bool := fC 5
@[expose] noncomputable def fwG : Nat → Bool := fC 6
@[expose] noncomputable def fwH : Nat → Bool := fC 7
@[expose] noncomputable def fwI : Nat → Bool := fC 8
@[expose] noncomputable def gwD : Nat → Bool := gC 3
@[expose] noncomputable def gwE : Nat → Bool := gC 4
@[expose] noncomputable def gwF : Nat → Bool := gC 5
@[expose] noncomputable def gwG : Nat → Bool := gC 6
@[expose] noncomputable def gwH : Nat → Bool := gC 7

#kc_each fE 0 9
#kc_each rC 0 419
#kc_each mE 0 9
#kc_each fwA 0 1
#kc_each fwB 0 1
#kc_each fwC 0 1
#kc_each fwD 0 1
#kc_each fwE 0 1
#kc_each fwF 0 1
#kc_each fwG 0 1
#kc_each fwH 0 1
#kc_each fwI 0 2
#kc_each gE 3 8
#kc_each iE 3 8
#kc_each gwD 0 1
#kc_each gwE 0 1
#kc_each gwF 0 1
#kc_each gwG 0 1
#kc_each gwH 0 1

#kc_forall_tree fE_all (fun j => fE j = true) 9 CFSG.KD.HNClsL.ClsB.fE
#kc_forall_tree rC_all (fun k => rC k = true) 419 CFSG.KD.HNClsL.ClsB.rC
#kc_forall_tree mE_all (fun j => mE j = true) 9 CFSG.KD.HNClsL.ClsB.mE
#kc_forall_tree fwA_all (fun i => fwA i = true) 1 CFSG.KD.HNClsL.ClsB.fwA
#kc_forall_tree fwB_all (fun i => fwB i = true) 1 CFSG.KD.HNClsL.ClsB.fwB
#kc_forall_tree fwC_all (fun i => fwC i = true) 1 CFSG.KD.HNClsL.ClsB.fwC
#kc_forall_tree fwD_all (fun i => fwD i = true) 1 CFSG.KD.HNClsL.ClsB.fwD
#kc_forall_tree fwE_all (fun i => fwE i = true) 1 CFSG.KD.HNClsL.ClsB.fwE
#kc_forall_tree fwF_all (fun i => fwF i = true) 1 CFSG.KD.HNClsL.ClsB.fwF
#kc_forall_tree fwG_all (fun i => fwG i = true) 1 CFSG.KD.HNClsL.ClsB.fwG
#kc_forall_tree fwH_all (fun i => fwH i = true) 1 CFSG.KD.HNClsL.ClsB.fwH
#kc_forall_tree fwI_all (fun i => fwI i = true) 2 CFSG.KD.HNClsL.ClsB.fwI
#kc_forall_tree gwD_all (fun i => gwD i = true) 1 CFSG.KD.HNClsL.ClsB.gwD
#kc_forall_tree gwE_all (fun i => gwE i = true) 1 CFSG.KD.HNClsL.ClsB.gwE
#kc_forall_tree gwF_all (fun i => gwF i = true) 1 CFSG.KD.HNClsL.ClsB.gwF
#kc_forall_tree gwG_all (fun i => gwG i = true) 1 CFSG.KD.HNClsL.ClsB.gwG
#kc_forall_tree gwH_all (fun i => gwH i = true) 1 CFSG.KD.HNClsL.ClsB.gwH

theorem fC_all (j : Nat) (hj : j < 9) :
    ∀ i < (nthD List.nil SB.FPL j).length - 1, fC j i = true := by
  match j, hj with
  | 0, _ => exact fwA_all
  | 1, _ => exact fwB_all
  | 2, _ => exact fwC_all
  | 3, _ => exact fwD_all
  | 4, _ => exact fwE_all
  | 5, _ => exact fwF_all
  | 6, _ => exact fwG_all
  | 7, _ => exact fwH_all
  | 8, _ => exact fwI_all

theorem gC_all (j : Nat) (h0 : 3 ≤ j) (hj : j < 8) :
    (∀ i < (nthD List.nil SB.GPL j).length - 1, gC j i = true) ∧ gE j = true ∧ iE j = true := by
  match j, h0, hj with
  | 0, h0, _ | 1, h0, _ | 2, h0, _ => exact absurd h0 (by decide)
  | 3, _, _ => exact ⟨gwD_all, gE3, iE3⟩
  | 4, _, _ => exact ⟨gwE_all, gE4, iE4⟩
  | 5, _, _ => exact ⟨gwF_all, gE5, iE5⟩
  | 6, _, _ => exact ⟨gwG_all, gE6, iE6⟩
  | 7, _, _ => exact ⟨gwH_all, gE7, iE7⟩

theorem poolB_length : poolB.length = 9 := by decide +kernel

theorem fW (j : Nat) (hj : j < 9) :
    wordP CFSG.KC.LL.HN.mm CFSG.KD.OrdHN.ONE LM (nthD List.nil SB.MWL j) =
      nthD CFSG.KD.OrdHN.ONE SB.PM j := by
  obtain ⟨h1, h2⟩ := andB_trueH (fE_all j hj)
  obtain ⟨h2, h3⟩ := andB_trueH h2
  have e := wordGo_of_chunks (P := FS j) (K := 32) (Nat.le_of_ble_eq_true h1) (fC_all j hj)
  rw [Nat.eq_of_beq_eq_true h2] at e
  exact e.trans (Nat.eq_of_beq_eq_true h3)

theorem gW (j : Nat) (h0 : 3 ≤ j) (hj : j < 8) :
    wordP CFSG.KC.LL.HN.mm CFSG.KD.OrdHN.ONE LM (nthD List.nil SB.IWL j) =
      nthD CFSG.KD.OrdHN.ONE SB.GL j := by
  obtain ⟨hc, he, -⟩ := gC_all j h0 hj
  obtain ⟨h1, h2⟩ := andB_trueH he
  obtain ⟨h2, h3⟩ := andB_trueH h2
  have e := wordGo_of_chunks (P := GS j) (K := 32) (Nat.le_of_ble_eq_true h1) hc
  rw [Nat.eq_of_beq_eq_true h2] at e
  exact e.trans (Nat.eq_of_beq_eq_true h3)

theorem pmB_length : SB.PM.length = 9 := by decide +kernel

@[expose, reducible] noncomputable def GWU : Nat → Nat :=
  gRng CFSG.KC.LL.HN.mm CFSG.KD.OrdHN.ONE lt poolB 3 8 SB.GL

theorem gAl : alphOK CFSG.KC.LL.HN.mm CFSG.KD.OrdHN.ONE lt = true := by quickRfl

theorem gOk : allL (allL okC) poolB = true := by quickRfl

@[expose, reducible] noncomputable def FA : Nat → Nat := nthD CFSG.KD.OrdHN.ONE SB.PM

theorem gGn : allL (fun j => andB (evC (nthD List.nil poolB j))
    (Nat.beq (CFSG.KC.LL.HN.mm (FA j) (FA 0)) (CFSG.KC.LL.HN.mm (FA 0) (FA j)))) gensB = true := by
  quickRfl

theorem gT : treeGo CFSG.KC.LL.HN.mm (gensB.map FA) (lenL gensB) trB [CFSG.KD.OrdHN.ONE] 1 0 0
    (fun ks n => andB (ks == SB.KS) (Nat.beq n nQB)) = true := by quickRfl

theorem gN : nodupN SB.KS = true := by quickRfl

theorem gL : linesGo CFSG.KC.LL.HN.mm CFSG.KD.OrdHN.ONE poolB FA linesB
    (fun pks => pks == SB.PKS) = true := by quickRfl

theorem gCv : coverOK CFSG.KD.OrdHN.ONE SB.KS SB.PKS = true := by quickRfl

theorem gWM' : mapS (specM CFSG.KC.LL.HN.mm CFSG.KD.OrdHN.ONE FA) wlB (fun xs => xs == SB.WM) =
    true := by quickRfl

theorem gF : fuseOK CFSG.KC.LL.HN.mm CFSG.KD.OrdHN.ONE poolB FA (lenL wlB) SB.WM (FA 0) fuseB
    SB.PKS = true := by quickRfl

theorem gX : witsOK CFSG.KC.LL.HN.mm CFSG.KD.OrdHN.ONE poolB FA GWU
    (FA 0) witsB wlB SB.WM = true := by quickRfl

theorem gR : restK CFSG.KC.LL.HN.mm CFSG.KD.OrdHN.ONE poolB gensB nQB linesB fuseB wlB witsB trB
    FA GWU = true := by
  have hW := gWM'
  rw [mapS_eqH, beq_iff_eq] at hW
  exact restK_of SB.KS SB.PKS SB.WM gGn gT gN gL gCv hW gF gX

end CFSG.KD.HNClsL.ClsB

end
