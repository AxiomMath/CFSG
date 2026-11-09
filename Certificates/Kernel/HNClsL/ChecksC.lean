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

namespace CFSG.KD.HNClsL.ClsC

open CFSG.KD.HNClsL CFSG.KC.HNClsL CFSG.KC.SlpPc CFSG.KC.Ord

@[expose] noncomputable def FS (j i : Nat) : Nat :=
  nthD CFSG.KD.OrdHN.ONE (nthD List.nil SC.FPL j) i

@[expose] noncomputable def GS (j i : Nat) : Nat :=
  nthD CFSG.KD.OrdHN.ONE (nthD List.nil SC.GPL j) i

@[expose] noncomputable def LM (c : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (nthD CFSG.KD.OrdHN.ONE SC.RV (Nat.sub c 37)) (lt c)
    (Nat.blt c 37)

@[expose] noncomputable def EM (c : Nat) : List Nat :=
  Bool.rec (motive := fun _ => List Nat) (nthD List.nil SC.RXL (Nat.sub c 37)) [c] (Nat.blt c 37)

@[expose] noncomputable def rC (k : Nat) : Bool :=
  slpR CFSG.KC.LL.HN.mm LM EM SC.RA SC.RB k

@[expose] noncomputable def mE (j : Nat) : Bool :=
  andB (allL (fun c => gdL c 131) (nthD List.nil SC.MWL j))
    ((nthD List.nil SC.MWL j).flatMap EM == nthD List.nil poolC j)

@[expose] noncomputable def fC (j i : Nat) : Bool :=
  Nat.beq (wordGo CFSG.KC.LL.HN.mm LM (((nthD List.nil SC.MWL j).drop (32 * i)).take 32) (FS j i))
    (FS j (i + 1))

@[expose] noncomputable def gC (j i : Nat) : Bool :=
  Nat.beq (wordGo CFSG.KC.LL.HN.mm LM (((nthD List.nil SC.IWL j).drop (32 * i)).take 32)
    (GS j i)) (GS j (i + 1))

@[expose] noncomputable def iE (j : Nat) : Bool :=
  andB (allL (fun c => gdL c 131) (nthD List.nil SC.IWL j))
    ((nthD List.nil SC.IWL j).flatMap EM == invWA (nthD List.nil poolC j) List.nil)

@[expose] noncomputable def fE (j : Nat) : Bool :=
  andB (Nat.ble (nthD List.nil SC.MWL j).length (32 * ((nthD List.nil SC.FPL j).length - 1)))
    (andB (Nat.beq (FS j 0) CFSG.KD.OrdHN.ONE)
      (Nat.beq (FS j ((nthD List.nil SC.FPL j).length - 1)) (nthD CFSG.KD.OrdHN.ONE SC.PM j)))

@[expose] noncomputable def gE (j : Nat) : Bool :=
  andB (Nat.ble (nthD List.nil SC.IWL j).length
      (32 * ((nthD List.nil SC.GPL j).length - 1)))
    (andB (Nat.beq (GS j 0) CFSG.KD.OrdHN.ONE)
      (Nat.beq (GS j ((nthD List.nil SC.GPL j).length - 1)) (nthD CFSG.KD.OrdHN.ONE SC.GL j)))

@[expose] noncomputable def fwA : Nat → Bool := fC 0
@[expose] noncomputable def fwB : Nat → Bool := fC 1
@[expose] noncomputable def fwC : Nat → Bool := fC 2
@[expose] noncomputable def fwD : Nat → Bool := fC 3
@[expose] noncomputable def fwE : Nat → Bool := fC 4
@[expose] noncomputable def fwF : Nat → Bool := fC 5
@[expose] noncomputable def fwG : Nat → Bool := fC 6
@[expose] noncomputable def fwH : Nat → Bool := fC 7
@[expose] noncomputable def fwI : Nat → Bool := fC 8
@[expose] noncomputable def fwJ : Nat → Bool := fC 9
@[expose] noncomputable def fwK : Nat → Bool := fC 10
@[expose] noncomputable def fwL : Nat → Bool := fC 11
@[expose] noncomputable def fwM : Nat → Bool := fC 12
@[expose] noncomputable def gwD : Nat → Bool := gC 3
@[expose] noncomputable def gwE : Nat → Bool := gC 4
@[expose] noncomputable def gwF : Nat → Bool := gC 5
@[expose] noncomputable def gwG : Nat → Bool := gC 6
@[expose] noncomputable def gwH : Nat → Bool := gC 7
@[expose] noncomputable def gwI : Nat → Bool := gC 8
@[expose] noncomputable def gwJ : Nat → Bool := gC 9

#kc_each fE 0 13
#kc_each rC 0 131
#kc_each mE 0 13
#kc_each fwA 0 1
#kc_each fwB 0 1
#kc_each fwC 0 1
#kc_each fwD 0 1
#kc_each fwE 0 1
#kc_each fwF 0 1
#kc_each fwG 0 1
#kc_each fwH 0 1
#kc_each fwI 0 1
#kc_each fwJ 0 1
#kc_each fwK 0 1
#kc_each fwL 0 1
#kc_each fwM 0 1
#kc_each gE 3 10
#kc_each iE 3 10
#kc_each gwD 0 1
#kc_each gwE 0 1
#kc_each gwF 0 1
#kc_each gwG 0 1
#kc_each gwH 0 1
#kc_each gwI 0 1
#kc_each gwJ 0 1

#kc_forall_tree fE_all (fun j => fE j = true) 13 CFSG.KD.HNClsL.ClsC.fE
#kc_forall_tree rC_all (fun k => rC k = true) 131 CFSG.KD.HNClsL.ClsC.rC
#kc_forall_tree mE_all (fun j => mE j = true) 13 CFSG.KD.HNClsL.ClsC.mE
#kc_forall_tree fwA_all (fun i => fwA i = true) 1 CFSG.KD.HNClsL.ClsC.fwA
#kc_forall_tree fwB_all (fun i => fwB i = true) 1 CFSG.KD.HNClsL.ClsC.fwB
#kc_forall_tree fwC_all (fun i => fwC i = true) 1 CFSG.KD.HNClsL.ClsC.fwC
#kc_forall_tree fwD_all (fun i => fwD i = true) 1 CFSG.KD.HNClsL.ClsC.fwD
#kc_forall_tree fwE_all (fun i => fwE i = true) 1 CFSG.KD.HNClsL.ClsC.fwE
#kc_forall_tree fwF_all (fun i => fwF i = true) 1 CFSG.KD.HNClsL.ClsC.fwF
#kc_forall_tree fwG_all (fun i => fwG i = true) 1 CFSG.KD.HNClsL.ClsC.fwG
#kc_forall_tree fwH_all (fun i => fwH i = true) 1 CFSG.KD.HNClsL.ClsC.fwH
#kc_forall_tree fwI_all (fun i => fwI i = true) 1 CFSG.KD.HNClsL.ClsC.fwI
#kc_forall_tree fwJ_all (fun i => fwJ i = true) 1 CFSG.KD.HNClsL.ClsC.fwJ
#kc_forall_tree fwK_all (fun i => fwK i = true) 1 CFSG.KD.HNClsL.ClsC.fwK
#kc_forall_tree fwL_all (fun i => fwL i = true) 1 CFSG.KD.HNClsL.ClsC.fwL
#kc_forall_tree fwM_all (fun i => fwM i = true) 1 CFSG.KD.HNClsL.ClsC.fwM
#kc_forall_tree gwD_all (fun i => gwD i = true) 1 CFSG.KD.HNClsL.ClsC.gwD
#kc_forall_tree gwE_all (fun i => gwE i = true) 1 CFSG.KD.HNClsL.ClsC.gwE
#kc_forall_tree gwF_all (fun i => gwF i = true) 1 CFSG.KD.HNClsL.ClsC.gwF
#kc_forall_tree gwG_all (fun i => gwG i = true) 1 CFSG.KD.HNClsL.ClsC.gwG
#kc_forall_tree gwH_all (fun i => gwH i = true) 1 CFSG.KD.HNClsL.ClsC.gwH
#kc_forall_tree gwI_all (fun i => gwI i = true) 1 CFSG.KD.HNClsL.ClsC.gwI
#kc_forall_tree gwJ_all (fun i => gwJ i = true) 1 CFSG.KD.HNClsL.ClsC.gwJ

theorem fC_all (j : Nat) (hj : j < 13) :
    ∀ i < (nthD List.nil SC.FPL j).length - 1, fC j i = true := by
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
  | 9, _ => exact fwJ_all
  | 10, _ => exact fwK_all
  | 11, _ => exact fwL_all
  | 12, _ => exact fwM_all

theorem gC_all (j : Nat) (h0 : 3 ≤ j) (hj : j < 10) :
    (∀ i < (nthD List.nil SC.GPL j).length - 1, gC j i = true) ∧ gE j = true ∧ iE j = true := by
  match j, h0, hj with
  | 0, h0, _ | 1, h0, _ | 2, h0, _ => exact absurd h0 (by decide)
  | 3, _, _ => exact ⟨gwD_all, gE3, iE3⟩
  | 4, _, _ => exact ⟨gwE_all, gE4, iE4⟩
  | 5, _, _ => exact ⟨gwF_all, gE5, iE5⟩
  | 6, _, _ => exact ⟨gwG_all, gE6, iE6⟩
  | 7, _, _ => exact ⟨gwH_all, gE7, iE7⟩
  | 8, _, _ => exact ⟨gwI_all, gE8, iE8⟩
  | 9, _, _ => exact ⟨gwJ_all, gE9, iE9⟩

theorem poolC_length : poolC.length = 13 := by decide +kernel

theorem fW (j : Nat) (hj : j < 13) :
    wordP CFSG.KC.LL.HN.mm CFSG.KD.OrdHN.ONE LM (nthD List.nil SC.MWL j) =
      nthD CFSG.KD.OrdHN.ONE SC.PM j := by
  obtain ⟨h1, h2⟩ := andB_trueH (fE_all j hj)
  obtain ⟨h2, h3⟩ := andB_trueH h2
  have e := wordGo_of_chunks (P := FS j) (K := 32) (Nat.le_of_ble_eq_true h1) (fC_all j hj)
  rw [Nat.eq_of_beq_eq_true h2] at e
  exact e.trans (Nat.eq_of_beq_eq_true h3)

theorem gW (j : Nat) (h0 : 3 ≤ j) (hj : j < 10) :
    wordP CFSG.KC.LL.HN.mm CFSG.KD.OrdHN.ONE LM (nthD List.nil SC.IWL j) =
      nthD CFSG.KD.OrdHN.ONE SC.GL j := by
  obtain ⟨hc, he, -⟩ := gC_all j h0 hj
  obtain ⟨h1, h2⟩ := andB_trueH he
  obtain ⟨h2, h3⟩ := andB_trueH h2
  have e := wordGo_of_chunks (P := GS j) (K := 32) (Nat.le_of_ble_eq_true h1) hc
  rw [Nat.eq_of_beq_eq_true h2] at e
  exact e.trans (Nat.eq_of_beq_eq_true h3)

theorem pmC_length : SC.PM.length = 13 := by decide +kernel

@[expose, reducible] noncomputable def GWU : Nat → Nat :=
  gRng CFSG.KC.LL.HN.mm CFSG.KD.OrdHN.ONE lt poolC 3 10 SC.GL

theorem gAl : alphOK CFSG.KC.LL.HN.mm CFSG.KD.OrdHN.ONE lt = true := by quickRfl

theorem gOk : allL (allL okC) poolC = true := by quickRfl

@[expose, reducible] noncomputable def FA : Nat → Nat := nthD CFSG.KD.OrdHN.ONE SC.PM

theorem gGn : allL (fun j => andB (evC (nthD List.nil poolC j))
    (Nat.beq (CFSG.KC.LL.HN.mm (FA j) (FA 0)) (CFSG.KC.LL.HN.mm (FA 0) (FA j)))) gensC = true := by
  quickRfl

theorem gT : treeGo CFSG.KC.LL.HN.mm (gensC.map FA) (lenL gensC) trC [CFSG.KD.OrdHN.ONE] 1 0 0
    (fun ks n => andB (ks == SC.KS) (Nat.beq n nQC)) = true := by quickRfl

theorem gN : nodupN SC.KS = true := by quickRfl

theorem gL : linesGo CFSG.KC.LL.HN.mm CFSG.KD.OrdHN.ONE poolC FA linesC
    (fun pks => pks == SC.PKS) = true := by quickRfl

theorem gCv : coverOK CFSG.KD.OrdHN.ONE SC.KS SC.PKS = true := by quickRfl

theorem gWM' : mapS (specM CFSG.KC.LL.HN.mm CFSG.KD.OrdHN.ONE FA) wlC (fun xs => xs == SC.WM) =
    true := by quickRfl

theorem gF : fuseOK CFSG.KC.LL.HN.mm CFSG.KD.OrdHN.ONE poolC FA (lenL wlC) SC.WM (FA 0) fuseC
    SC.PKS = true := by quickRfl

theorem gX : witsOK CFSG.KC.LL.HN.mm CFSG.KD.OrdHN.ONE poolC FA GWU
    (FA 0) witsC wlC SC.WM = true := by quickRfl

theorem gR : restK CFSG.KC.LL.HN.mm CFSG.KD.OrdHN.ONE poolC gensC nQC linesC fuseC wlC witsC trC
    FA GWU = true := by
  have hW := gWM'
  rw [mapS_eqH, beq_iff_eq] at hW
  exact restK_of SC.KS SC.PKS SC.WM gGn gT gN gL gCv hW gF gX

end CFSG.KD.HNClsL.ClsC

end
