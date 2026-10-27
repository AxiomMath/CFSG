module

public import Certificates.Kernel.Sporadic.OddCore.J2CnK
public import Certificates.Kernel.Sporadic.OddCore.J2Loc
public import Certificates.Data.Kernel.GH74Ev
public import Certificates.Data.GH74J2CentCheck
public import Certificates.Kernel.Sporadic.ON.Gen
meta import Certificates.Data.GH74J2CentCheck
meta import Certificates.Kernel.Sporadic.OddCore.J2Loc
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelGH74.J2CentE

open CFSG.GH74.Generic.S45.EvSpor CFSG.Sporadic.SmallOddCore.Native CFSG.PSL3Four.Native
open CFSG.Sporadic.SmallOddCore

meta def idM : Array Nat := idTab 315
meta def invM (a : Array Nat) : Array Nat := CFSG.Monster.B.Co2.Native.invCand 315 a
meta def cgM : Array (Array Nat) := j2CG.map natArr
meta def letM (l : Nat) : Array Nat := if l < 4 then cgM[l]! else invM cgM[l - 4]!
meta def evW (w : List Nat) : Array Nat := w.foldl (fun acc l => comp 315 acc (letM l)) idM
meta def cnj (g x : Array Nat) : Array Nat := comp 315 (comp 315 g x) (invM g)
meta def tAM : Array Nat := natArr j2TA

meta def eM : Array (Array Nat) := (j2EWords.map evW).toArray
meta def o1M : Array (Array Nat) := #[tAM] ++ (j2Orb1Conj.map fun w => cnj (evW w) (evW j2Orb1Root)).toArray
meta def o2M : Array (Array Nat) := #[tAM] ++ (j2Orb2Conj.map fun w => cnj (evW w) (evW j2Orb2Root)).toArray
meta def pfM : Array (Array Nat) := (j2PerfPairs.map fun p =>
  comp 315 (comp 315 (evW p.1) (evW p.2)) (comp 315 (invM (evW p.1)) (invM (evW p.2)))).toArray
meta def s1M : Array (Array Nat) := eM ++ #[cgM[0]!, cgM[1]!]
meta def s2M : Array (Array Nat) := s1M.map fun s => cnj cgM[3]! s

meta def idsM (k : Nat) : Array (Array Nat) := Array.replicate k idM
meta def ids4M : Array (Array Nat) := idsM 4
meta def ids11M : Array (Array Nat) := idsM 11
meta def ids21M : Array (Array Nat) := idsM 21
meta def ids3M : Array (Array Nat) := idsM 3
meta def ids6M : Array (Array Nat) := idsM 6

meta def recOf (gs : Array (Array Nat)) : Array (Array Nat) :=
  (bfs (fun j t => conjTab 315 idM gs[j]! t) gs.size idM 3000).tabs
meta def clOf (gs : Array (Array Nat)) : Array (Array Nat) :=
  ((recOf gs).map fun x => (gs ++ gs.map invM).map fun g => comp 315 x g).flatten
meta def eRecM : Array (Array Nat) := recOf eM
meta def o1RecM : Array (Array Nat) := recOf o1M
meta def o2RecM : Array (Array Nat) := recOf o2M
meta def pfRecM : Array (Array Nat) := recOf pfM
meta def s1RecM : Array (Array Nat) := recOf s1M
meta def s2RecM : Array (Array Nat) := recOf s2M
meta def eClM : Array (Array Nat) := clOf eM
meta def o1ClM : Array (Array Nat) := clOf o1M
meta def o2ClM : Array (Array Nat) := clOf o2M
meta def pfClM : Array (Array Nat) := clOf pfM
meta def s1ClM : Array (Array Nat) := clOf s1M
meta def s2ClM : Array (Array Nat) := clOf s2M

meta def eIM : Array (Array Nat) := eM.map invM
meta def o1IM : Array (Array Nat) := o1M.map invM
meta def o2IM : Array (Array Nat) := o2M.map invM
meta def pfIM : Array (Array Nat) := pfM.map invM
meta def s1IM : Array (Array Nat) := s1M.map invM
meta def s2IM : Array (Array Nat) := s2M.map invM

meta def o1CM : Array (Array Nat) := (j2Orb1Conj.map fun w => invM (evW w)).toArray
meta def o2CM : Array (Array Nat) := (j2Orb2Conj.map fun w => invM (evW w)).toArray
meta def pfWM : Array (Array Nat) :=
  (j2PerfPairs.map fun p => #[invM (evW p.1), invM (evW p.2)]).toArray.flatten

meta def eAllIM : Array (Array Nat) := eRecM.map invM

meta def ePM : Array (Array Nat) :=
  #[tAM] ++ ((List.range 4).toArray.map fun i => eM.map fun e => cnj cgM[i]! e).flatten

meta def isInv (x : Array Nat) : Bool := comp 315 x x == idM && x != idM

meta def nciM : List Nat := (List.range eRecM.size).filter fun i => isInv eRecM[i]! && eRecM[i]! != tAM

meta def cmM : List Nat := (List.range 10).flatMap fun a => (List.range 10).map fun b =>
  if comp 315 eRecM[nciM[a]!]! eRecM[nciM[b]!]! == comp 315 eRecM[nciM[b]!]! eRecM[nciM[a]!]!
  then 1 else 0

meta def gpM : List Nat := (List.range 4).flatMap fun a => (List.range 4).map fun b =>
  if comp 315 eM[a]! eM[b]! == comp 315 eM[b]! eM[a]! then 1 else 0

end CertificateChecks.KernelGH74.J2CentE

open CertificateChecks.KernelGH74.J2CentE in
#kmulh CertificateChecks.KernelGH74.J2E 315 9 ids4M eM idM 3000
open CertificateChecks.KernelGH74.J2CentE in
#kmulh CertificateChecks.KernelGH74.J2O1 315 9 ids11M o1M idM 3000
open CertificateChecks.KernelGH74.J2CentE in
#kmulh CertificateChecks.KernelGH74.J2O2 315 9 ids21M o2M idM 3000
open CertificateChecks.KernelGH74.J2CentE in
#kmulh CertificateChecks.KernelGH74.J2PF 315 9 ids3M pfM idM 3000
open CertificateChecks.KernelGH74.J2CentE in
#kmulh CertificateChecks.KernelGH74.J2S1 315 9 ids6M s1M idM 3000
open CertificateChecks.KernelGH74.J2CentE in
#kmulh CertificateChecks.KernelGH74.J2S2 315 9 ids6M s2M idM 3000
open CertificateChecks.KernelGH74.J2CentE in
#kfind CertificateChecks.KernelGH74.J2ECl eRecM eClM
open CertificateChecks.KernelGH74.J2CentE in
#kfind CertificateChecks.KernelGH74.J2O1Cl o1RecM o1ClM
open CertificateChecks.KernelGH74.J2CentE in
#kfind CertificateChecks.KernelGH74.J2O2Cl o2RecM o2ClM
open CertificateChecks.KernelGH74.J2CentE in
#kfind CertificateChecks.KernelGH74.J2PFCl pfRecM pfClM
open CertificateChecks.KernelGH74.J2CentE in
#kfind CertificateChecks.KernelGH74.J2S1Cl s1RecM s1ClM
open CertificateChecks.KernelGH74.J2CentE in
#kfind CertificateChecks.KernelGH74.J2S2Cl s2RecM s2ClM
open CertificateChecks.KernelGH74.J2CentE in
#kmisc_packarrs CertificateChecks.KernelGH74.J2EI eIM 9
open CertificateChecks.KernelGH74.J2CentE in
#kmisc_packarrs CertificateChecks.KernelGH74.J2O1I o1IM 9
open CertificateChecks.KernelGH74.J2CentE in
#kmisc_packarrs CertificateChecks.KernelGH74.J2O2I o2IM 9
open CertificateChecks.KernelGH74.J2CentE in
#kmisc_packarrs CertificateChecks.KernelGH74.J2PFI pfIM 9
open CertificateChecks.KernelGH74.J2CentE in
#kmisc_packarrs CertificateChecks.KernelGH74.J2S1I s1IM 9
open CertificateChecks.KernelGH74.J2CentE in
#kmisc_packarrs CertificateChecks.KernelGH74.J2S2I s2IM 9
open CertificateChecks.KernelGH74.J2CentE in
#kmisc_packarrs CertificateChecks.KernelGH74.J2O1C o1CM 9
open CertificateChecks.KernelGH74.J2CentE in
#kmisc_packarrs CertificateChecks.KernelGH74.J2O2C o2CM 9
open CertificateChecks.KernelGH74.J2CentE in
#kmisc_packarrs CertificateChecks.KernelGH74.J2PFW pfWM 9
open CertificateChecks.KernelGH74.J2CentE in
#kmisc_packarrs CertificateChecks.KernelGH74.J2EAI eAllIM 9
open CertificateChecks.KernelGH74.J2CentE in
#kfind CertificateChecks.KernelGH74.J2EP eRecM ePM
open CertificateChecks.KernelGH74.J2CentE in
#knatlist CertificateChecks.KernelGH74.J2NCI nciM
open CertificateChecks.KernelGH74.J2CentE in
#knatlist CertificateChecks.KernelGH74.J2CM cmM
open CertificateChecks.KernelGH74.J2CentE in
#knatlist CertificateChecks.KernelGH74.J2GP gpM

namespace CertificateChecks.KernelGH74.J2CentE

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KS.GH74
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.J2Cn CFSG.GH74.Generic.S45.EvSpor

@[expose] noncomputable def cK (p : Nat) : Bool := canonK 315 9 (mask 9) (315 * 9) p

@[expose] noncomputable def iK (p q : Nat) : Bool := invEqK 315 9 (mask 9) (315 * 9) p q

@[expose] noncomputable def lt (l : Nat) : Nat := nIf(Nat.blt l 4, F (Nat.add 32 l), I (Nat.add 28 l))

@[expose] noncomputable def wK (w : List Nat) : Nat := wfoldK 315 9 (mask 9) lt w idK

@[expose] noncomputable def tK : Nat := F 31

@[expose] noncomputable def memK (cnt : Nat) (T : Nat → Nat) (x : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) false (fun i ih => bIf(Nat.beq (T i) x, true, ih)) cnt

@[expose] noncomputable def memL (L : List Nat) (x : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun y _ ih => bIf(Nat.beq y x, true, ih)) L

@[expose] noncomputable def cmK (x y xi yi : Nat) : Nat := pc (pc x y) (pc xi yi)

@[expose] noncomputable def cjK (c ci x : Nat) : Nat := pc (pc c x) ci

theorem gens_ok : bAnd(allN 4 (fun j => bAnd(Nat.beq (J2E.GI j) (wK (j2EWords.getD j [])),
      bAnd(Nat.beq (J2E.G j) idK, bAnd(cK (J2EI j), iK (J2E.GI j) (J2EI j))))),
    bAnd(bAnd(Nat.beq (J2O1.GI 0) tK, Nat.beq (J2O2.GI 0) tK),
    bAnd(allN 10 (fun k => bAnd(cK (J2O1C k), bAnd(iK (wK (j2Orb1Conj.getD k [])) (J2O1C k),
      Nat.beq (J2O1.GI (Nat.succ k)) (cjK (wK (j2Orb1Conj.getD k [])) (J2O1C k) (wK j2Orb1Root))))),
    bAnd(allN 20 (fun k => bAnd(cK (J2O2C k), bAnd(iK (wK (j2Orb2Conj.getD k [])) (J2O2C k),
      Nat.beq (J2O2.GI (Nat.succ k)) (cjK (wK (j2Orb2Conj.getD k [])) (J2O2C k) (wK j2Orb2Root))))),
    bAnd(allN 11 (fun j => bAnd(Nat.beq (J2O1.G j) idK, bAnd(cK (J2O1I j), iK (J2O1.GI j) (J2O1I j)))),
    bAnd(allN 21 (fun j => bAnd(Nat.beq (J2O2.G j) idK, bAnd(cK (J2O2I j), iK (J2O2.GI j) (J2O2I j)))),
    bAnd(allN 3 (fun k => bAnd(cK (J2PFW (Nat.mul 2 k)), bAnd(cK (J2PFW (Nat.succ (Nat.mul 2 k))),
      bAnd(iK (wK (j2PerfPairs.getD k ([], [])).1) (J2PFW (Nat.mul 2 k)),
      bAnd(iK (wK (j2PerfPairs.getD k ([], [])).2) (J2PFW (Nat.succ (Nat.mul 2 k))),
      Nat.beq (J2PF.GI k) (cmK (wK (j2PerfPairs.getD k ([], [])).1) (wK (j2PerfPairs.getD k ([], [])).2)
        (J2PFW (Nat.mul 2 k)) (J2PFW (Nat.succ (Nat.mul 2 k))))))))),
    bAnd(allN 3 (fun j => bAnd(Nat.beq (J2PF.G j) idK, bAnd(cK (J2PFI j), iK (J2PF.GI j) (J2PFI j)))),
    bAnd(allN 6 (fun j => bAnd(Nat.beq (J2S1.GI j) (nIf(Nat.blt j 4, J2E.GI j, F (Nat.add 28 j))),
      bAnd(Nat.beq (J2S1.G j) idK, bAnd(cK (J2S1I j), iK (J2S1.GI j) (J2S1I j))))),
    allN 6 (fun j => bAnd(Nat.beq (J2S2.GI j) (cjK (F 35) (I 35) (J2S1.GI j)),
      bAnd(Nat.beq (J2S2.G j) idK, bAnd(cK (J2S2I j), iK (J2S2.GI j) (J2S2I j)))))))))))))) = true := by
  quickRfl

theorem sizes_ok : bAnd(Nat.beq J2E.cnt 32, bAnd(Nat.beq J2O1.cnt 32, bAnd(Nat.beq J2O2.cnt 32,
    bAnd(Nat.beq J2PF.cnt 1920, bAnd(Nat.beq J2S1.cnt 128, bAnd(Nat.beq J2S2.cnt 128,
    bAnd(penumHdK idK J2E.cnt 3000 J2E.T J2E.PL, bAnd(penumHdK idK J2O1.cnt 3000 J2O1.T J2O1.PL,
    bAnd(penumHdK idK J2O2.cnt 3000 J2O2.T J2O2.PL, bAnd(penumHdK idK J2PF.cnt 3000 J2PF.T J2PF.PL,
    bAnd(penumHdK idK J2S1.cnt 3000 J2S1.T J2S1.PL, penumHdK idK J2S2.cnt 3000 J2S2.T J2S2.PL)))))))))))
    = true := by
  quickRfl

@[expose] noncomputable def bOr (a b : Bool) : Bool := bIf(a, true, b)

@[expose] noncomputable def ePQ (c : Nat) : Nat :=
  nIf(Nat.beq c 0, tK, cjK (F (Nat.add 32 (Nat.div (Nat.sub c 1) 4)))
    (I (Nat.add 32 (Nat.div (Nat.sub c 1) 4))) (J2E.GI (Nat.mod (Nat.sub c 1) 4)))

@[expose] noncomputable def getL (L : List Nat) (i : Nat) : Nat := L.getD i 0

@[expose] noncomputable def bN (b : Bool) : Nat := nIf(b, 1, 0)

@[expose] noncomputable def patK (a b c d : Nat) : Bool :=
  bAnd(Nat.beq (getL J2CM (Nat.add (Nat.mul 10 a) b)) (getL J2GP 1),
  bAnd(Nat.beq (getL J2CM (Nat.add (Nat.mul 10 a) c)) (getL J2GP 2),
  bAnd(Nat.beq (getL J2CM (Nat.add (Nat.mul 10 a) d)) (getL J2GP 3),
  bAnd(Nat.beq (getL J2CM (Nat.add (Nat.mul 10 b) c)) (getL J2GP 6),
  bAnd(Nat.beq (getL J2CM (Nat.add (Nat.mul 10 b) d)) (getL J2GP 7),
    Nat.beq (getL J2CM (Nat.add (Nat.mul 10 c) d)) (getL J2GP 11))))))

theorem e_ok : bAnd(allN 4 (fun j => bAnd(involK (J2E.GI j), bIf(Nat.beq (J2E.GI j) tK, false, true))),
    bAnd(allN 17 (fun c => atK J2E.cnt J2E.T J2EP c (ePQ c)),
    allN 32 (fun i => bAnd(cK (J2EAI i), iK (J2E.T i) (J2EAI i))))) = true := by
  quickRfl

theorem struct_ok : allN 32 (fun i => bAnd(bOr (Nat.beq (pc (J2E.T i) (J2E.T i)) idK)
    (Nat.beq (pc (J2E.T i) (J2E.T i)) tK),
    allN 32 (fun j => strictB (cmK (J2E.T i) (J2E.T j) (J2EAI i) (J2EAI j)) (fun c =>
      bOr (Nat.beq c idK) (Nat.beq c tK))))) = true := by
  quickRfl

theorem center_ok : bAnd(allN 32 (fun i => bIf(allN 32 (fun j => pcommK 315 9 (J2E.T i) (J2E.T j)),
      bOr (Nat.beq (J2E.T i) idK) (Nat.beq (J2E.T i) tK), true)),
    bAnd(allN 32 (fun i => pcommK 315 9 tK (J2E.T i)),
      Nat.beq (cntBelowK J2E.cnt (fun i => involK (J2E.T i)) 1) 11)) = true := by
  quickRfl

theorem ecent_ok : allN J2C2.cnt (fun i => bIf(allN 4 (fun j => pcommK 315 9 (J2C2.T i) (J2E.GI j)),
    bOr (Nat.beq (J2C2.T i) idK) (Nat.beq (J2C2.T i) tK), true)) = true := by
  quickRfl

theorem cover_ok : allN 32 (fun i => bOr (Nat.beq (J2E.T i) idK) (bOr (Nat.beq (J2E.T i) tK)
    (bOr (memL ((List.range 10).map fun k => J2O1.GI (Nat.succ k)) (J2E.T i))
      (memL ((List.range 20).map fun k => J2O2.GI (Nat.succ k)) (J2E.T i))))) = true := by
  quickRfl

theorem syl_ok : allN J2S1.cnt (fun i => bIf(memK J2S2.cnt J2S2.T (J2S1.T i),
    memK J2E.cnt J2E.T (J2S1.T i), true)) = true := by
  quickRfl

theorem nc_ok : (List.range 32).filter (fun i => bAnd(involK (J2E.T i),
      bIf(Nat.beq (J2E.T i) tK, false, true))) = J2NCI ∧
    allN 10 (fun a => allN 10 (fun b => Nat.beq (getL J2CM (Nat.add (Nat.mul 10 a) b))
      (bN (commK (J2E.T (getL J2NCI a)) (J2E.T (getL J2NCI b)))))) = true ∧
    allN 4 (fun a => allN 4 (fun b => Nat.beq (getL J2GP (Nat.add (Nat.mul 4 a) b))
      (bN (commK (J2E.GI a) (J2E.GI b))))) = true ∧
    Nat.ble ((quadIdx 10).filter (fun t => patK t.1 t.2.1 t.2.2.1 t.2.2.2)).length 1920 = true := by
  decide +kernel

theorem eE : penumSlK 315 9 (mask 9) (315 * 9) true J2E.G J2E.GI 4 J2E.cnt J2E.T J2E.PL
    J2E.POS J2E.SRT J2E.SRI 0 J2E.cnt = true := by quickRfl
theorem eH : slK J2E.cnt (hsortPtK 315 9 (mask 9) J2E.cnt J2E.T J2E.HS J2E.HSI) 0 J2E.cnt = true := by
  quickRfl
theorem eCl : slK (Nat.mul J2E.cnt 8)
    (findPtK J2E.cnt J2E.T (prodQK 315 9 (mask 9) 8 J2E.T (bothK 4 J2E.GI J2EI)) J2ECl) 0
    (Nat.mul J2E.cnt 8) = true := by quickRfl

theorem o1E : penumSlK 315 9 (mask 9) (315 * 9) true J2O1.G J2O1.GI 11 J2O1.cnt J2O1.T J2O1.PL
    J2O1.POS J2O1.SRT J2O1.SRI 0 J2O1.cnt = true := by quickRfl
theorem o1H : slK J2O1.cnt (hsortPtK 315 9 (mask 9) J2O1.cnt J2O1.T J2O1.HS J2O1.HSI) 0 J2O1.cnt =
    true := by quickRfl
theorem o1Cl : slK (Nat.mul J2O1.cnt 22)
    (findPtK J2O1.cnt J2O1.T (prodQK 315 9 (mask 9) 22 J2O1.T (bothK 11 J2O1.GI J2O1I)) J2O1Cl) 0
    (Nat.mul J2O1.cnt 22) = true := by quickRfl

theorem o2E : penumSlK 315 9 (mask 9) (315 * 9) true J2O2.G J2O2.GI 21 J2O2.cnt J2O2.T J2O2.PL
    J2O2.POS J2O2.SRT J2O2.SRI 0 J2O2.cnt = true := by quickRfl
theorem o2H : slK J2O2.cnt (hsortPtK 315 9 (mask 9) J2O2.cnt J2O2.T J2O2.HS J2O2.HSI) 0 J2O2.cnt =
    true := by quickRfl
theorem o2Cl : slK (Nat.mul J2O2.cnt 42)
    (findPtK J2O2.cnt J2O2.T (prodQK 315 9 (mask 9) 42 J2O2.T (bothK 21 J2O2.GI J2O2I)) J2O2Cl) 0
    (Nat.mul J2O2.cnt 42) = true := by quickRfl

theorem s1E : penumSlK 315 9 (mask 9) (315 * 9) true J2S1.G J2S1.GI 6 J2S1.cnt J2S1.T J2S1.PL
    J2S1.POS J2S1.SRT J2S1.SRI 0 J2S1.cnt = true := by quickRfl
theorem s1H : slK J2S1.cnt (hsortPtK 315 9 (mask 9) J2S1.cnt J2S1.T J2S1.HS J2S1.HSI) 0 J2S1.cnt =
    true := by quickRfl
theorem s1Cl : slK (Nat.mul J2S1.cnt 12)
    (findPtK J2S1.cnt J2S1.T (prodQK 315 9 (mask 9) 12 J2S1.T (bothK 6 J2S1.GI J2S1I)) J2S1Cl) 0
    (Nat.mul J2S1.cnt 12) = true := by quickRfl

theorem s2E : penumSlK 315 9 (mask 9) (315 * 9) true J2S2.G J2S2.GI 6 J2S2.cnt J2S2.T J2S2.PL
    J2S2.POS J2S2.SRT J2S2.SRI 0 J2S2.cnt = true := by quickRfl
theorem s2H : slK J2S2.cnt (hsortPtK 315 9 (mask 9) J2S2.cnt J2S2.T J2S2.HS J2S2.HSI) 0 J2S2.cnt =
    true := by quickRfl
theorem s2Cl : slK (Nat.mul J2S2.cnt 12)
    (findPtK J2S2.cnt J2S2.T (prodQK 315 9 (mask 9) 12 J2S2.T (bothK 6 J2S2.GI J2S2I)) J2S2Cl) 0
    (Nat.mul J2S2.cnt 12) = true := by quickRfl

@[expose] noncomputable def pfE (s : Nat) : Bool :=
  penumSlK 315 9 (mask 9) (315 * 9) true J2PF.G J2PF.GI 3 J2PF.cnt J2PF.T J2PF.PL J2PF.POS J2PF.SRT
    J2PF.SRI (Nat.mul 240 s) 240

@[expose] noncomputable def pfH (s : Nat) : Bool :=
  slK J2PF.cnt (hsortPtK 315 9 (mask 9) J2PF.cnt J2PF.T J2PF.HS J2PF.HSI) (Nat.mul 240 s) 240

@[expose] noncomputable def pfCl (s : Nat) : Bool :=
  slK (Nat.mul J2PF.cnt 6)
    (findPtK J2PF.cnt J2PF.T (prodQK 315 9 (mask 9) 6 J2PF.T (bothK 3 J2PF.GI J2PFI)) J2PFCl)
    (Nat.mul 720 s) 720

end CertificateChecks.KernelGH74.J2CentE

#kon_slices CertificateChecks.KernelGH74.J2CentE.pfE 0 8
#kon_join CertificateChecks.KernelGH74.J2CentE.pfE_all CertificateChecks.KernelGH74.J2CentE.pfE 8
#kon_slices CertificateChecks.KernelGH74.J2CentE.pfH 0 8
#kon_join CertificateChecks.KernelGH74.J2CentE.pfH_all CertificateChecks.KernelGH74.J2CentE.pfH 8
#kon_slices CertificateChecks.KernelGH74.J2CentE.pfCl 0 16
#kon_join CertificateChecks.KernelGH74.J2CentE.pfCl_all CertificateChecks.KernelGH74.J2CentE.pfCl 16

end
