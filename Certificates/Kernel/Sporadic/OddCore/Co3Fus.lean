module

public import Certificates.Kernel.Sporadic.Co3.C
public import Certificates.Kernel.Sporadic.Co3.T
public import Certificates.Kernel.Sporadic.Co3.Single
public import Certificates.Kernel.Sporadic.OddCore.MulHCmd
public import Certificates.Kernel.Sporadic.OddCore.RowsCmd
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
public import Certificates.Data.Kernel.Spor.MulHQ
public import CFSG.Sporadic.SmallOddCore.Co3FusionCheckInputs
meta import CFSG.Sporadic.SmallOddCore.Co3FusionCheckInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.Co3FT CFSG.Sporadic.SmallOddCore.co3FusionHex

#kmisc_hexflat CertificateChecks.KernelSpor.Co3FT CFSG.Sporadic.SmallOddCore.co3FusionHex
  3 276 9 191

namespace CertificateChecks.KernelSpor.Co3Fus

open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.PSL3Four.Native
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Co3

meta def idM : Array Nat := idTab 276
meta def ids8M : Array (Array Nat) := Array.replicate 8 idM
meta def tM : Array (Array Nat) := co3TArrs.extract 0 8
meta def tiM : Array (Array Nat) := tM.map (CFSG.Monster.B.Co2.Native.invCand 276)
meta def eRecM : Array (Array Nat) :=
  (bfs (fun j t => conjTab 276 idM tM[j]! t) 8 idM 2000).tabs
meta def eClM : Array (Array Nat) :=
  (eRecM.map fun x => (tM ++ tiM).map fun g => comp 276 x g).flatten
meta def wM : Array (Array Nat) := (List.range 191).toArray.map fun k => natArr (co3FusionTbl k)
meta def wiM : Array (Array Nat) := wM.map (CFSG.Monster.B.Co2.Native.invCand 276)
meta def flM : Array Nat :=
  (List.range 191).toArray.map fun k => if co3FusionFlags.getD k false then 1 else 0
meta def tgtM (b : Nat) : Array Nat := if b == 1 then co3ZArr else co3TtArr
meta def isInvM (x : Array Nat) : Bool := comp 276 x x == idM && x != idM
meta def wjM : Array Nat := eRecM.map fun x =>
  if isInvM x then
    ((List.range 191).find? fun k => conjTab 276 wM[k]! wiM[k]! x == tgtM flM[k]!).getD 0
  else 0
meta def invIdxL : List Nat := (List.range eRecM.size).filter fun i => isInvM eRecM[i]!
meta def piM : Array Nat := (List.range eRecM.size).toArray.map fun i => invIdxL.idxOf i
meta def ptsM : Array Nat := ((List.range 191).toArray.map fun p =>
  (List.range 191).toArray.map fun j =>
    let i := invIdxL.getD p 0
    let s := eRecM[i]!
    if flM[j]! == flM[wjM[i]!]! then 0 else
      ((List.range 276).find? fun x =>
        (wM[j]!)[s[(wiM[j]!)[x]!]!]! != (tgtM flM[j]!)[x]!).getD 0).flatten

#kmulh CertificateChecks.KernelSpor.Co3E 276 9 ids8M tM idM 2000
#kfind CertificateChecks.KernelSpor.Co3ECl eRecM eClM
#kmisc_packarrs CertificateChecks.KernelSpor.Co3FI wiM 9
#krows CertificateChecks.KernelSpor.Co3FL flM
#krows CertificateChecks.KernelSpor.Co3WJ wjM
#krows CertificateChecks.KernelSpor.Co3PI piM
#krows CertificateChecks.KernelSpor.Co3PTS ptsM

end CertificateChecks.KernelSpor.Co3Fus

namespace CertificateChecks.KernelSpor.Co3Fus

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp 276 9 (mask 9) p q

@[expose] noncomputable def idK : Nat := pidn 276 9

@[expose] noncomputable def pt (p x : Nat) : Nat := pg 9 (mask 9) p x

@[expose] noncomputable def involK (s : Nat) : Bool :=
  bAnd(Nat.beq (pc s s) idK, bIf(Nat.beq s idK, false, true))

@[expose] noncomputable def tgt (b : Nat) : Nat := nIf(Nat.beq b (nat_lit 1), Co3Z, Co3Tt)

@[expose] noncomputable def fl (j : Nat) : Nat := r32 Co3FL j

@[expose] noncomputable def fusesK (j s : Nat) : Bool :=
  Nat.beq (pc (pc (Co3FT.F j) s) (Co3FI j)) (tgt (fl j))

@[expose] noncomputable def missK (j s x : Nat) : Bool :=
  bAnd(Nat.blt x (nat_lit 276),
    bIf(Nat.beq (pt (Co3FT.F j) (pt s (pt (Co3FI j) x))) (pt (tgt (fl j)) x), false, true))

@[expose] noncomputable def fusPtK (i : Nat) : Bool :=
  strictB (Co3E.T i) (fun s => bIf(involK s,
    strictB (r32 Co3WJ i) (fun j => strictB (r32 Co3PI i) (fun p =>
    bAnd(Nat.blt j (nat_lit 191), bAnd(Nat.blt p (nat_lit 191), bAnd(fusesK j s,
      allN 191 (fun j' => bIf(Nat.beq (fl j') (fl j), true,
        missK j' s (r32 Co3PTS (Nat.add (Nat.mul p (nat_lit 191)) j'))))))))), true))

theorem base_ok : bAnd(szOK 276 9, bAnd(canonK 276 9 (mask 9) (276 * 9) idK,
    bAnd(CFSG.KS.Prim.idK 276 9 (mask 9), bAnd(canonK 276 9 (mask 9) (276 * 9) Co3Z,
    bAnd(canonK 276 9 (mask 9) (276 * 9) Co3Tt, bAnd(Nat.beq Co3E.cnt 1024,
    bAnd(penumHdK idK Co3E.cnt 2000 Co3E.T Co3E.PL,
    allN 8 (fun j => bAnd(Nat.beq (Co3E.GI j) (Co3T.S j), bAnd(Nat.beq (Co3E.G j) idK,
      bAnd(canonK 276 9 (mask 9) (276 * 9) (Co3T.S j),
        canonK 276 9 (mask 9) (276 * 9) (Co3T.SI j)))))))))))) = true := by
  quickRfl

theorem flags_ok : allN 191 (fun k => Nat.beq (fl k)
    (nIf(CFSG.Sporadic.SmallOddCore.co3FusionFlags.getD k false, 1, 0))) = true := by
  quickRfl

@[expose] noncomputable def witK (k : Nat) : Bool :=
  bAnd(canonK 276 9 (mask 9) (276 * 9) (Co3FT.F k),
  bAnd(invEqK 276 9 (mask 9) (276 * 9) (Co3FT.F k) (Co3FI k),
  bAnd(canonK 276 9 (mask 9) (276 * 9) (Co3FI k),
  bAnd(Co3Text.hiOK (Co3FT.F k), Co3C.sift (Co3FT.F k)))))

theorem wit0 : slK 191 witK 0 96 = true := by quickRfl
theorem wit1 : slK 191 witK 96 95 = true := by quickRfl

theorem fus0 : slK Co3E.cnt fusPtK 0 256 = true := by quickRfl
theorem fus1 : slK Co3E.cnt fusPtK 256 256 = true := by quickRfl
theorem fus2 : slK Co3E.cnt fusPtK 512 256 = true := by quickRfl
theorem fus3 : slK Co3E.cnt fusPtK 768 256 = true := by quickRfl

theorem counts : bAnd(Nat.beq (cntBelowK Co3E.cnt (fun i => strictB (Co3E.T i) involK) 16) 191,
    bAnd(Nat.beq (cntBelowK Co3E.cnt (fun i => bAnd(strictB (Co3E.T i) involK,
      Nat.beq (fl (r32 Co3WJ i)) 1)) 16) 55,
    Nat.beq (cntBelowK Co3E.cnt (fun i => bAnd(strictB (Co3E.T i) involK,
      bIf(Nat.beq (fl (r32 Co3WJ i)) 1, false, true))) 16) 136)) = true := by
  quickRfl

end CertificateChecks.KernelSpor.Co3Fus

end
