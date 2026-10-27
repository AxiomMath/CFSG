module

public import Certificates.Kernel.Sporadic.OddCore.MulHCmd
public import Certificates.Kernel.Sporadic.OddCore.RowsCmd
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Kernel.McLAS.Rec3A
public import Certificates.Kernel.McLAS.RecK
public import Certificates.Kernel.McLAS.Tabs
public import Certificates.Kernel.Sporadic.OddCore.McLTL
public import Certificates.Kernel.Census.McLChain
public import Certificates.Data.Kernel.McLAS.Three
meta import Certificates.Kernel.McLAS.Meta
meta import Certificates.Kernel.Sporadic.OddCore.McLTL
import Certificates.Kernel.McLAS.Meta

namespace CertificateChecks.KernelMcLAS.M

open CFSG.Sporadic.Recognition.McLAS CFSG.Sporadic.SmallOddCore.Native CFSG.PSL3Four.Native

meta def lgM : Array (Array Nat) := #[tM 3, tM 4, tM 5]

meta def conjOf (gs : Array (Array Nat)) (E : Enum) (i : Nat) : Array Nat := Id.run do
  let mut path : List Nat := []
  let mut c := i
  for _ in [0:E.tabs.size] do
    if c == 0 then break
    path := E.lab[c]! :: path
    c := E.par[c]!
  let mut h := idM
  for l in path do
    h := comp 275 gs[l]! h
  return h

meta def r3E : Enum := bfs (fun j t => conjTab 275 pgM[j]! pgiM[j]! t) 2 x3AM 31000

meta def s20M : Array Nat :=
  ((List.range r3E.tabs.size).filter fun i =>
    comp 275 r3E.tabs[i]! (tM 3) == comp 275 (tM 3) r3E.tabs[i]!).toArray

meta def witMap : Std.HashMap (Array Nat) (Array Nat) := Id.run do
  let mut m : Std.HashMap (Array Nat) (Array Nat) := {}
  for i in s20M do
    let h := conjOf pgM r3E i
    let s := comp 275 (comp 275 (invM h) (tM 3)) h
    let E := bfs (fun j t => conjTab 275 kgM[j]! kgiM[j]! t) 3 s 400
    for q in [0:E.tabs.size] do
      let t := E.tabs[q]!
      if !m.contains t then
        let k := conjOf kgM E q
        m := m.insert t (comp 275 h (invM k))
  return m

meta def twM : Array (Array Nat) :=
  CertificateChecks.KernelSpor.McLTL.recT.map fun t => witMap.getD t idM

meta def twIM : Array (Array Nat) := twM.map invM

meta def b600M : Array Nat :=
  let kr := mulRec kgM 30000
  ((List.range kr.size).filter fun i =>
    let t := kr[i]!
    t != idM && comp 275 t (comp 275 t t) == idM &&
      ((List.range 275).filter fun p => t[p]! == p).length != 5).toArray

meta def recTM : Array (Array Nat) := CertificateChecks.KernelSpor.McLTL.recT

meta def r3TabsM : Array (Array Nat) := r3E.tabs

meta def x1sM : Array (Array Nat) := #[tM 0]

end CertificateChecks.KernelMcLAS.M

public section

set_option maxRecDepth 400000

#kmulh CertificateChecks.KernelMcLAS.RL 275 9 CertificateChecks.KernelMcLAS.M.ids3M
  CertificateChecks.KernelMcLAS.M.lgM CertificateChecks.KernelMcLAS.M.idM 1000
#krows CertificateChecks.KernelMcLAS.S20 CertificateChecks.KernelMcLAS.M.s20M
#krows CertificateChecks.KernelMcLAS.B600 CertificateChecks.KernelMcLAS.M.b600M
#kfind CertificateChecks.KernelMcLAS.TinA CertificateChecks.KernelMcLAS.M.r3TabsM
  CertificateChecks.KernelMcLAS.M.recTM
#kfind CertificateChecks.KernelMcLAS.XinT CertificateChecks.KernelMcLAS.M.recTM
  CertificateChecks.KernelMcLAS.M.x1sM
#kmisc_packarrs CertificateChecks.KernelMcLAS.TW CertificateChecks.KernelMcLAS.M.twM 9
#kmisc_packarrs CertificateChecks.KernelMcLAS.TWI CertificateChecks.KernelMcLAS.M.twIM 9

namespace CertificateChecks.KernelMcLAS

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KS.McLAS

@[expose] noncomputable def cmK (i : Nat) : Bool :=
  bIf(commK (R3A.T i) (TT.F (nat_lit 3)), inRowK S20 (nat_lit 20) i, true)

@[expose] noncomputable def cmSl (s : Nat) : Bool :=
  slK R3A.cnt cmK (Nat.mul s (nat_lit 200)) (nat_lit 200)

@[expose] noncomputable def tcK (i : Nat) : Bool :=
  strictB (CertificateChecks.KernelSpor.McLTT.T i) fun t =>
    bIf(ord3K t, bIf(atK R3A.cnt R3A.T TinA i t, true,
      bAnd(canonK 275 9 (mask 9) (275 * 9) (TW i), bAnd(canonK 275 9 (mask 9) (275 * 9) (TWI i),
      bAnd(invEqK 275 9 (mask 9) (275 * 9) (TW i) (TWI i),
      bAnd(siftK 275 9 (mask 9) (275 * 9) (pidn 275 9) CertificateChecks.KernelCensus.McLC.LR
          CertificateChecks.KernelCensus.McLC.TRI CertificateChecks.KernelCensus.McLC.BP 5 0 (TW i),
        Nat.beq (pcK (TW i) t) (pcK (TT.F (nat_lit 3)) (TW i))))))), true)

@[expose] noncomputable def tcSl (s : Nat) : Bool :=
  slK CertificateChecks.KernelSpor.McLTT.cnt tcK (Nat.mul s (nat_lit 200)) (nat_lit 200)

@[expose] noncomputable def bK (j : Nat) : Bool :=
  strictB (r32 B600 j) fun i => bAnd(Nat.blt i RK.cnt, strictB (RK.T i) fun t =>
    bAnd(ord3K t, bAnd(bIf(Nat.beq (fixK t) (nat_lit 5), false, true),
      bIf(Nat.blt (Nat.succ j) (nat_lit 600), Nat.blt i (r32 B600 (Nat.succ j)), true))))

@[expose] noncomputable def bSl (s : Nat) : Bool :=
  slK (nat_lit 600) bK (Nat.mul s (nat_lit 200)) (nat_lit 200)

@[expose] noncomputable def rlSl (s : Nat) : Bool :=
  recSlK true RL.G RL.GI 3 RL.cnt RL.T RL.PL RL.POS RL.SRT RL.SRI RL.HS RL.HSI
    (Nat.mul s (nat_lit 200)) (nat_lit 200)

end CertificateChecks.KernelMcLAS

end
