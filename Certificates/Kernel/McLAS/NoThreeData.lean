module

public import Certificates.Kernel.Sporadic.OddCore.MN
public import Certificates.Kernel.Sporadic.OddCore.McLTwo
public import Certificates.Kernel.Sporadic.OddCore.RowsCmd
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Data.Kernel.McLAS.NoThree
meta import Certificates.Kernel.Sporadic.OddCore.MN
meta import Certificates.Kernel.Sporadic.OddCore.McLTwo

public section

namespace CertificateChecks.KernelMcLAS.NoThrM

open CFSG.Sporadic.SmallOddCore.Native CFSG.PSL3Four.Native

meta def idM : Array Nat := idTab 275
meta def cmp (p q : Array Nat) : Array Nat := comp 275 p q
meta def invM (p : Array Nat) : Array Nat := CFSG.Monster.B.Co2.Native.invCand 275 p

meta def ysM : Array (Array Nat) :=
  let k1 := CertificateChecks.KernelSpor.MNd.k1M
  let k1i := CertificateChecks.KernelSpor.MNd.k1iM
  let st := fun j t => conjTab 275 k1[j]! k1i[j]! t
  (bfs st 2 CertificateChecks.KernelSpor.MNd.q7M 120000).tabs ++
    (bfs st 2 CertificateChecks.KernelSpor.MNd.q15M 120000).tabs

meta def sM : Array (Array Nat) := CertificateChecks.KernelSpor.McLTwo.recM
meta def siM : Array (Array Nat) := CertificateChecks.KernelSpor.McLTwo.eiM
meta def t0M : Array Nat := CertificateChecks.KernelSpor.MNd.cM 4

meta def invoM (x : Array Nat) : Bool := x != idM && cmp x x == idM

meta def zIdx : Nat :=
  ((List.range sM.size).find? fun s => invoM sM[s]! && sM.all fun x => cmp x sM[s]! == cmp sM[s]! x).getD 0

meta def vIdx : Nat :=
  ((List.range sM.size).find? fun s => s != zIdx && invoM sM[s]! &&
    cmp sM[s]! sM[zIdx]! == cmp sM[zIdx]! sM[s]!).getD 0

meta def conjM (x : Array Nat) : Array Nat := Id.run do
  let pg := CertificateChecks.KernelSpor.MNd.pgM
  let pgi := CertificateChecks.KernelSpor.MNd.pgiM
  let E := bfs (fun j t => conjTab 275 pg[j]! pgi[j]! t) 2 t0M 30000
  let k := (E.tabs.findIdx? (· == x)).getD 0
  let mut acc := idM
  let mut cur := k
  for _ in [0:E.tabs.size] do
    if cur == 0 then break
    acc := cmp acc pg[E.lab[cur]!]!
    cur := E.par[cur]!
  return acc

meta def gM : Array (Array Nat) :=
  #[conjM sM[zIdx]!, conjM sM[vIdx]!, conjM (cmp sM[zIdx]! sM[vIdx]!)]
meta def giM : Array (Array Nat) := gM.map invM
meta def jM : Array Nat := #[zIdx, vIdx]

meta def ordM (z : Array Nat) : Nat := Id.run do
  let mut seen := Array.replicate 275 false
  let mut o := 1
  for x in [0:275] do
    if !seen[x]! then
      let mut c := 0
      let mut y := x
      for _ in [0:276] do
        seen := seen.set! y true
        c := c + 1
        y := z[y]!
        if y == x then break
      o := Nat.lcm o c
  return o

meta def witM (g gi y : Array Nat) : Nat := Id.run do
  let yy := cmp g (cmp y gi)
  let mut best := 0
  let mut cost := 1000000
  for a in [0:sM.size] do
    if cost ≤ 3 then break
    let z := cmp yy (cmp sM[a]! (cmp yy siM[a]!))
    let o := ordM z
    let mut e := 1
    let mut m := o
    for _ in [0:8] do
      if m % 3 == 0 then
        m := m / 3
        e := e * 3
    if 1 < m && e < 256 && e + m < cost then
      cost := e + m
      best := a + 256 * e + 65536 * m
  return best

meta def wM : Array Nat :=
  (List.range 3).toArray.flatMap fun j => ysM.map fun y => witM gM[j]! giM[j]! y

end CertificateChecks.KernelMcLAS.NoThrM

#kmisc_packarrs CertificateChecks.KernelMcLAS.NoThrG CertificateChecks.KernelMcLAS.NoThrM.gM 9
#kmisc_packarrs CertificateChecks.KernelMcLAS.NoThrGI CertificateChecks.KernelMcLAS.NoThrM.giM 9
#krows CertificateChecks.KernelMcLAS.NoThrJ CertificateChecks.KernelMcLAS.NoThrM.jM
#krows CertificateChecks.KernelMcLAS.NoThrW CertificateChecks.KernelMcLAS.NoThrM.wM

namespace CertificateChecks.KernelMcLAS

open CFSG.KC.Enum CFSG.KS.PEnum CFSG.KS.McLNT

@[expose] noncomputable def noThrU (j : Nat) : Nat :=
  nIf(Nat.beq j (nat_lit 0), CertificateChecks.KernelSpor.McLTwoS.T (r32 NoThrJ (nat_lit 0)),
    nIf(Nat.beq j (nat_lit 1), CertificateChecks.KernelSpor.McLTwoS.T (r32 NoThrJ (nat_lit 1)),
      pc (CertificateChecks.KernelSpor.McLTwoS.T (r32 NoThrJ (nat_lit 0)))
        (CertificateChecks.KernelSpor.McLTwoS.T (r32 NoThrJ (nat_lit 1)))))

@[expose] noncomputable def noThrK (j i : Nat) : Bool :=
  ntItemK NoThrG NoThrGI CertificateChecks.KernelSpor.MN.Q1a.T CertificateChecks.KernelSpor.MN.Q1e.T
    CertificateChecks.KernelSpor.McLTwoS.T CertificateChecks.KernelSpor.McLTwoEI NoThrW j i

end CertificateChecks.KernelMcLAS

end
