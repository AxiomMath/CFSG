module

public import Certificates.Kernel.SporSch.Tits.Abel2261
public import Certificates.Kernel.Sporadic.Tits.LocH
public import Certificates.Kernel.Sporadic.Tits.LocJ
public import Certificates.Kernel.Sporadic.Tits.LocK
public import Certificates.Kernel.Sporadic.Tits.LocN
public import Certificates.Kernel.SporSch.Tits.GenList
public import CFSG.Certificates.Kernel.Spor.SiftEq
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4TInputs
public meta import CFSG.Quasithin.Vol2.Ch6Sec1Lem4TInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.T614

meta def eGenM : List (Array Nat) := (List.range 5).map CFSG.Quasithin.H13.Tits614.eGenArr

meta def g1M : Array Nat := CFSG.Sporadic.Schreier.Tits.titsGenArrs[1]!

meta def pInvM : Array Nat :=
  CFSG.Monster.B.Co2.Native.invCand 1755 CFSG.Quasithin.H13.Tits614.pArr

meta def labM : Array Nat := Id.run do
  let S := CFSG.Sporadic.Schreier.Tits.titsSArrs
  let g0 := S[0]!
  let g1 := S[1]!
  let g2 := S[2]!
  let mut lab : Array Nat := Array.replicate 1755 1755
  for x in [0:1755] do
    if lab[x]! == 1755 then
      lab := lab.set! x x
      let mut todo : List Nat := [x]
      for _ in [0:1755] do
        match todo with
        | [] => break
        | y :: rest =>
          todo := rest
          for z in [g0[y]!, g1[y]!, g2[y]!] do
            if lab[z]! == 1755 then
              lab := lab.set! z x
              todo := z :: todo
  return lab

end CertificateChecks.KernelSporSch.T614

#ks_perm CertificateChecks.KernelSporSch.T614P 11 CFSG.Quasithin.H13.Tits614.pArr
#ks_perm CertificateChecks.KernelSporSch.T614PI 11 CertificateChecks.KernelSporSch.T614.pInvM
#ks_perm CertificateChecks.KernelSporSch.T614G1 11 CertificateChecks.KernelSporSch.T614.g1M
#kst_plist CertificateChecks.KernelSporSch.T614EG 11 CertificateChecks.KernelSporSch.T614.eGenM
#kst_plist CertificateChecks.KernelSporSch.T614EL 11 CFSG.Quasithin.H13.Tits614.eArrs
#ks_perm CertificateChecks.KernelSporSch.T614Lab 11 CertificateChecks.KernelSporSch.T614.labM

namespace CertificateChecks.KernelSporSch.T614

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CertificateChecks.KernelSpor

@[expose] noncomputable def sfJ (X : Nat) : Bool :=
  siftK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) TitsJ.LR TitsJ.TRI TitsJ.BP 4 0 X

@[expose] noncomputable def sfK (X : Nat) : Bool :=
  siftK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) TitsK.LR TitsK.TRI TitsK.BP 5 0 X

@[expose] noncomputable def labT (q : Nat) : Nat := pg 11 (mask 11) CertificateChecks.KernelSporSch.T614Lab q

end CertificateChecks.KernelSporSch.T614

end
