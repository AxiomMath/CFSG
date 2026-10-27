module

public import Certificates.Kernel.Om1K.Elts
meta import Certificates.Data.Holder1711.Om1Check
meta import Certificates.Kernel.Om1K.Defs
meta import Certificates.Data.Holder1711.Om2Check
meta import Certificates.Data.Kernel.BfsPin
meta import Certificates.Data.Kernel.SetOrb

namespace CertificateChecks.KernelOm1.A

open CFSG.Monster.B.Fischer CFSG.Monster.B.Co2.Native
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Check
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Data

meta def gXM : Array (Array Nat) := wsA (reflTab ()) wX
meta def gXiM : Array (Array Nat) := wsA (reflTab ()) wXr

meta def orb0M : ArrCert := orbF gXM (fCode (eA 15)) 3151

meta def subsM : List ArrCert := subCerts (reflTab ())

meta def trsM : List ArrCert :=
  let RT := reflTab ()
  let gT := wsA RT wT
  wSub.map fun w => orbF (gT.push (wA RT w)) (fCode (eA 15)) 3151

meta def orbAM : ArrCert := orbF gXM (fCode (eA 3)) 3781

meta def rootM : Nat := (fCode (eA 23))[0]!

meta def roM : ArrCert := orbF gXM #[rootM] 241

meta def transM : Array (Array Nat) × Array (Array Nat) := Id.run do
  let c := roM
  let mut tt : Array (Array Nat) := #[idA 240]
  let mut ti : Array (Array Nat) := #[idA 240]
  for i in [1:c.pts.size] do
    tt := tt.push (compA 240 gXM[c.lab[i]!]! tt[c.par[i]!]!)
    ti := ti.push (compA 240 ti[c.par[i]!]! gXiM[c.lab[i]!]!)
  return (tt, ti)

meta def ttM : List (Array Nat) := transM.1.toList
meta def tiM : List (Array Nat) := transM.2.toList

meta def schM : Array (Array Nat) × Array (Array Nat) := Id.run do
  let c := roM
  let (tt, ti) := transM
  let mut hs : Array (Array Nat) := #[]
  let mut ix : Array (Array Nat) := #[]
  for p in [0:c.pts.size] do
    for k in [0:gXM.size] do
      let q := (c.edges[p]!)[k]!
      let h := compA 240 ti[q]! (compA 240 gXM[k]! tt[p]!)
      if hs.size < 10 && !(h == idA 240) && !(hs.contains h) then
        hs := hs.push h
        ix := ix.push #[q, k, p]
  return (hs, ix)

meta def sgM : List (Array Nat) := schM.1.toList
meta def ixM : List (Array Nat) := schM.2.toList

meta def ocM : ArrCert := orbF schM.1 (fCode (eA 23)) 3781

end CertificateChecks.KernelOm1.A

public section

set_option maxRecDepth 400000

#arr_cert_tabs CertificateChecks.KernelOm1.A.Orb CertificateChecks.KernelOm1.A.orb0M 8 240
#arr_certs_idx CertificateChecks.KernelOm1.A.Sub CertificateChecks.KernelOm1.A.subsM
  CertificateChecks.KernelOm1.A.orb0M
#arr_certs_idx CertificateChecks.KernelOm1.A.Tr CertificateChecks.KernelOm1.A.trsM
  CertificateChecks.KernelOm1.A.orb0M
#arr_cert_tabs CertificateChecks.KernelOm1.A.OA CertificateChecks.KernelOm1.A.orbAM 8 240
#arr_cert_tabs CertificateChecks.KernelOm1.A.RO CertificateChecks.KernelOm1.A.roM 8 240
#perm_tab CertificateChecks.KernelOm1.A.TT CertificateChecks.KernelOm1.A.ttM 8
#perm_tab CertificateChecks.KernelOm1.A.TI CertificateChecks.KernelOm1.A.tiM 8
#perm_tab CertificateChecks.KernelOm1.A.SG CertificateChecks.KernelOm1.A.sgM 8
#perm_tab CertificateChecks.KernelOm1.A.IX CertificateChecks.KernelOm1.A.ixM 8
#arr_cert_tabs CertificateChecks.KernelOm1.A.OC CertificateChecks.KernelOm1.A.ocM 8 240

end
