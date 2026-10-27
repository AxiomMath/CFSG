module

public import Certificates.Kernel.Om2K.CertGen
meta import Certificates.Data.Holder1711.Om2Check
import CFSG.Assembly.ComponentTypeDefs
import CFSG.Assembly.LowTwoRankDefs

namespace CertificateChecks.KernelOm2

open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2Check
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2Data
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Check (reflTab)


meta def lettersM : List (Array Nat) := (lettersY (reflTab ())).toList

meta def tGensM : List (Array Nat) := wT.map (wY (lettersY (reflTab ())))

meta def subWM : List (Array Nat) := wSub.map (wY (lettersY (reflTab ())))

meta def fuseM : List (Array Nat) := wFuse0.map (wY (lettersY (reflTab ())))

meta def eltsM : List (Array Nat) :=
  [wT0, wI0, wJ0, wTc, wFuseC, wLiftA, wLiftB].map (wY (lettersY (reflTab ())))

meta def ccM : List (Array Nat) := wCc.map (wY (lettersY (reflTab ())))

meta def crM : List (Array Nat) := wCR.map (wY (lettersY (reflTab ())))

meta def mainCert : CFSG.Monster.B.Fischer.ArrCert :=
  let RT := reflTab ()
  orbFY (genY RT) (fCodeY (wY (lettersY RT) wT0)) 6301

meta def subCertsM : List CFSG.Monster.B.Fischer.ArrCert := subCertsY (reflTab ())

meta def transCertsM : List CFSG.Monster.B.Fischer.ArrCert :=
  let RT := reflTab ()
  let LY := lettersY RT
  let gT := (wT.map (wY LY)).toArray
  wSub.map fun w => orbFY (gT.push (wY LY w)) (fCodeY (wY LY wT0)) 6301

end CertificateChecks.KernelOm2

public section

set_option maxRecDepth 400000

#perm_tab CertificateChecks.KernelOm2.L CertificateChecks.KernelOm2.lettersM 9
#perm_tab CertificateChecks.KernelOm2.TG CertificateChecks.KernelOm2.tGensM 9
#perm_tab CertificateChecks.KernelOm2.WS CertificateChecks.KernelOm2.subWM 9
#perm_tab CertificateChecks.KernelOm2.FU CertificateChecks.KernelOm2.fuseM 9
#perm_tab CertificateChecks.KernelOm2.EL CertificateChecks.KernelOm2.eltsM 9
#perm_tab CertificateChecks.KernelOm2.CC CertificateChecks.KernelOm2.ccM 9
#perm_tab CertificateChecks.KernelOm2.CRG CertificateChecks.KernelOm2.crM 9
#arr_cert_tabs CertificateChecks.KernelOm2.Orb CertificateChecks.KernelOm2.mainCert 9 240
#arr_certs_idx CertificateChecks.KernelOm2.Sub CertificateChecks.KernelOm2.subCertsM
  CertificateChecks.KernelOm2.mainCert
#arr_certs_idx CertificateChecks.KernelOm2.Tr CertificateChecks.KernelOm2.transCertsM
  CertificateChecks.KernelOm2.mainCert

end
