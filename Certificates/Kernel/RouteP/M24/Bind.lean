module

public import CFSG.Certificates.Kernel.RouteP.M24Text
public meta import CFSG.Certificates.Kernel.Common.StrChunks
public import CFSG.Certificates.Kernel.Common.StrChunks

public section

set_option maxRecDepth 1000000

#str_chunks CertificateChecks.KernelRouteP.M24.TTree
  Certificates.RouteP.M24Defect.treeText 140000 1000000 512
#str_chunks CertificateChecks.KernelRouteP.M24.TCombo
  Certificates.RouteP.M24Defect.comboText 140000 1000000 512
#str_chunks CertificateChecks.KernelRouteP.M24.TBez
  Certificates.RouteP.M24Defect.bezoutText 140000 1000000 512

namespace CertificateChecks.KernelRouteP.M24

open CFSG.KC.RouteP CFSG.KS.RouteP Certificates.RouteP.M24Defect

theorem tree_ok : treeOKL TTree.chars = true := by decide +kernel

theorem combo_ascii : TCombo.chars.all (fun c => decide (c.toNat < 128)) = true := by
  decide +kernel

theorem combo_ok : comboOKL TCombo.chars = true := by decide +kernel

theorem bez_ok : bezOKL TBez.chars = true := by decide +kernel

theorem treeTab_eq : treeTab () = (treeTabL TTree.chars).toArray := treeTab_ofList TTree.eq tree_ok

theorem comboData_eq : comboData () = comboDataL TCombo.chars :=
  comboData_ofList TCombo.eq (by simpa using combo_ascii) combo_ok

theorem sData_eq : sData () = sDataL TBez.chars := sData_ofList TBez.eq bez_ok

theorem tData_eq : tData () = tDataL TBez.chars := tData_ofList TBez.eq bez_ok

end CertificateChecks.KernelRouteP.M24
