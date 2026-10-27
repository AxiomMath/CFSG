module

public import Certificates.Data.Kernel.SmithL6KR
public import Certificates.Kernel.SmithL6K.Data
public import Certificates.Kernel.SmithL6K.DataW
public import Certificates.Kernel.SmithL6K.DataO
public import Certificates.Kernel.SmithL6K.DataR
public import Certificates.Kernel.SmithL6Coll.Data

public section

namespace CertificateChecks.KernelSmithL6K

open CFSG.SmithL6 CFSG.SmithL6.K CFSG.SmithL6.CollK

theorem trL_ok : (trL == CertificateChecks.KernelSmithL6Coll.rtop.flatten && trL.length == 651 &&
    trL.all (·.length == 9)) = true := by decide +kernel

theorem trG_ok : (trGens.toList.all (fun p => decide (p < 1953) &&
    apK (tcl.getD p []) (fldW 20 wtP 0) == fldW 20 wtP 0) &&
    trGens.toList.map (ucolsK tcP idxP p0) == trG && trG.all (·.length == 9)) = true := by
  decide +kernel

theorem trLift_ok : (tvImgP tcP idxP 0 224 == 224 && fixW0K p0 (tvImgP tcP idxP 0) &&
    fixW0K p0 (tvImgP tcP idxP 224) &&
    fixW0K p0 (fun x => tvImgP tcP idxP 0 (tvImgP tcP idxP 224 x)) && fixW0K p0 (tauP tcP idxP) &&
    trR == [colsF p0 (tvImgP tcP idxP 0), colsF p0 (tvImgP tcP idxP 224),
      colsF p0 (fun x => tvImgP tcP idxP 0 (tvImgP tcP idxP 224 x)), colsF p0 (tauP tcP idxP)]) =
    true := by decide +kernel

theorem trTree_ok : treeK 651 6 (rootK trR trL) (edgeK trG trL) trrt trtr = true := by
  decide +kernel

end CertificateChecks.KernelSmithL6K
