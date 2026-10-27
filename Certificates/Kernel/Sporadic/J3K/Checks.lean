module

public import Certificates.Kernel.Sporadic.J3K.Defs
import CFSG.Certificates.Kernel.Common.Harness
import Certificates.Kernel.Sporadic.ON.Gen
public import CFSG.Certificates.Kernel.Spor.PChainSound
public import Mathlib.GroupTheory.Perm.Basic

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.J3K

theorem invAB_ok : invAB = true := by quickRfl
theorem bfs_ok : bfs = true := by quickRfl
theorem invL_ok : invL = true := by quickRfl
theorem tree1_ok : tree1 = true := by quickRfl
theorem labOK_ok : labOK = true := by quickRfl
theorem der_ok : der = true := by quickRfl

theorem rowsA_eq : CFSG.KS.Raw.unpack 80 80 (CFSG.KS.SporSch.payRun 80 J3SeedA.chars 0 0 0) =
    RAL.toArray := by decide +kernel
theorem rowsB_eq : CFSG.KS.Raw.unpack 80 80 (CFSG.KS.SporSch.payRun 80 J3SeedB.chars 0 0 0) =
    RBL.toArray := by decide +kernel
theorem colsA_eq : CFSG.Sporadic.J3.Native.transposeRows 80 RAL.toArray = CAJ := by decide +kernel
theorem colsB_eq : CFSG.Sporadic.J3.Native.transposeRows 80 RBL.toArray = CBJ := by decide +kernel
theorem mat_ok : CFSG.Sporadic.J3.Native.matOK RAL.toArray RBL.toArray = true := by decide +kernel

end CertificateChecks.KernelSpor.J3K


end
