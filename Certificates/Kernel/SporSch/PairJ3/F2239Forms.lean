module

public import Certificates.Data.Kernel.SporSch.J3F80
public import Certificates.Kernel.J4Q.MatData
public import Certificates.Kernel.SporSch.PairJ3.FormsText
public import Certificates.Kernel.SporSch.PairJ3.Tab
public import Certificates.Kernel.Sporadic.J3K.Data
public import CFSG.Certificates.Kernel.Common.Harness
public meta import Certificates.Kernel.SporSch.J4S.Gen
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.SporSch.J4S.Gen

public section

set_option maxRecDepth 400000

#kc_repo #kc_ktree CFSG.KD.J3F FW "Certificates/Kernel/SporSch/PairJ3/f2239/forms.bin"
  405 4 2493180 14203776186070957187
#kc_repo #kc_ktree CFSG.KD.J3F SG "Certificates/Kernel/SporSch/PairJ3/f2239/sort.bin"
  2 4 12312 7484510681478955162
#kc_repo #kc_ktree CFSG.KD.J3F SGI "Certificates/Kernel/SporSch/PairJ3/f2239/sortinv.bin"
  2 4 12312 2891131743385737575

namespace CertificateChecks.KernelSporSch.F2239

open CFSG.KC.Enum CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KS CFSG.KS.SporSch.J3F CFSG.KD.J3F
open CertificateChecks.KernelSpor.J3K CertificateChecks.KernelSporSch

@[expose] noncomputable def A1 : Nat := packRowsK RAL
@[expose] noncomputable def A2 : Nat := packRowsK RBL
@[expose] noncomputable def A1T : Nat := trJ t0 t1 t2 t3 t4 t5 t6 A1
@[expose] noncomputable def A2T : Nat := trJ t0 t1 t2 t3 t4 t5 t6 A2

@[expose] noncomputable def fF (r : Nat) : Bool :=
  formsF c rm t0 t1 t2 t3 t4 t5 t6 usK dgK FW (PJ3.S 0) (PJ3.S 1) A1 A1T A2 A2T r

@[expose] noncomputable def chunks : List (List Char) :=
  [PJ3FT.c0, PJ3FT.c1, PJ3FT.c2, PJ3FT.c3, PJ3FT.c4, PJ3FT.c5, PJ3FT.c6, PJ3FT.c7, PJ3FT.c8,
    PJ3FT.c9, PJ3FT.c10, PJ3FT.c11, PJ3FT.c12, PJ3FT.c13, PJ3FT.c14, PJ3FT.c15, PJ3FT.c16,
    PJ3FT.c17, PJ3FT.c18, PJ3FT.c19, PJ3FT.c20, PJ3FT.c21, PJ3FT.c22, PJ3FT.c23, PJ3FT.c24,
    PJ3FT.c25, PJ3FT.c26, PJ3FT.c27, PJ3FT.c28, PJ3FT.c29, PJ3FT.c30, PJ3FT.c31, PJ3FT.c32,
    PJ3FT.c33, PJ3FT.c34, PJ3FT.c35, PJ3FT.c36, PJ3FT.c37]

@[expose] noncomputable def fC (j : Nat) : Bool :=
  wordsK FW (nat_lit 162) (Nat.mul (nat_lit 162) j) (chunks.getD j [])

theorem rows : bAnd(rows80K RAL, rows80K RBL) = true := by quickRfl

theorem sort : sortK FW SG SGI 6156 = true := by quickRfl

end CertificateChecks.KernelSporSch.F2239

#kss_slices CertificateChecks.KernelSporSch.F2239.FWC CertificateChecks.KernelSporSch.F2239.fC 1 38
#kss_slices CertificateChecks.KernelSporSch.F2239.FFS CertificateChecks.KernelSporSch.F2239.fF 162 38

end
