module

public import Certificates.Kernel.Sporadic.Fi22.N3153Data
public import Certificates.Data.Kernel.Fi22Nbr3153
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Sporadic.FischerOddCore.Fi22CentData
public meta import CFSG.Monster.B.Fischer.Fi22GraphCheckInputs
public meta import CFSG.Sporadic.FischerOddCore.Fi22ExtCheckInputs
import Certificates.Kernel.Co1B.GenTri2045
import CFSG.Certificates.Kernel.Common.Harness

#kc_repo #kc_ktree CFSG.KD.N2070 O "Certificates/Kernel/Sporadic/Fi22/data/ord2070.bin" 7020 4 28080 3042997870458489844

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.N2070

meta def permsM : Array (Array Nat) :=
  #[CFSG.Monster.B.Fischer.fi22GraphOuterArr, CFSG.Sporadic.FischerOddCore.fi22ExtArr 22,
    CFSG.Sporadic.FischerOddCore.fi22ExtArr 24, CFSG.Sporadic.FischerOddCore.fi22ExtArr 25,
    CFSG.Sporadic.FischerOddCore.fi22ExtArr 26]

end CertificateChecks.KernelSpor.N2070

#kmisc_packarrs CertificateChecks.KernelSpor.N2070.UP CertificateChecks.KernelSpor.N2070.permsM 12

namespace CertificateChecks.KernelSpor.N2070

open CFSG.KC.Enum CFSG.KC.N3153 CFSG.KD.N3153 CFSG.Sporadic.FischerOddCore

@[expose] noncomputable def imgUB (s : Nat) : Bool :=
  allBlk (Nat.mul (nat_lit 64) s) (fun x => bIf(Nat.blt x (nat_lit 3510),
    imgOK (nat_lit 3510) (nat_lit 693) (UP (nat_lit 0)) R M x, true)) (nat_lit 64)

@[expose] noncomputable def cellB (j : Nat) : Bool :=
  bIf(Nat.blt (Nat.mod j (nat_lit 10)) (fi22CentRefPoints.getD (Nat.div j (nat_lit 10)) []).length,
    cellK (nat_lit 3510) S (UP (Nat.add (Nat.div j (nat_lit 10)) (nat_lit 1)))
      (fi22CentRefPoints.getD (Nat.div j (nat_lit 10)) []) (nat_lit 4) (Nat.mod j (nat_lit 10))
      ((fi22CentRefBounds.getD (Nat.div j (nat_lit 10)) []).getD (Nat.mod j (nat_lit 10))
        (nat_lit 0)),
    true)

@[expose] noncomputable def injB (c : Nat) : Bool :=
  injK (nat_lit 3510) S (UP (Nat.add c (nat_lit 1))) (fi22CentRefPoints.getD c []) (nat_lit 4)
    (CFSG.KD.N2070.O c)

end CertificateChecks.KernelSpor.N2070

#kc_slices CertificateChecks.KernelSpor.N2070.ImgU CertificateChecks.KernelSpor.N2070.imgUB 55
#kc_slices CertificateChecks.KernelSpor.N2070.Cell CertificateChecks.KernelSpor.N2070.cellB 40
#kc_slices CertificateChecks.KernelSpor.N2070.Inj CertificateChecks.KernelSpor.N2070.injB 4

end
