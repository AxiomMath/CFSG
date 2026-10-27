module

public import Certificates.Kernel.Sporadic.Fi22.N3153Data
public import Certificates.Data.Kernel.Fi22Search2071
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Sporadic.FischerOddCore.Fi22CentData
public meta import CFSG.Sporadic.FischerOddCore.Fi22CentCheckInputs
public meta import CFSG.Sporadic.FischerOddCore.Fi22ExtCheckInputs
import Certificates.Kernel.Co1B.GenTri2045
import CFSG.Certificates.Kernel.Common.Harness

#kc_repo #kc_ktree CFSG.KD.S2071 D "Certificates/Kernel/Sporadic/Fi22/data/srch2071.bin" 392 4 54096 3091335387369609619
#kc_repo #kc_ktree CFSG.KD.S2071 O "Certificates/Kernel/Sporadic/Fi22/data/ord2071.bin" 7020 4 7020 11311879831167741424

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.N2071

meta def permsM : Array (Array Nat) :=
  ((Array.range 66).map fun j => CFSG.Sporadic.FischerOddCore.fi22CentArr (240 + j)).push
    (CFSG.Sporadic.FischerOddCore.fi22ExtArr 21)

end CertificateChecks.KernelSpor.N2071

#kmisc_packarrs CertificateChecks.KernelSpor.N2071.PP CertificateChecks.KernelSpor.N2071.permsM 12

namespace CertificateChecks.KernelSpor.N2071

open CFSG.KC.Enum CFSG.KC.N3153 CFSG.KC.S2071 CFSG.KD.N3153 CFSG.Sporadic.FischerOddCore
open CFSG.Sporadic.FischerOddCore.Native

@[expose] def nodesK : Array SNode :=
  (fi22SearchNodeData.map fun N => (⟨N.1, N.2.1, N.2.2.1, N.2.2.2.1, N.2.2.2.2⟩ : SNode)).toArray

@[expose] def srcCols : List Nat := [730877637, 658955187, 750283541, 1105569919, 745883633,
  1112879537, 1434709558, 423835125, 1238362071, 1261704378]

@[expose] noncomputable def nodeB (i : Nat) : Bool :=
  strictB (PP (nat_lit 66)) fun T => nodeK (nat_lit 3510) S T (fun j => PP j) (nat_lit 64)
    (fun a => PP (Nat.add (nat_lit 64) a)) (nat_lit 2) nodesK fi22SearchBase srcCols (nat_lit 4)
    CFSG.KD.S2071.D i

@[expose] noncomputable def srcB (e : Nat) : Bool :=
  strictB (PP (nat_lit 66)) fun T => srcColK (nat_lit 3510) S T fi22SearchBase (nat_lit 4) e
    (srcCols.getD e (nat_lit 0))

@[expose] noncomputable def imgB (a s : Nat) : Bool :=
  allBlk (Nat.mul (nat_lit 64) s) (fun x => bIf(Nat.blt x (nat_lit 3510),
    imgOK (nat_lit 3510) (nat_lit 693) (PP (Nat.add (nat_lit 64) a)) R M x, true)) (nat_lit 64)

@[expose] noncomputable def img0B (s : Nat) : Bool := imgB (nat_lit 0) s

@[expose] noncomputable def img1B (s : Nat) : Bool := imgB (nat_lit 1) s

end CertificateChecks.KernelSpor.N2071

#kc_slices CertificateChecks.KernelSpor.N2071.Node CertificateChecks.KernelSpor.N2071.nodeB 138
#kc_slices CertificateChecks.KernelSpor.N2071.Src CertificateChecks.KernelSpor.N2071.srcB 10
#kc_slices CertificateChecks.KernelSpor.N2071.ImgA0 CertificateChecks.KernelSpor.N2071.img0B 55
#kc_slices CertificateChecks.KernelSpor.N2071.ImgA1 CertificateChecks.KernelSpor.N2071.img1B 55

namespace CertificateChecks.KernelSpor.N2071

open CFSG.KC.Enum CFSG.KC.N3153 CFSG.KD.N3153 CFSG.Sporadic.FischerOddCore

theorem inj : strictB (PP 66) (fun T => injK 3510 S T fi22SearchBase 4 (CFSG.KD.S2071.O 0)) =
    true := by quickRfl

end CertificateChecks.KernelSpor.N2071

end
