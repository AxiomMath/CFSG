module

public import Certificates.Kernel.Misc.Perm.CharsCat
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Kernel.Sporadic.OddCore.MNK
public import Certificates.Data.Kernel.Spor.Chain
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.McLCheck
meta import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.McLCheck
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_chars_cat CertificateChecks.KernelSpor.OddCore.MHeis
  CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.mclHeisHex
#kmisc_hexflat CertificateChecks.KernelSpor.OddCore.MHeis
  CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.mclHeisHex 3 275 9 4

namespace CertificateChecks.KernelSpor.OddCore

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CertificateChecks.KernelSpor.MNd

@[expose] noncomputable def invPK (x xi : Nat) : Bool :=
  bAnd(canonK 275 9 (mask 9) (275 * 9) x, bAnd(canonK 275 9 (mask 9) (275 * 9) xi,
    invEqK 275 9 (mask 9) (275 * 9) x xi))

@[expose] noncomputable def heisK (X Y T : Nat) : Bool :=
  strictB (pinvS 275 9 (mask 9) X) fun XI => strictB (pinvS 275 9 (mask 9) Y) fun YI =>
  strictB (pc (pc (pc XI YI) X) Y) fun W =>
    bAnd(invPK X XI, bAnd(invPK Y YI, bAnd(sK X, bAnd(sK Y,
    bAnd(isId 5 X, bAnd(isId 5 Y, bAnd(isId 5 W, bAnd(bIf(Nat.beq W idK, false, true),
    bAnd(commK X W, bAnd(commK Y W, Nat.beq (pc (pc T X) T) XI))))))))))

theorem ok129020 :
    bAnd(heisK (MHeis.F 0) (MHeis.F 1) (S 0), heisK (MHeis.F 2) (MHeis.F 3) (F 17)) = true := by
  quickRfl

theorem ok129020_neg : bAnd(bIf(Nat.beq (pc (pc (S 0) (MHeis.F 2)) (S 0))
    (pinvS 275 9 (mask 9) (MHeis.F 2)), false, true),
    bIf(commK (MHeis.F 0) (MHeis.F 1), false, true)) = true := by
  quickRfl

end CertificateChecks.KernelSpor.OddCore

end
