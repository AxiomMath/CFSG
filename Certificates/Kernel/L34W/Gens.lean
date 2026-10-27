module

public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Data.Kernel.L34W.Tab42
public import CFSG.Certificates.Kernel.LocalCompUnpack
meta import Certificates.Data.CFSGNative.PSL3Four.Certificate
public import CFSG.Certificates.Kernel.Spor.RawSound

public section

set_option maxRecDepth 400000

#kmisc_packarrs CertificateChecks.KernelL34W.GT CFSG.PSL3Four.Native.gTabs 6

namespace CertificateChecks.KernelL34W

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.PSL3Four.Native

@[expose] noncomputable def gensOK (G : Nat → Nat) : Bool :=
  bAnd(Nat.beq gTabs.size (nat_lit 6), allN (nat_lit 6) fun k =>
    bAnd(bindArrK gTabs[k]! (nat_lit 42) (nat_lit 6) (G k),
      canonK (nat_lit 42) (nat_lit 6) (mask 6) (nat_lit 252) (G k)))

theorem gens_k : gensOK GT = true := by decide +kernel

theorem gens_neg : (!gensOK fun k => GT (nIf(Nat.beq k 0, 1, nIf(Nat.beq k 1, 0, k)))) = true := by
  decide +kernel

end CertificateChecks.KernelL34W

end
