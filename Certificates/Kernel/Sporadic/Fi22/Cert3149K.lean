
module

public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Certificates.Kernel.Th.S.Chars
public import Certificates.Data.Kernel.Spor.HexAt
public import Certificates.Data.Kernel.Spor.TextAt
public import CFSG.Certificates.Kernel.Enum.Defs
public import CFSG.Monster.B.Fischer.Fi22CertInputs
public meta import CFSG.Monster.B.Fischer.Fi22CertInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#th_chars CertificateChecks.KernelSpor.F3149.SOC CFSG.Monster.B.Fischer.fi22StabOrbitsHex
#th_chars CertificateChecks.KernelSpor.F3149.MGC CFSG.Monster.B.Fischer.fi22MergeHex

namespace CertificateChecks.KernelSpor.F3149

open CFSG.Monster.B.Fischer

meta def soM : Array (Array Nat) :=
  (List.range 65).toArray.map fun j => (List.range 54).toArray.map fun i =>
    CFSG.Monster.B.Max2.Native.hexAt fi22StabOrbitsBytes (3 * (54 * j + i)) 3

meta def mgM : Array (Array Nat) :=
  (List.range 877).toArray.map fun j => (List.range 56).toArray.map fun i =>
    CFSG.Monster.B.Max2.Native.hexAt fi22MergeBytes (56 * j + i) 1

end CertificateChecks.KernelSpor.F3149

#kmisc_packarrs CertificateChecks.KernelSpor.F3149.SO CertificateChecks.KernelSpor.F3149.soM 12
#kmisc_packarrs CertificateChecks.KernelSpor.F3149.MG CertificateChecks.KernelSpor.F3149.mgM 4

namespace CertificateChecks.KernelSpor.F3149

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.HexAt CFSG.KS.Text

@[expose] noncomputable def G (k : Nat) : Nat := pg 12 (mask 12) (SO (Nat.div k 54)) (Nat.mod k 54)

@[expose] noncomputable def D (i : Nat) : Nat := pg 4 (mask 4) (MG (Nat.div i 56)) (Nat.mod i 56)

@[expose] noncomputable def D3 (i : Nat) : Nat :=
  ((0 * 16 + D i) * 16 + D (i + 1)) * 16 + D (i + 2)

@[expose] noncomputable def mgOK (j : Nat) : Bool :=
  bAnd(Nat.blt (0 * 16 + D (7 * j)) 2, bAnd(Nat.blt (D3 (7 * j + 1)) 3510, Nat.blt (D3 (7 * j + 4)) 3510))

theorem asciiSO : asciiK SOC = true := by quickRfl
theorem asciiMG : asciiK MGC = true := by quickRfl
theorem lenSO : Nat.beq SOC.length 10530 = true := by quickRfl
theorem lenMG : Nat.beq MGC.length 49112 = true := by quickRfl
theorem bindSO : hexAtK SOC 0 3 54 12 65 SO = true := by quickRfl
theorem bindMG : hexAtK MGC 0 1 56 4 877 MG = true := by quickRfl
theorem ptsLt : allN 3510 (fun k => Nat.blt (G k) 3510) = true := by quickRfl
theorem inc1 : allN 2815 (fun k => Nat.blt (G (1 + k)) (G (1 + k + 1))) = true := by quickRfl
theorem inc2 : allN 692 (fun k => Nat.blt (G (2817 + k)) (G (2817 + k + 1))) = true := by quickRfl
theorem merges : allN 7016 mgOK = true := by quickRfl

theorem neg : bAnd(bIf(Nat.blt (G 1) (G 0), false, true),
    bIf(allN 7016 (fun j => Nat.blt (0 * 16 + D (7 * j)) 1), false, true)) = true := by
  quickRfl

end CertificateChecks.KernelSpor.F3149

end
