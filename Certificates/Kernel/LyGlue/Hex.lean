module

public import CFSG.Sporadic.Recognition.LyonsModelData
public import Certificates.Kernel.B3S3.HexGen
public import CFSG.Certificates.Kernel.Common.StrLitChunks
public import Certificates.Data.Kernel.Spor.Chain
public import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public meta import CFSG.Sporadic.Recognition.LyonsModelData

set_option maxRecDepth 400000

public section

#str_lit_chunks CertificateChecks.KernelLy.CH CFSG.Sporadic.Recognition.LyonsSims.Ly0.cTabHex
  4000 400000 2048
#kb3_hexarrs CertificateChecks.KernelLy.CH CFSG.Sporadic.Recognition.LyonsSims.Ly0.cTabHex 5 4455 17

#str_lit_chunks CertificateChecks.KernelLy.DH CFSG.Sporadic.Recognition.LyonsSims.Ly0.dTabHex
  4000 400000 2048
#kb3_hexarrs CertificateChecks.KernelLy.DH CFSG.Sporadic.Recognition.LyonsSims.Ly0.dTabHex 5 4455 17

#kc_select CertificateChecks.KernelLy CS CH.F.L 15
#kc_select CertificateChecks.KernelLy DS DH.F.L 15

namespace CertificateChecks.KernelLy

@[expose] noncomputable def hexCK (cs : List Char) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun c _ ih => (Nat.blt (Char.toNat c) 58 && Nat.ble 48 (Char.toNat c) ||
      Nat.blt (Char.toNat c) 103 && Nat.ble 97 (Char.toNat c)) && ih) cs

theorem cHex : hexCK CH.chars = true := by decide +kernel

theorem dHex : hexCK DH.chars = true := by decide +kernel

@[expose] noncomputable def cL (a : Nat) : Nat :=
  CFSG.KC.Enum.pg 17 (CFSG.KS.mask 17) (CS (Nat.div a 4455)) (Nat.mod a 4455)

@[expose] noncomputable def dL (a : Nat) : Nat :=
  CFSG.KC.Enum.pg 17 (CFSG.KS.mask 17) (DS (Nat.div a 4455)) (Nat.mod a 4455)

theorem cN : CH.N = 15 := by decide +kernel

theorem dN : DH.N = 15 := by decide +kernel

theorem cS_eq {k : Nat} (hk : k < 15) : CS k = CH.F k := by
  interval_cases k <;> rfl

theorem dS_eq {k : Nat} (hk : k < 15) : DS k = DH.F k := by
  interval_cases k <;> rfl

end CertificateChecks.KernelLy

end
