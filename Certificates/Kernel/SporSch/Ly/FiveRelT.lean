module

public import Certificates.Kernel.SporSch.Ly.FiveRelData
public import Certificates.Kernel.SporSch.Ru.RowsGen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.LyFR

open CFSG.KC.Enum CFSG.KS CFSG.KC.LyFiveRel CertificateChecks.KernelSporSch.LyBS CFSG.KD.OrdLy
open CertificateChecks.KernelSporSch.LyFL (pw V)

theorem vp : allN 20 (fun u => Nat.beq (VP u) (pw (V (Nat.div u 5)) (Nat.mod u 5))) = true := by
  quickRfl

theorem xp : allN 5 (fun c => Nat.beq (XP c) (pw LyFL.D.XX c)) = true := by quickRfl

theorem pa : allN 25 (fun u => Nat.beq (PA u)
    (mul (VP (Nat.add 15 (Nat.div u 5))) (VP (Nat.add 10 (Nat.mod u 5))))) = true := by quickRfl

theorem pb : allN 125 (fun u => Nat.beq (PB u) (mul (PA (Nat.div u 5)) (VP (Nat.add 5 (Nat.mod u 5))))) =
    true := by quickRfl

theorem pc : allN 625 (fun u => Nat.beq (PC u) (mul (PB (Nat.div u 5)) (VP (Nat.mod u 5)))) = true := by
  quickRfl

@[expose] noncomputable def tBlk (g : Nat) : Bool :=
  allBlk (Nat.mul 64 g) (tAt mul LyFL.D.AA LyFL.D.BB ONE (LyFTP.F 0) (LyFTG.F 0) TT) 64

end CertificateChecks.KernelSporSch.LyFR

#kss_each CertificateChecks.KernelSporSch.LyFRT CertificateChecks.KernelSporSch.LyFR.tBlk 45

end
