module

public import Certificates.Kernel.SporSch.Ru.Text4060
public import Certificates.Kernel.SporSch.Ru.Text1920
public import Certificates.Kernel.SporSch.GenPerms
public import CFSG.Certificates.Kernel.SporSch.RuSound
meta import CFSG.Sporadic.Schreier.RuDefs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.RuLines

open CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2.Native

meta def inv4060M : Array (Array Nat) := (Array.range 45).map fun L => invCand 4060 (ruArr4060 L)

meta def inv1920M : Array (Array Nat) := (Array.range 41).map fun L => invCand 1920 (ruArr1920 L)

meta def inv80M : Array (Array Nat) := (Array.range 8).map fun L => invCand 80 (ruArr80 L)

end CertificateChecks.KernelSporSch.RuLines

#kss_perms CertificateChecks.KernelSporSch.RuLI4060 12 CertificateChecks.KernelSporSch.RuLines.inv4060M
#kss_perms CertificateChecks.KernelSporSch.RuLI1920 11 CertificateChecks.KernelSporSch.RuLines.inv1920M
#kss_perms CertificateChecks.KernelSporSch.RuLI80 7 CertificateChecks.KernelSporSch.RuLines.inv80M

namespace CertificateChecks.KernelSporSch.RuLines

open CFSG.KC.Enum CFSG.KS CertificateChecks.KernelSporSch

theorem perm4060a : allN 23 (fun j => permOK 4060 12 (mask 12) (4060 * 12) (RuT4060.L j)
    (RuLI4060 j)) = true := by quickRfl

theorem perm4060b : allN 22 (fun j => permOK 4060 12 (mask 12) (4060 * 12)
    (RuT4060.L (Nat.add 23 j)) (RuLI4060 (Nat.add 23 j))) = true := by quickRfl

theorem perm1920a : allN 41 (fun j => permOK 1920 11 (mask 11) (1920 * 11) (RuT1920.L j)
    (RuLI1920 j)) = true := by quickRfl

theorem perm80a : allN 8 (fun j => permOK 80 7 (mask 7) (80 * 7) (RuT80.L j) (RuLI80 j)) = true := by
  quickRfl

theorem perm4060 (j : Nat) (hj : j < 45) :
    permOK 4060 12 (mask 12) (4060 * 12) (RuT4060.L j) (RuLI4060 j) = true := by
  rcases Nat.lt_or_ge j 23 with h | h
  · exact allN_spec perm4060a j h
  · have := allN_spec perm4060b (j - 23) (by omega)
    rwa [show Nat.add 23 (j - 23) = j from Nat.add_sub_cancel' h] at this

theorem perm1920 (j : Nat) (hj : j < 41) :
    permOK 1920 11 (mask 11) (1920 * 11) (RuT1920.L j) (RuLI1920 j) = true := allN_spec perm1920a j hj

theorem perm80 (j : Nat) (hj : j < 8) :
    permOK 80 7 (mask 7) (80 * 7) (RuT80.L j) (RuLI80 j) = true := allN_spec perm80a j hj

end CertificateChecks.KernelSporSch.RuLines

end
