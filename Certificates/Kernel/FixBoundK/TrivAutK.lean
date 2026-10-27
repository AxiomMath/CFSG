module

public import Certificates.Data.Kernel.FixBoundK.TrivAut
public import Certificates.Kernel.FixBoundK.TrivData
public import Certificates.Kernel.MonsterB.Perm3018Data

public section

namespace CertificateChecks.KernelFixBoundK.TrivAutK

open CFSG.KC.FixBoundK CFSG.KC.FixBoundK.Triv CertificateChecks.KernelFixBoundK.TrivD

theorem code : codeK = true := by decide +kernel

theorem aut : autK CertificateChecks.Perm3018.GS CertificateChecks.Perm3018.GA = true := by
  decide +kernel

theorem repLen : lenS reps = 2 := by decide +kernel

noncomputable def idG : Nat := (List.range 24).foldr (fun j acc => acc * 32 + j) 0

noncomputable def swapG : Nat :=
  ([1, 0] ++ (List.range 22).map (· + 2)).foldr (fun j acc => acc * 32 + j) 0

theorem goodId : autG idG = true := by decide +kernel

theorem badDep : codeL (bmL.getD 1 0 :: bmL.tail) = false := by
  decide +kernel

theorem badNonCw : codeL (1 :: bmL.tail) = false := by decide +kernel

theorem badRepeat : permG (idG - 32) = false := by decide +kernel

theorem badSwap : autG swapG = false := by decide +kernel

end CertificateChecks.KernelFixBoundK.TrivAutK

end
