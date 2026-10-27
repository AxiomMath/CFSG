module

public import Certificates.Data.Kernel.Misc.MergeT
public import Certificates.Kernel.Misc.Tits.Flags8076

set_option maxRecDepth 400000
set_option Elab.async false

public section

namespace CertificateChecks.KernelMisc.Tits8076

open CFSG.KC.Enum CFSG.KC.MergeT CFSG.Quasithin CFSG.Certificates
open CFSG.KS (mask)

@[expose] noncomputable def FL (i : Nat) : Nat := CFSG.KS.Mathieu.nget TitsFL i

@[expose] noncomputable def SL (i : Nat) : Nat := CFSG.KS.Mathieu.nget TitsSL i

@[expose] noncomputable def mOK (j : Nat) : Bool :=
  mergeTK 8775 14 FL 13 0 titsOverReps[j + 3]! (mergeVals (titsOverMerge j)) [1, 2]

theorem m0 : mOK 0 = true := by decide +kernel
theorem m1 : mOK 1 = true := by decide +kernel
theorem m2 : mOK 2 = true := by decide +kernel
theorem m3 : mOK 3 = true := by decide +kernel
theorem m4 : mOK 4 = true := by decide +kernel
theorem m5 : mOK 5 = true := by decide +kernel
theorem m6 : mOK 6 = true := by decide +kernel
theorem m7 : mOK 7 = true := by decide +kernel
theorem m8 : mOK 8 = true := by decide +kernel
theorem m9 : mOK 9 = true := by decide +kernel
theorem m10 : mOK 10 = true := by decide +kernel
theorem m11 : mOK 11 = true := by decide +kernel
theorem m12 : mOK 12 = true := by decide +kernel
theorem m13 : mOK 13 = true := by decide +kernel
theorem m14 : mOK 14 = true := by decide +kernel

theorem moved : allN 17 (fun c => (List.range 3).any fun i =>
    Bool.rec (motive := fun _ => Bool) true false
      (Nat.beq (pg 14 (mask 14) (SL i) titsOverReps[c + 1]!) titsOverReps[c + 1]!)) = true := by
  decide +kernel

end CertificateChecks.KernelMisc.Tits8076

end
