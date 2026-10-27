module

public import Certificates.Kernel.HMathieu.Odd
public import Certificates.Data.Kernel.HMathieu.PickJ
public import CFSG.Quasithin.AppendixH.H15.H157Inputs

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelHMathieu.Odd

open CFSG.KC.HMathieu CFSG.Quasithin.H.Mathieu CFSG.ASVolI.AppH.H157

@[expose] noncomputable def okR490013 (a : Array Nat) : Bool := rankOK 11 8 (matOf 11 (act11 a))

@[expose] noncomputable def okA490013 (a : Array Nat) : Bool :=
  (conj3AStd.any fun h => conjToB h a tStd && inAutOK h) || okR490013 a

@[expose] noncomputable def tail490013 (ok : Array Nat → Bool) (E : List Nat) : Bool :=
  (E.drop 1).all fun e => ok (unpk e)

theorem c490013s3 : tail490013 okA490013 (E.getD 5 []) = true := by decide +kernel
theorem c490013s5 : tail490013 okR490013 (E.getD 6 []) = true := by decide +kernel
theorem c490013s7 : tail490013 okR490013 (E.getD 7 []) = true := by decide +kernel
theorem c490013s11 : tail490013 okR490013 (E.getD 8 []) = true := by decide +kernel
theorem c490013s23 : tail490013 okR490013 (E.getD 9 []) = true := by decide +kernel

end CertificateChecks.KernelHMathieu.Odd

end
