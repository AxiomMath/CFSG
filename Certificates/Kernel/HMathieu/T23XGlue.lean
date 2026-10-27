
module

public import Certificates.Kernel.HMathieu.T23X
public import Certificates.Kernel.HMathieu.T23Glue

public section

namespace CertificateChecks.KernelHMathieu.T23X

open CFSG.KC.HMathieu CFSG.Quasithin.H.Mathieu CertificateChecks.KernelHMathieu

theorem gtabs : GTabs inv23s2 (cmD rows) (mkD rows) :=
  gtabs_of T23.packed T23.invData (by rw [T23.lenOK]; exact tabs)

end CertificateChecks.KernelHMathieu.T23X

end
