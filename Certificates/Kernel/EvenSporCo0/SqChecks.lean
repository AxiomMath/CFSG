module

public import Certificates.Kernel.EvenSporCo0.Data
public import Certificates.Data.Kernel.EvenSporCo0.SqSum

public section

namespace CertificateChecks.KernelCo0

open CFSG.KC.EvenSporCo0

theorem fix24514 : fixK S.G = true := by decide +kernel

theorem sqO24514 : sqOK S.T S.N 16777215 6528 = true := by decide +kernel

theorem sq8_24514 : sqOK S.T S.N 255 15232 = true := by decide +kernel

theorem sq8O24514 : sqOK S.T S.N 16776960 10368 = true := by decide +kernel

end CertificateChecks.KernelCo0

end
