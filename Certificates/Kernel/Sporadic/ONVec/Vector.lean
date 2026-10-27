module

public import Certificates.Kernel.Sporadic.ONVec.Cert
public import Certificates.Kernel.Sporadic.ONVec.Final

public section

namespace CertificateChecks.KernelSpor.ONVec

theorem vector_cert_proved : CFSG.ONSchreier.Native.vectorCert
    (CFSG.ONSchreier.Native.digitsW CFSG.ONSchreier.Data.rootDigits) CFSG.ONSchreier.Data.spanIdx
    (CFSG.F3.Native.rowsOf 154 CFSG.ONSchreier.Data.spanInvPayload)
    (CFSG.F3.Native.rowsOf 154 CFSG.ONSchreier.Data.formPayload) CFSG.ONSchreier.Data.baseList
    CFSG.ONSchreier.Data.strongWords 3 = true :=
  vector_cert_ok sigAll ssortAll

end CertificateChecks.KernelSpor.ONVec

end
