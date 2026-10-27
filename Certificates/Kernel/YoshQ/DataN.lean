module

public import Certificates.Data.Kernel.YoshQ.Replay
public meta import Certificates.Kernel.YoshQ.Gen
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Certificates.Kernel.Common.Eval

public section

#kc_eval CertificateChecks.KernelYoshQ N00 CertificateChecks.KernelYoshQ.stepN 0 0
#kc_eval CertificateChecks.KernelYoshQ N01 CertificateChecks.KernelYoshQ.stepN 0 1
#kc_eval CertificateChecks.KernelYoshQ N10 CertificateChecks.KernelYoshQ.stepN 1 0
#kc_eval CertificateChecks.KernelYoshQ N11 CertificateChecks.KernelYoshQ.stepN 1 1

end
