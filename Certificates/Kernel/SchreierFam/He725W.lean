module

public import Certificates.Kernel.Sporadic.IntWordsCmd
public import Certificates.Data.Insp443He
public meta import Certificates.Data.Insp443He

public section

namespace CertificateChecks.KernelSchreierFam.He725

open CFSG.SectionRank.QTK.Insp443.He CFSG.Quasithin.KGC31.He

meta def genM : Array (List Int) := l7GenW.toArray

meta def derM : Array (List Int) := l7Der.toArray

meta def qM : Array (List Int) := qW.toArray

meta def cM : Array (List Int) := #[c7W]

end CertificateChecks.KernelSchreierFam.He725

#kc_intwords CertificateChecks.KernelSchreierFam.He725.gL CertificateChecks.KernelSchreierFam.He725.genM
#kc_intwords CertificateChecks.KernelSchreierFam.He725.dL CertificateChecks.KernelSchreierFam.He725.derM
#kc_intwords CertificateChecks.KernelSchreierFam.He725.qL CertificateChecks.KernelSchreierFam.He725.qM
#kc_intwords CertificateChecks.KernelSchreierFam.He725.cL CertificateChecks.KernelSchreierFam.He725.cM

end
