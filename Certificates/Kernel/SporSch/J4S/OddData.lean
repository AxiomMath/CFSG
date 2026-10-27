
module

public import CFSG.Sporadic.Schreier.J4SOddData

public section

namespace CertificateChecks.KernelSporSch.J4Odd

open CFSG.Sporadic.J4Schreier

@[expose] def certPairs : Array Pair := certList.toArray

@[expose] def eRowsA : Array Pair := #[(eRows, tInvRows)]

@[expose] def csA : Array Pair := #[(certSum certList, certSum certList)]

end CertificateChecks.KernelSporSch.J4Odd

end
