module

public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutCentralizerData
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAut

public section

namespace CertificateChecks.KernelLC.M12Cent

open CFSG.Sporadic.Schreier CFSG.ComponentClassification.M12Cover

@[expose] def q2Words : List (List ℤ) := [[2, -3, -3], [4, 2, 1], [3, 3, 2, -3], [5, -2, 5, 4, 2]]

@[expose] def q4Words : List (List ℤ) := [[3, 1, -2, 1], [-1, 3, 2], [-1, 3, 1, 1, 2]]

@[expose] def q5Words : List (List ℤ) := [[3, 1, -3, 1], [-3, 2, 1, 3]]

@[expose] def k1Words : List (List ℤ) := [[-2, 4], [-3, -3], [-2, 4, 1], [-3, 4, -2]]

@[expose] def k3Words : List (List ℤ) := [[-2, -3], [-3, 1]]

@[expose] def q2RWords : List (List ℤ) :=
  [[-2, 4], [-3, -3], [-2, 5], [-2, 4, 5], [2, 3, 5], [4, 5, -3]]

@[expose] def q4RWords : List (List ℤ) := [[2, 3], [1, -3, 4], [1, 3, 4]]

@[expose] def q4GWords : List (List ℤ) :=
  m12CentWords2.map fun w => gzWord ++ w ++ invCodes gzWord

end CertificateChecks.KernelLC.M12Cent

end
