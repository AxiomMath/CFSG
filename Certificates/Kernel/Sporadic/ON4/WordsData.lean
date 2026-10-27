module

public import Certificates.Kernel.Sporadic.ON2.GenWords
public meta import CFSG.Sporadic.Schreier.ONOuterData
public meta import Mathlib.Init

public section

namespace CertificateChecks.KernelSpor.ON4

open CFSG.ONSchreier

meta def wordsM : Array (List Int) :=
  let ws : Array (List Int) := #[Data.McommChain.strongWords[3]!, Data.McommChain.strongWords[4]!,
    Data.LcommChain.strongWords[3]!, Data.LcommChain.strongWords[4]!,
    Data.LcommChain.strongWords[5]!, Data.jointChain.strongWords[6]!,
    Data.jointChain.strongWords[7]!, Data.jointChain.strongWords[8]!]
  ws ++ ws.map fun w => w.reverse.map fun l => -l

end CertificateChecks.KernelSpor.ON4

#kon_words CertificateChecks.KernelSpor.ON4W CertificateChecks.KernelSpor.ON4.wordsM
