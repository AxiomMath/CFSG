module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanE6TwoSylowData

public section

open CFSG.AGLEmbedding.E6Two

namespace Certificates.Kernel.ONanE6Two

set_option maxRecDepth 100000 in
theorem e6SylowCheck_k9616 : e6SylowCheck e6SylowData = true := by decide +kernel

end Certificates.Kernel.ONanE6Two
