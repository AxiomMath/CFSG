
module

public import CFSG.Quasithin.Background.HMathieuFacts24Inputs

public section

namespace CertificateChecks.KernelMathieuAut

open CFSG.Quasithin.H.Mathieu

set_option maxHeartbeats 40000000 in
theorem inv24ArrK :
    inAutOK inv24Arr = true ∧ (∀ i < 24, inv24Arr[inv24Arr[i]!]! = i) ∧
      inv24Arr[0]! ≠ 0 ∧ ((List.range (2 ^ 11)).filter fun m => act11 inv24Arr m == m).length =
        2 ^ 7 := by
  decide +kernel

end CertificateChecks.KernelMathieuAut

end
