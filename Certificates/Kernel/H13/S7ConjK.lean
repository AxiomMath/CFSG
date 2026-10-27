module

public import CFSG.Quasithin.H13.L32NS7ConjInputs
public import Certificates.Data.Kernel.Mat8P
public import Certificates.Kernel.H13.Data
public import Certificates.Kernel.H13.DataReps
public import CFSG.Certificates.Kernel.Common.Each

public section

namespace CertificateChecks.KernelH13

open CFSG.Quasithin.H13.Mat8Cert CFSG.Quasithin.H13.S7Conj CFSG.KC.Mat8P

@[expose] def powBP : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, acc => acc
  | fuel + 1, base, n, acc =>
    powBP fuel (mulP base base) (n / 2) (if n % 2 = 1 then mulP acc base else acc)

@[expose] def invP (p : ℕ) : ℕ := powBP 10 p 839 oneP

@[expose] noncomputable def conjBP (m mi : ℕ) (h : List ℕ) : Bool :=
  mulP m mi == oneP && memP (ofListP D.s7L) (mulP (mulP m (code64R c7)) mi) &&
    memP (ofListP D.s7L) (mulP (mulP m (code64R h)) mi)

@[expose] noncomputable def hBF (h : List ℕ) : Bool :=
  (elemsF [c7, h] 5041).all validB && nodupP ((elemsF [c7, h] 5041).map code64R) &&
    memLR (ofListLR (elemsF [c7, h] 5041)) one8 && [c7, h].all validB &&
    (if (elemsF [c7, h] 5041).length ≤ 5040 then
      ((elemsF [c7, h] 5041).all fun x => [c7, h].all fun g =>
          memLR (ofListLR (elemsF [c7, h] 5041)) (mul8F g x)) &&
        ((elemsF [c7, h] 5041).length != 5040 || D.s8L.any fun m => conjBP m (invP m) h)
    else true)

@[expose] noncomputable def hBk (k : ℕ) : Bool := ((D.repsL.drop (k * 1)).take 1).all fun r => hBF (unpackM r)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
#kc_each hBk 0 28

end CertificateChecks.KernelH13

end
