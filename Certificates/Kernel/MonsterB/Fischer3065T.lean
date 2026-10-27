
module

public import Certificates.Kernel.MonsterB.Fischer3067T

public section

namespace CertificateChecks.KernelMonB.F3065

open CFSG.Monster.B.TwoA.Fischer CFSG.Monster.B.TwoA.Fischer.Cert CFSG.Sporadic.SmallF2.Native
  CFSG.KC.FischerK CFSG.KC.FischerE CFSG.KLie.CT CertificateChecks.KernelMonB.IndCand
  CertificateChecks.KernelMonB.F3067

@[expose] noncomputable def ncL (i : ℕ) : ℕ := GramLit.ncRows.toArray[i]!

@[expose] noncomputable def suppT (w : List ℕ) (N : ℕ) : Bool :=
  decide (N < 2 ^ 3510) && allN 3510 fun q => (labF w q != q) == bit N q

@[expose] noncomputable def colN (L : List ℕ) (y : ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0
    (fun r _ ih => Nat.lor (Nat.land (Nat.shiftRight r y) 1) (Nat.shiftLeft ih 1)) L

@[expose] noncomputable def gramRowT (i : ℕ) : Bool :=
  (labelWord i).all (· < 13) && wordL candF (labelWord i) 22 == basisPt i &&
    suppT (labelWord i) (ncL i) &&
    gramRow i == ofBits 78 (fun k => (ncL i).testBit (basisPt k))

end CertificateChecks.KernelMonB.F3065

end
