
module

public import CFSG.Quasithin.H13.J4ClassCheckInputs

public section

namespace CertificateChecks.KernelH13.J4ClsData

open CFSG.Quasithin.H13.J4 CFSG.Quasithin.H13.J4.Native

@[expose] def nextIdx (gens : Array (Array Nat × Array Nat)) (E : ClsEnum) : Array Nat :=
  let m := clsIdx E.1
  (E.1.toList.flatMap fun B => gens.toList.map fun g => m.getD (conjCols g.2 g.1 B) E.1.size).toArray

@[expose] def e2E : Array (Array Nat) := cls2.1
@[expose] def e2P : Array Nat := cls2.2.1
@[expose] def e2G : Array Nat := cls2.2.2
@[expose] def e2N : Array Nat := nextIdx xyPairs cls2
@[expose] def e3E : Array (Array Nat) := cls3.1
@[expose] def e3P : Array Nat := cls3.2.1
@[expose] def e3G : Array Nat := cls3.2.2
@[expose] def e3N : Array Nat := nextIdx xyPairs cls3

end CertificateChecks.KernelH13.J4ClsData

end
