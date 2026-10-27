module

public import Certificates.Kernel.LyBenes.Data

public section

namespace CertificateChecks.KernelLyB

open CFSG.KC.LyBenes CFSG.Sporadic.Recognition.LyonsSims.LyFinal

@[expose] noncomputable def rbChunkOf (Ns : Nat → Nat) (L : List (List (Fin 6 × Bool))) (j : Nat) :
    Bool :=
  ((L.drop (8 * j)).take 8).all (bNetOK Ns)

@[expose] noncomputable def rbChunk (j : Nat) : Bool := rbChunkOf NS RB j

end CertificateChecks.KernelLyB

end
