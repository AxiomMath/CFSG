module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census219.M24TcData

public section

namespace CertificateChecks.KernelTc.M24

open CFSG.AGLEmbeddingD2.Wilson.Census219

@[expose] def keys : Array Nat := (List.range 24).toArray

@[expose] def keys6 : Array Nat := (List.range 6).toArray

@[expose] def gQ : Array (Array Nat) := m24TcD.gQ

@[expose] def gK : Array (Array Nat) := m24TcD.gK

@[expose] def sig : Array (Array Nat) := m24TcD.sig

@[expose] def misc : Array (Array Nat) := m24TcD.cu ++ m24TcD.cv ++ m24TcD.reps ++ #[m24xA]

end CertificateChecks.KernelTc.M24

end
