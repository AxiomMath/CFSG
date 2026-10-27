module

public import Certificates.Kernel.LyBenes.Data
public import CFSG.Sporadic.Recognition.LyonsFinalCore107
public import CFSG.Sporadic.Recognition.LyonsFinalModularInputs
public import CFSG.Sporadic.Recognition.LyonsFinalDist2Inputs

public section

namespace CertificateChecks.KernelLyB

open CFSG.KC.LyBenes CFSG.Sporadic.Recognition.LyonsSims.LyFinal

@[expose] noncomputable def famChunk (j : Nat) : Bool :=
  (((Rcore107 ++ modularLearned).drop (16 * j)).take 16).all fun r => !isBWord r || bNetOK NS r

@[expose] noncomputable def stepOK (s : Dist2Step) : Bool :=
  match s.kind with
  | .B => bNetOK NS (parseWord s.old ++ derivInv (parseWord s.new))
  | _ => true

@[expose] noncomputable def stepsAt (i : Nat) : List Dist2Step :=
  (dist2Derivs.getD i ⟨"", []⟩).steps

@[expose] noncomputable def stepChunk (i j : Nat) : Bool :=
  (((stepsAt i).drop (40 * j)).take 40).all stepOK

@[expose] noncomputable def invWordsOK : Bool :=
  ([(0 : Fin 6), 2, 3, 4].map fun i => [(i, true), (i, true)]).all (bNetOK NS)

end CertificateChecks.KernelLyB

end
