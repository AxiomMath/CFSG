module

public import Certificates.Kernel.LyGlue.TabData

public section

namespace CertificateChecks.KernelLy

open CFSG.Sporadic.Recognition.LyonsSims CFSG.Sporadic.Recognition CFSG.KC.LyGlue

@[expose] def cdE (w : List Int) : List Nat := w.flatMap cdIdx

@[expose] def uE (w : List Int) : List Nat :=
  w.flatMap fun l => if l = 1 then [1] else cdE (Ly0.uWords.getD (l.toNat - 1) [])

@[expose] def wE : List Nat := cdE Ly0.wordConj ++ (uE yU ++ uE yU) ++
  cdE (McLMultiplier.invW Ly0.wordConj)

@[expose] def expect : List (List Nat) :=
  [cdE Ly0.wordU2, cdE Ly0.wordU3, cdE Ly0.wordU4, uE yU, uE xU, cdE Ly0.wordConj,
    cdE (McLMultiplier.invW Ly0.wordConj), uE yU ++ uE yU, wE, uE xU ++ uE xU, wE ++ wE,
    cdE (Glue.txWords.getD 0 []), cdE (Glue.txWords.getD 1 []), cdE (Glue.txWords.getD 2 []),
    cdE (Glue.txWords.getD 3 [])]

end CertificateChecks.KernelLy

end
