
module

public import CFSG.Sporadic.Schreier.J4SSylowData
public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.SporSch.J4S.XY
public import CFSG.Certificates.Kernel.SporSch.J4STokSound
public import CFSG.Certificates.Kernel.SporSch.J4STextSound
meta import CFSG.Sporadic.Schreier.J4SSylowData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSporSch.J4E CFSG.Sporadic.J4Schreier.elementsText
#kss_tokens CertificateChecks.KernelSporSch.J4E CFSG.Sporadic.J4Schreier.elementsText
#kss_tree CertificateChecks.KernelSporSch.J4E.T CFSG.Sporadic.J4Schreier.elementColumns 11
#kss_sort CertificateChecks.KernelSporSch.J4ES CFSG.Sporadic.J4Schreier.elementColumns 11

#ks_chars CertificateChecks.KernelSporSch.J4D CFSG.Sporadic.J4Schreier.parentsText
#kss_tokens CertificateChecks.KernelSporSch.J4D CFSG.Sporadic.J4Schreier.parentsText
#kss_tree CertificateChecks.KernelSporSch.J4D.T CFSG.Sporadic.J4Schreier.discoveryParents 10

#ks_chars CertificateChecks.KernelSporSch.J4R CFSG.Sporadic.J4Schreier.edgesText
#kss_tokens CertificateChecks.KernelSporSch.J4R CFSG.Sporadic.J4Schreier.edgesText
#kss_tree CertificateChecks.KernelSporSch.J4R.T CFSG.Sporadic.J4Schreier.rightEdges 10

#ks_chars CertificateChecks.KernelSporSch.J4CT CFSG.Sporadic.J4Schreier.cTableText
#kss_tokens CertificateChecks.KernelSporSch.J4CT CFSG.Sporadic.J4Schreier.cTableText
#kss_vec CertificateChecks.KernelSporSch.J4CT.T CFSG.Sporadic.J4Schreier.cTable

#ks_chars CertificateChecks.KernelSporSch.J4SQ CFSG.Sporadic.J4Schreier.squaresText
#kss_tokens CertificateChecks.KernelSporSch.J4SQ CFSG.Sporadic.J4Schreier.squaresText
#kss_vec CertificateChecks.KernelSporSch.J4SQ.T CFSG.Sporadic.J4Schreier.squares

#kss_table CertificateChecks.KernelSporSch.J4GC CFSG.Sporadic.J4Schreier.generatorColumns 11 11

namespace CertificateChecks.KernelSporSch.J4Five

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch.C11
open CFSG.Sporadic.J4Schreier CFSG.Sporadic.Schreier.PairText
open CertificateChecks.KernelSporSch

@[expose] def J4NB : Nat := 1321269383840139985276097490840631300

theorem nb : bindWK 11 11 normalOrbitSpanBasis.toArray.toList J4NB = true := by quickRfl

theorem pE : permsK 11 11 1024 J4E.toks J4E.T = true := by quickRfl
theorem pD : permsK 10 2 1024 J4D.toks J4D.T = true := by quickRfl
theorem pR : permsK 10 4 1024 J4R.toks J4R.T = true := by quickRfl
theorem pCT : permsK 10 1 1024 J4CT.toks J4CT.T = true := by quickRfl
theorem pSQ : permsK 10 1 1024 J4SQ.toks J4SQ.T = true := by quickRfl

theorem E_size : elementColumns.size = 1024 := by
  rw [elementColumns, J4E.eq, CFSG.KS.SporSch.tokK_sound J4E.tok]
  exact (permsK_sound pE).1

theorem E_eq {e : Nat} (he : e < 1024) : elementColumns[e]! = unpack11 (J4E.T e) := by
  rw [elementColumns, J4E.eq, CFSG.KS.SporSch.tokK_sound J4E.tok]
  exact (permsK_sound pE).2 e he

theorem D_get {e i : Nat} (he : e < 1024) (hi : i < 2) :
    (discoveryParents[e]!)[i]! = ent 10 (J4D.T e) i := by
  rw [discoveryParents, J4D.eq, CFSG.KS.SporSch.tokK_sound J4D.tok, (permsK_sound pD).2 e he,
    unpackW_get hi]

theorem R_get {e i : Nat} (he : e < 1024) (hi : i < 4) :
    (rightEdges[e]!)[i]! = ent 10 (J4R.T e) i := by
  rw [rightEdges, J4R.eq, CFSG.KS.SporSch.tokK_sound J4R.tok, (permsK_sound pR).2 e he,
    unpackW_get hi]

theorem CT_eq : cTable = tabA 1024 J4CT.T := by
  rw [cTable, J4CT.eq, CFSG.KS.SporSch.tokK_sound J4CT.tok]
  exact natsK_sound pCT

theorem SQ_eq : squares = tabA 1024 J4SQ.T := by
  rw [squares, J4SQ.eq, CFSG.KS.SporSch.tokK_sound J4SQ.tok]
  exact natsK_sound pSQ

theorem GC_eq {i : Nat} (hi : i < 4) : generatorColumns[i]! = unpack11 (J4GC i) :=
  (bind2_sound J4GC.bind).2 i hi

theorem NB_get {j : Nat} (hj : j < 11) : normalOrbitSpanBasis.toArray[j]! = ent 11 J4NB j := by
  rw [bindW_sound nb, unpackW_get hj]

end CertificateChecks.KernelSporSch.J4Five

end
