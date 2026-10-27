module

public import Certificates.Kernel.SporSch.J1.Levels
public import Certificates.Kernel.SporSch.J1.GenCent
public meta import Certificates.Kernel.SporSch.J1.Chain
public meta import CFSG.Sporadic.Schreier.J1CentData
import CFSG.Certificates.Kernel.Common.Harness
public meta import CFSG.Sporadic.Schreier.J1CountCheck
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreCentral
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreWords

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.J1

open CFSG.KS.SporSch.MOCG

meta def wordA (L : Int → Array Nat) (wd : List Int) : Array Nat :=
  wd.foldr (fun l acc => comp (L l) acc) (idA 3080)

meta def aL (l : Int) : Array Nat :=
  if l = 1 then strongM[0]! else if l = -1 then invA strongM[0]! else if l = 2 then strongM[1]!
  else invA strongM[1]!

meta def cM (i : Nat) : Array Nat := wordA aL (CFSG.Sporadic.Schreier.j1CWords.getD i [])

meta def cL (l : Int) : Array Nat :=
  if 0 < l then cM (l.toNat - 1) else invA (cM ((-l).toNat - 1))

meta def dM (j : Nat) : Array Nat := wordA cL (CFSG.Sporadic.Schreier.j1DWords.getD j [])

meta def c0M : Array Nat := cM 0
meta def c1M : Array Nat := cM 1
meta def c2M : Array Nat := cM 2
meta def c3M : Array Nat := cM 3
meta def ci0M : Array Nat := invA (cM 0)
meta def ci1M : Array Nat := invA (cM 1)
meta def ci2M : Array Nat := invA (cM 2)
meta def ci3M : Array Nat := invA (cM 3)
meta def d0M : Array Nat := dM 0
meta def d1M : Array Nat := dM 1
meta def d2M : Array Nat := dM 2

meta def dGM : Array (Array Nat) := #[dM 0, dM 1, dM 2]

end CertificateChecks.KernelSporSch.J1

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch.J1C CertificateChecks.KernelSporSch

#kss_packeq CertificateChecks.KernelSporSch.J1W.C0 12 CertificateChecks.KernelSporSch.J1.c0M
  (wordP 3080 12 (mask 12) (pidn 3080 12) (ltrK J1L.S J1L.SI)
    (CFSG.Sporadic.Schreier.j1CWords.getD 0 []))
#kss_packeq CertificateChecks.KernelSporSch.J1W.C1 12 CertificateChecks.KernelSporSch.J1.c1M
  (wordP 3080 12 (mask 12) (pidn 3080 12) (ltrK J1L.S J1L.SI)
    (CFSG.Sporadic.Schreier.j1CWords.getD 1 []))
#kss_packeq CertificateChecks.KernelSporSch.J1W.C2 12 CertificateChecks.KernelSporSch.J1.c2M
  (wordP 3080 12 (mask 12) (pidn 3080 12) (ltrK J1L.S J1L.SI)
    (CFSG.Sporadic.Schreier.j1CWords.getD 2 []))
#kss_packeq CertificateChecks.KernelSporSch.J1W.C3 12 CertificateChecks.KernelSporSch.J1.c3M
  (wordP 3080 12 (mask 12) (pidn 3080 12) (ltrK J1L.S J1L.SI)
    (CFSG.Sporadic.Schreier.j1CWords.getD 3 []))
#kss_packeq CertificateChecks.KernelSporSch.J1W.CI0 12 CertificateChecks.KernelSporSch.J1.ci0M
  (pinvS 3080 12 (mask 12) J1W.C0)
#kss_packeq CertificateChecks.KernelSporSch.J1W.CI1 12 CertificateChecks.KernelSporSch.J1.ci1M
  (pinvS 3080 12 (mask 12) J1W.C1)
#kss_packeq CertificateChecks.KernelSporSch.J1W.CI2 12 CertificateChecks.KernelSporSch.J1.ci2M
  (pinvS 3080 12 (mask 12) J1W.C2)
#kss_packeq CertificateChecks.KernelSporSch.J1W.CI3 12 CertificateChecks.KernelSporSch.J1.ci3M
  (pinvS 3080 12 (mask 12) J1W.C3)

namespace CertificateChecks.KernelSporSch.J1W

@[expose] noncomputable def C (i : Nat) : Nat := [C0, C1, C2, C3].getD i 0

@[expose] noncomputable def CI (i : Nat) : Nat := [CI0, CI1, CI2, CI3].getD i 0

theorem permC : allN 4 (fun i => permOK 3080 12 (mask 12) (3080 * 12) (C i) (CI i)) = true := by
  quickRfl

end CertificateChecks.KernelSporSch.J1W

#kss_packeq CertificateChecks.KernelSporSch.J1W.D0 12 CertificateChecks.KernelSporSch.J1.d0M
  (wordP 3080 12 (mask 12) (pidn 3080 12) (ltrK J1W.C J1W.CI)
    (CFSG.Sporadic.Schreier.j1DWords.getD 0 []))
#kss_packeq CertificateChecks.KernelSporSch.J1W.D1 12 CertificateChecks.KernelSporSch.J1.d1M
  (wordP 3080 12 (mask 12) (pidn 3080 12) (ltrK J1W.C J1W.CI)
    (CFSG.Sporadic.Schreier.j1DWords.getD 1 []))
#kss_packeq CertificateChecks.KernelSporSch.J1W.D2 12 CertificateChecks.KernelSporSch.J1.d2M
  (wordP 3080 12 (mask 12) (pidn 3080 12) (ltrK J1W.C J1W.CI)
    (CFSG.Sporadic.Schreier.j1DWords.getD 2 []))

namespace CertificateChecks.KernelSporSch.J1W

@[expose] noncomputable def D (j : Nat) : Nat := [D0, D1, D2].getD j 0

theorem ncommD : (!(allN 3080 (fun x => Nat.beq (pg 12 (mask 12) (pcomp 3080 12 (mask 12) (D 0)
    (D 2)) x) (pg 12 (mask 12) (pcomp 3080 12 (mask 12) (D 2) (D 0)) x)))) = true := by
  quickRfl

theorem commD : allN 3 (fun j => Nat.beq (pcomp 3080 12 (mask 12) (D j) (J1L.S 0))
    (pcomp 3080 12 (mask 12) (J1L.S 0) (D j))) = true := by
  quickRfl

end CertificateChecks.KernelSporSch.J1W

end
