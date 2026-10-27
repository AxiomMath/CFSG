module

public import Certificates.Kernel.Co1B.Tri2045
public import CFSG.Certificates.Kernel.LocalCompCo1EndSound
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo1EndTests
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo1EndData
public meta import Certificates.Kernel.SporSch.Co1.GenDag
public meta import Certificates.Kernel.LocalComp.Co1EndIn
import CFSG.Certificates.Kernel.Common.Harness
public meta import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo1Cen2BData
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo1Cen2BData

public section

set_option maxRecDepth 400000

#kss_co1dag CertificateChecks.KernelLC.Co1End.E CertificateChecks.KernelLC.Co1End.endDag

namespace CertificateChecks.KernelLC.Co1End

open CFSG.KS.Raw CFSG.KS.SporSch.M24 CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1Block
open CFSG.ComponentClassification.RankTwoSporadic.Co1 CertificateChecks.KernelSporSch.Co1Packed
open CFSG.KC.Co1End

@[expose] noncomputable def PX : Nat := CertificateChecks.KernelCo1B.Cent2045.D2.M 19

@[expose] noncomputable def PY : Nat := CertificateChecks.KernelCo1B.Cent2045.D2.M 21

theorem kB : (Nat.beq (E.M 0) PA && Nat.beq (E.M 1) PB && Nat.beq (E.M 2) PX &&
    Nat.beq (E.M 3) PY) = true := by quickRfl

theorem rx : twoBXYRows.1 = unpack 24 24 PX := CertificateChecks.KernelCo1B.Tri2045.rx_eq

theorem ry : twoBXYRows.2 = unpack 24 24 PY := CertificateChecks.KernelCo1B.Tri2045.ry_eq

theorem kD : dagK E.M E.MI 4 E.N co1EndD = true := by quickRfl

theorem kE : elemK PA PX PY (E.M 4) (E.M 12) (E.M 16) (E.M 27) (E.MI 27) (E.M 36) (E.MI 36)
    co1EndDB = true := by quickRfl

theorem hN : E.N = 37 := rfl

theorem base_eq : co1EndBase = (List.range 4).map fun i => unpack 24 24 (E.M i) := by
  have h := kB
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := h
  unfold co1EndBase
  rw [aR_u, bR_u, rx, ry, ← Nat.eq_of_beq_eq_true h0,
    ← Nat.eq_of_beq_eq_true h1, ← Nat.eq_of_beq_eq_true h2, ← Nat.eq_of_beq_eq_true h3]
  rfl

theorem dag_eq : dag co1EndBase (co1EndD.map decWord) =
    ((List.range E.N).map fun i => unpack 24 24 (E.M i),
      (List.range E.N).map fun i => unpack 24 24 (E.MI i), true) :=
  dagK_sound base_eq kD

theorem kI27 : invOKK (E.M 27) (E.MI 27) = true := by quickRfl

theorem kI36 : invOKK (E.M 36) (E.MI 36) = true := by quickRfl

theorem ent {k : Nat} (hk : k - 1 < E.N) :
    entryR ((List.range E.N).map fun i => unpack 24 24 (E.M i)) k = unpack 24 24 (E.M (k - 1)) :=
  CertificateChecks.KernelCo1B.Tri2045.rows_getD hk

theorem check : co1EndCheck co1EndD co1EndIdx co1EndDB = true := by
  unfold co1EndCheck co1EndCoreOK
  rw [dag_eq, Bool.true_and]
  simp only [co1EndIdx, List.getD_cons_zero, List.getD_cons_succ]
  rw [ent (k := 5) (by rw [hN]; decide), ent (k := 13) (by rw [hN]; decide),
    ent (k := 17) (by rw [hN]; decide), ent (k := 28) (by rw [hN]; decide),
    ent (k := 37) (by rw [hN]; decide),
    elemOK_eq co1EndDB aR_u rx ry (invOKK_sound kI27).2 (invOKK_sound kI36).2]
  exact kE

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.RankTwoSporadic
  CFSG.ComponentClassification.RankTwoSporadic.Co1 in
open Certificates in
theorem cert15049 : co1EndCheck co1EndD co1EndIdx co1EndDB = true := check

end CertificateChecks.KernelLC.Co1End

end
