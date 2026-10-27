module

public import Certificates.Kernel.Sporadic.OddCore.J2FusK
public import Certificates.Kernel.Sporadic.OddCore.MulHGlue
public import Certificates.Kernel.Sporadic.OddCore.CentGlue
public import CFSG.Certificates.Kernel.Spor.PackWord
public import CFSG.Certificates.Kernel.BfsPinAlg

public section

namespace CertificateChecks.KernelSpor.J2Fus

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MulH CFSG.KC.BfsPin
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Schreier.Native CertificateChecks.KernelSpor
open CFSG.ComponentClassification.GSThmB.CF23I.J2

abbrev Cn (p : Nat) : Prop := canonK 315 9 (mask 9) (315 * 9) p = true

theorem hn : szOK 315 9 = true := by decide

theorem cId : Cn idK := (PP.id hn).1

theorem idT_eq : idT 315 = tabT (unpack 315 9 idK) := by
  rw [idT_tabT, idA_eq hn]
  rfl

theorem fF {k : Nat} (hk : k < 42) :
    Cn (J2CentT.F k) ∧ invEqK 315 9 (mask 9) (315 * 9) (J2CentT.F k) (J2CentI k) = true ∧
      Cn (J2CentI k) := by
  have hc := (bAnd_iff _ _).1 (allN_spec k_canon k hk)
  exact ⟨hc.1, allN_spec OddCore.j2_perms k hk, hc.2⟩

theorem tabF {k : Nat} (hk : k < 42) : j2CentTbl k = tabT (unpack 315 9 (J2CentT.F k)) := by
  rw [← OddCore.j2CentTbl_eq hk, tabT_natArr]

theorem permF {k : Nat} (hk : k < 42) : permOK 315 (j2CentTbl k) = true := by
  rw [tabF hk]
  exact permOK_unpack (fF hk).1 (fF hk).2.1

theorem c1_getD {l : Nat} (h1 : 1 ≤ l) (h5 : l ≤ 5) :
    j2C1Gens.getD (l - 1) (idT 315) = tabT (unpack 315 9 (L1 l)) ∧ Cn (L1 l) := by
  refine ⟨?_, (fF (k := l + 17) (by omega)).1⟩
  unfold L1
  rw [← tabF (by omega)]
  rcases (by omega : l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4 ∨ l = 5) with rfl | rfl | rfl | rfl | rfl <;>
    simp [j2C1Gens]

theorem c12_getD {l : Nat} (hl : l = 9 ∨ l = 5 ∨ l = 6) :
    (j2C1Gens ++ j2C2Gens).getD (l - 1) (idT 315) = tabT (unpack 315 9 (L12 l)) ∧ Cn (L12 l) := by
  rcases hl with rfl | rfl | rfl
  · refine ⟨?_, (fF (k := 35) (by norm_num)).1⟩
    rw [show L12 9 = J2CentT.F 35 by simp [L12], ← tabF (by norm_num)]
    simp [j2C1Gens, j2C2Gens]
  · refine ⟨?_, (fF (k := 22) (by norm_num)).1⟩
    rw [show L12 5 = J2CentT.F 22 by simp [L12], ← tabF (by norm_num)]
    simp [j2C1Gens, j2C2Gens]
  · refine ⟨?_, (fF (k := 32) (by norm_num)).1⟩
    rw [show L12 6 = J2CentT.F 32 by simp [L12], ← tabF (by norm_num)]
    simp [j2C1Gens, j2C2Gens]

theorem g1_eq : wordTbl 315 j2C1Gens [3, 2] = tabT (unpack 315 9 G1) ∧ Cn G1 :=
  wordTbl_unpack idT_eq cId fun l hl => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl <;> exact c1_getD (by norm_num) (by norm_num)

theorem g2_eq : wordTbl 315 j2C1Gens [2, 4, 2, 4] = tabT (unpack 315 9 G2) ∧ Cn G2 :=
  wordTbl_unpack idT_eq cId fun l hl => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl | rfl <;> exact c1_getD (by norm_num) (by norm_num)

theorem c0_eq : c0Tbl = tabT (unpack 315 9 C0) ∧ Cn C0 :=
  wordTbl_unpack idT_eq cId fun l hl => by
    apply c12_getD
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    omega

theorem ld1 : LD 1 = G1 := by simp [LD]

theorem ld2 : LD 2 = G2 := by simp [LD]

theorem d0_eq : d0Tbl = tabT (unpack 315 9 D0) ∧ Cn D0 :=
  wordTbl_unpack idT_eq cId fun l hl => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl
    · rw [ld1]
      simpa [j2DGens] using g1_eq
    · rw [ld2]
      simpa [j2DGens] using g2_eq
    · rw [ld2]
      simpa [j2DGens] using g2_eq

theorem j2FusOK_of : j2FusOK = true := by
  have hi := k_inv
  simp only [bAnd_iff] at hi
  have hci : Cn C0I := hi.2.2.2
  have hd := k_d0
  have c17 := fF (k := 17) (by norm_num)
  unfold j2FusOK
  simp only [Bool.and_eq_true, List.all_eq_true]
  refine ⟨⟨⟨⟨⟨?_, ?_⟩, permF (by norm_num)⟩, ?_⟩, ?_⟩, ?_⟩
  · intro t ht
    simp only [j2C1Gens, j2C2Gens, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact permF (by norm_num)
  · intro t ht
    simp only [j2DGens, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · rw [g1_eq.1]
      exact permOK_unpack g1_eq.2 hi.1
    · rw [g2_eq.1]
      exact permOK_unpack g2_eq.2 hi.2.1
  · rw [d0_eq.1, involOK_unpack' (by norm_num) idT_eq cId d0_eq.2]
    exact hd
  · rw [c0_eq.1, invT_unpack (by norm_num) hi.2.2.1]
    exact invOK_unpack c0_eq.2 hci hi.2.2.1
  · rw [c0_eq.1, invT_unpack (by norm_num) hi.2.2.1, tabF (by norm_num), d0_eq.1,
      compT_unpack hci c17.1, compT_unpack (canonK_pcomp hci c17.1) c0_eq.2,
      compT_unpack c17.1 d0_eq.2,
      tblEq_unpack (canonK_pcomp (canonK_pcomp hci c17.1) c0_eq.2) (canonK_pcomp c17.1 d0_eq.2)]
    exact fusK

end CertificateChecks.KernelSpor.J2Fus

end
