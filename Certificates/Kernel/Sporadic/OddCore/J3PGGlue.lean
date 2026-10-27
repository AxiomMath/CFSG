module

public import Certificates.Kernel.Sporadic.OddCore.C129006
public import Certificates.Kernel.Sporadic.OddCore.CentGlue
public import Certificates.Kernel.J3Dc.Final
public import CFSG.Certificates.Kernel.BfsPinAlg
public import CFSG.Sporadic.SmallOddCore.J3CheckInputs

public section

namespace CertificateChecks.KernelSpor.OddCore.J3W

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.PkPow CFSG.KC.BfsPin CFSG.KS.MulH
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.OddCore CertificateChecks.KernelCensus

theorem cn : szOK 6156 13 = true ∧ canonK 6156 13 (mask 13) (6156 * 13) (J3CentP 21) = true ∧
    canonK 6156 13 (mask 13) (6156 * 13) (J3S.F 0) = true ∧
    canonK 6156 13 (mask 13) (6156 * 13) (J3S.F 1) = true ∧
    canonK 6156 13 (mask 13) (6156 * 13) (pidn 6156 13) = true := by
  simpa only [bAnd_iff] using canonJ3

theorem t_eq : j3CentTbl 21 = tabT (unpack 6156 13 (J3CentP 21)) := by
  rw [← j3CentTbl_eq (by norm_num), tabT_natArr]

theorem pg_eq {l : Nat} (hl : l < 2) : j3PGTbls[l]! = tabT (unpack 6156 13 (J3S.F l)) := by
  have h : j3PGTbls[l]! = CFSG.Sporadic.Schreier.j3StrongArrs[l]!.map UInt32.ofNat := by
    interval_cases l <;> simp [j3PGTbls]
  rw [h, CFSG.KD.J3Dc.strong_eq (by omega)]
  rfl

theorem idT_eq : idT 6156 = tabT (unpack 6156 13 (pidn 6156 13)) := by
  rw [idT_tabT, idA_eq cn.1]

theorem strictN_id (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem pows (X : Nat) : Pows 6156 13 X (ppw 6156 13 X) :=
  ⟨rfl, fun e => strictN_id (ppw 6156 13 X e) (fun q => pcomp 6156 13 (mask 13) X q)⟩

theorem perm_t : permOK 6156 (j3CentTbl 21) = true :=
  List.all_eq_true.1 j3_permOK_all 21 (List.mem_range.2 (by norm_num))

theorem not_of_bIf {c : Bool} (h : bIf(c, false, true) = true) : c = false := by
  cases c
  · rfl
  · exact absurd h Bool.false_ne_true

theorem foldl_pg {n w : Nat} {gs : Array Table} {S : Nat → Nat} :
    ∀ (wd : List Nat) (acc : Nat), canonK n w (mask w) (n * w) acc = true →
      (∀ l ∈ wd, gs[l]! = tabT (unpack n w (S l)) ∧ canonK n w (mask w) (n * w) (S l) = true) →
      wd.foldl (fun a l => compT n a gs[l]!) (tabT (unpack n w acc)) =
          tabT (unpack n w (wfoldK n w (mask w) S wd acc)) ∧
        canonK n w (mask w) (n * w) (wfoldK n w (mask w) S wd acc) = true
  | [], acc, ha, _ => ⟨rfl, ha⟩
  | l :: rest, acc, ha, h => by
    obtain ⟨h1, h2⟩ := h l List.mem_cons_self
    rw [List.foldl_cons, h1, compT_unpack ha h2, wfoldK_cons]
    exact foldl_pg rest _ (canonK_pcomp ha h2) fun l' hl' => h l' (List.mem_cons_of_mem l hl')

end CertificateChecks.KernelSpor.OddCore.J3W

end
