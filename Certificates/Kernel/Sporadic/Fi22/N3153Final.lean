
module

public import Certificates.Kernel.Sporadic.Fi22.N3153Chk
public import Certificates.Kernel.Sporadic.Fi22.G3147
public import Certificates.Kernel.Sporadic.Fi22.Ext2073
public import CFSG.Certificates.Kernel.Fi22Nbr3153Sound
public import CFSG.Certificates.Kernel.PackSetSound
public import CFSG.Certificates.Kernel.BfsPinAlg
public import CFSG.Monster.B.Fischer.Fi22GraphBoundBase
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.NativeSchreierEnum
public import CFSG.Monster.B.Fischer.Fi22CentralizerCheckBase
public import CFSG.Monster.B.Fischer.Fi22CoverBase
public import CFSG.Monster.B.Fischer.Fi22CoverCheckBase
public import CFSG.Monster.B.Fischer.Fi22GraphBoundCheckBase
public import CFSG.Monster.B.Fischer.Fi22LocalBase
public import CFSG.Sporadic.FischerOddCore.RefineSpec

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.N3153

open CFSG.KC.Enum CFSG.KC.N3153 CFSG.KD.N3153 CFSG.KS.Raw CFSG.KC.BfsPin
open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Monster.B.Fischer CFSG.Sporadic.FischerOddCore.Native CertificateChecks.KernelSpor

theorem gp0 : GP 0 = Fi22CGT.F 0 := Nat.eq_of_beq_eq_true (by quickRfl)
theorem gp1 : GP 1 = Fi22CGT.F 1 := Nat.eq_of_beq_eq_true (by quickRfl)
theorem gp2 : GP 2 = Fi22E2073.E := Nat.eq_of_beq_eq_true (by quickRfl)
theorem gp3 : GP 3 = pidn 3510 12 := Nat.eq_of_beq_eq_true (by quickRfl)

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem of_blocks {f : Nat → Bool}
    (h : ∀ s < 55, allBlk (Nat.mul 64 s) (fun x => bIf(Nat.blt x 3510, f x, true)) 64 = true) :
    ∀ x < 3510, f x = true := by
  intro x hx
  have h2 := CFSG.KC.Pack.allBlk_spec (h (x / 64) (by omega)) (x % 64) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul 64 (x / 64)) (x % 64) = x := by
    change 64 * (x / 64) + x % 64 = x
    omega
  have hb : Nat.blt x 3510 = true := Eq.mpr Nat.blt_eq hx
  rw [e, hb] at h2
  exact h2

theorem rows : ∀ x < 3510, rowOK 3510 693 R M S x = true := fun x hx =>
  CFSG.KC.Fi22Snd.rowOK_of_W (by norm_num) (by norm_num) dilK_ok
    (of_blocks (f := fun x => rowOKW 3510 693 R M S dilK x) Row.all x hx)

theorem imgs : ∀ k < 2, ∀ x < 3510, imgOK 3510 693 (GP k) R M x = true := by
  intro k hk
  interval_cases k
  · exact of_blocks Img0.all
  · exact of_blocks Img1.all

theorem gens_eq : ∀ k < 2, fi22OrigArrs[k]! = unpack 3510 12 (GP k) := by
  intro k hk
  rw [fi22OrigArrs, getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]
  change fi22ChainGen k = _
  rw [Fi22G.gen_eq hk]
  interval_cases k
  · rw [gp0]
  · rw [gp1]

theorem z_eq : (fi22OuterStrong3510 1)[0]! = unpack 3510 12 (GP 2) := by
  rw [Fi22E2073.outE, gp2]

theorem id_eq : idA 3510 = unpack 3510 12 (GP 3) := by
  rw [gp3]
  exact idA_eq (by decide +kernel)

theorem root_eq : fi22N0List = decodeRow 693 (R 0) := by
  rw [fi22N0List, z_eq]
  exact (root_sound (by norm_num) (by norm_num) (rows 0 (by norm_num))
    (CFSG.KC.Pack.allN_spec root)).symm

theorem graph : adjSearch 3510 fi22OrigArrs fi22N0List = rowsArr 3510 693 R ∧
    adjOK 3510 fi22OrigArrs (rowsArr 3510 693 R) fi22N0List = true :=
  graph_sound (ng := 2) (G := GP) (T := T) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by simp [fi22OrigArrs]) gens_eq rows imgs (CFSG.KC.Pack.allN_spec tree)
    (CFSG.KC.Pack.allN_spec sym0) root_eq

theorem nbr_eq : fi22Nbr = rowsArr 3510 693 R := graph.1

theorem adj : adjOK 3510 fi22OrigArrs fi22Nbr fi22N0List = true := by
  rw [nbr_eq]
  exact graph.2

theorem symm :
    ∀ x < 3510, ∀ y ∈ fi22Nbr[x]!, x ∈ fi22Nbr[y]! := by
  intro x hx y hy
  have hA := adjFacts_of_adjOK adj
  have hy' : y < 3510 := (hA.point ⟨x, hx⟩).lt y hy
  obtain ⟨g, hg, hgx⟩ := fi22P_exists_smul ⟨x, hx⟩ 0
  have hinv : NbrInv fi22Nbr g :=
    hA.inv_of_mem_closure rep_fi22OrigArrs_nat (fi22P_eq_closure_gens ▸ hg)
  have h1 := (hinv ⟨x, hx⟩ ⟨y, hy'⟩).1 hy
  rw [hgx, Fin.val_zero] at h1
  have h2 := hA.root_symm _ h1
  have h3 := (hinv ⟨y, hy'⟩ ⟨x, hx⟩).2
  rw [hgx, Fin.val_zero] at h3
  exact h3 h2

theorem facts3153 :
    adjOK 3510 fi22OrigArrs fi22Nbr fi22N0List = true ∧
      boundsOK 3510 fi22Nbr (idA 3510) fi22GraphBase fi22GraphOrbitBounds 4 = true := by
  refine ⟨adj, bounds_sound (d := 693) (T := GP 3) (P := O 0) (R := R) (M := M) (S := S)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) nbr_eq rows symm id_eq rfl
    (by decide) (fun s hs => ?_) ?_⟩
  · have h := Cell.all s hs
    rw [cellB, strictB_eq] at h
    exact h
  · have h := inj
    rw [strictB_eq] at h
    exact h

end CertificateChecks.KernelSpor.N3153

end
