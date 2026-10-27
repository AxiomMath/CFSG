module

public import Certificates.Kernel.SporSch.Ly.Syl2190
public import Certificates.Kernel.SporSch.Ly.GLQSig
public import Certificates.Kernel.SporSch.Ly.GLQWords
public import Certificates.Kernel.SporSch.Ly.GLQCands
public import Certificates.Kernel.SporSch.Ly.GLQInvo
public import CFSG.Certificates.Kernel.SporSch.LyGLQTable
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.LyGQF

open CFSG.KC.Enum CFSG.KS CFSG.KC.Ord CFSG.KS.SporSch.LyM CFSG.KD.OrdLy CFSG.KS.SporSch.LySyl
open CFSG.Sporadic.LySchreier.Native CFSG.Sporadic.He.Native CFSG.Sporadic.Ly.Native
open CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.LyBS
open CertificateChecks.KernelSporSch.LyBSF CertificateChecks.KernelSporSch.LyR3E
open CertificateChecks.KernelSporSch.LySyF CFSG.KS.SporSch.LyGLQ

local notation "U" X:max => unpackL 111 12 1332 X

theorem tab_eq : mulTabOf 256 (sylowBFS (sylowGens (cStarArr (U B4))) 256).2.1
    (sylowBFS (sylowGens (cStarArr (U B4))) 256).2.2.1
    (sylowBFS (sylowGens (cStarArr (U B4))) 256).2.2.2 = TBL LySt.MT 256 := by
  have hpl : ∀ j < 256, plOK LySy.W LySt.PL 256 j = true := fun j hj => allN_spec LySt.plAll j hj
  have hB := bfs_sound (kg := 6) (c := 256) (cap := 256) (nS := 32) (Hh := 8) (UG := LySy.UG)
    (E := LySy.E) (W := LySy.W) (PL := LySt.PL) (SO := LySy.ST) (SOI := LySy.SIT) (C := LySy.C)
    consts (fun k hk => hv (vUGk hk)) (fun i hi => hv (vEi hi)) (Nat.eq_of_beq_eq_true LySy.e0)
    (by decide) (fun i hi => allN_spec LySy.srt i hi) rfl rfl rfl (Nat.eq_of_beq_eq_true LySy.c0)
    (Nat.eq_of_beq_eq_true LySy.cN) LySy.hrun hpl (Nat.eq_of_beq_eq_true LySt.pl0)
    ⟨us_size, us_get⟩
  have hT := mulTab_sound (n := 256) (MT := LySt.MT) (W := LySy.W) (PL := LySt.PL) (by decide)
    (by decide) hpl
    (fun i hi => chain_atB LySt.rowAll hi)
  rw [hB.1]
  dsimp only [recOf]
  exact hT.1

theorem hid : ∀ b < 256, tmK LySt.MT 0 b = b := by
  have c : LySt.rowQ 0 = true := chain_atB LySt.rowAll (B := 256) (by decide)
  unfold LySt.rowQ rowOK at c
  rw [CFSG.KS.Raw.strictB_eq] at c
  have c2 : allN 256 (fun j => Nat.beq (b8 (LySt.MT 0) j) j) = true := by
    revert c
    cases Nat.blt (LySt.MT 0) (Nat.shiftLeft 1 (Nat.mul 8 256)) <;> intro c
    · exact absurd c Bool.false_ne_true
    · exact c
  intro b hb
  exact Nat.eq_of_beq_eq_true (allN_spec c2 b hb)

theorem w1 : getW LyGQ.W 1 = [0] := by decide +kernel

theorem w3 : getW LyGQ.W 3 = [1] := by decide +kernel

theorem w5 : getW LyGQ.W 5 = [2] := by decide +kernel

theorem facts : glqCertificate () = true := by
  unfold glqCertificate glqWithGens glqWithEnum
  rw [b4_eq, tab_eq]
  exact table_ok hid LyGQ.sig LyGQ.assoc LyGQ.words w1 w3 w5 LyGQ.auts LyGQ.alen LyGQ.invo

end CertificateChecks.KernelSporSch.LyGQF

end
