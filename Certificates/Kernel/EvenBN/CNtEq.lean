
module

public import Certificates.Kernel.EvenBN.CNtAux
public import Certificates.Kernel.SporSch.Tits.Inv2266
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelEvenBN

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.Schreier.Tits CertificateChecks.KernelSpor CertificateChecks.KernelSporSch
open CertificateChecks.KernelSporSch.TitsHelp CertificateChecks.KernelSporSch.TitsInv
open CertificateChecks.KernelSpor.Tits2268 CFSG.KC.BfsPin

theorem cnt_eq : titsCNt = CNtC.map (fun k => unpack 1755 11 (PN k)) :=
  surv5K_soundCT bindsN permN TitsN.hl agrTN mCNt aCNt TitsNtE.all

theorem cnt_canon : ∀ k ∈ CNtC, C (PN k) := by
  intro k hk
  have hlt := (ascK_spec aCNt).2 k hk
  obtain ⟨d0, d1, d2, d3, d4, -⟩ := code_facts hlt.2
  have ct := allN_spec canTRN
  unfold PN
  rw [prodCode_eq]
  exact canonK_pcomp (canonK_pcomp (canonK_pcomp (canonK_pcomp (allN_spec (ct 0 (by omega)) _ d0)
    (allN_spec (ct 1 (by omega)) _ d1)) (allN_spec (ct 2 (by omega)) _ d2))
    (allN_spec (ct 3 (by omega)) _ d3)) (allN_spec (ct 4 (by omega)) _ d4)

theorem cnt_len : CNtC.length = 1536 := Nat.eq_of_beq_eq_true lCNt

theorem cnt_getD {i : Nat} (hi : i < 1536) (d : Array Nat) :
    titsCNt.getD i d = unpack 1755 11 (PN (CNtC.getD i 0)) := by
  rw [cnt_eq]
  have h : i < CNtC.length := by rw [cnt_len]; exact hi
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem cnt_mem {i : Nat} (hi : i < 1536) : CNtC.getD i 0 ∈ CNtC := by
  have h : i < CNtC.length := by rw [cnt_len]; exact hi
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  exact List.getElem_mem h

theorem aux_eq : CFSG.Quasithin.RuRank3.titsAuxArr = unpack 1755 11 (TAux.F 0) := by
  change hexTable 3 1755 (1755 * 0) CFSG.Quasithin.RuRank3.titsAuxText = _
  rw [TAux.eq]
  exact CFSG.KC.Misc.HexFlat.hexTable_sound TAux.all 0 (by norm_num)

end CertificateChecks.KernelEvenBN

end
