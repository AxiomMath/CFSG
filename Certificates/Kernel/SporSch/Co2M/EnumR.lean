
module

public import Certificates.Kernel.SporSch.Co2M.EnumQ
public meta import Certificates.Kernel.SporSch.Co2M.EnumGen
public meta import CFSG.Sporadic.Co2Schreier.Arrays
public meta import CFSG.Sporadic.Co2Cert.Data
meta import Certificates.Kernel.Misc.Perm.HexCmd
import CFSG.Certificates.Kernel.Common.Harness
import Certificates.Kernel.Misc.Perm.HexCmd

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.Co2M

open CFSG.Sporadic.Co2Schreier CFSG.Sporadic.Co2Cert

meta def rgRows : Array (Array Nat) :=
  rArrs.map fun a => Gen.rowsOf (Gen.matOf vecsM (Gen.basisOf vecsM) a)

meta def rRecs : Array (Array Nat) :=
  Gen.enumRecs vecsM (rgRows.map fun r => (List.range 22).foldl (fun a i => a ||| (r[i]! <<< (22 * i))) 0) 2048

meta def rcRows : Array (Array Nat) :=
  (dArrs ++ dArrs.map (CFSG.Monster.B.Co2.Native.invCand 2300)).map fun a =>
    Gen.rowsOf (Gen.matOf vecsM (Gen.basisOf vecsM) a)

meta def rPis : Array (Array Nat) := localRec.chains.rAction.origArrs

end CertificateChecks.KernelSporSch.Co2M

#kmisc_packarrs CertificateChecks.KernelSporSch.Co2M.RG CertificateChecks.KernelSporSch.Co2M.rgRows 22
#kmisc_packarrs CertificateChecks.KernelSporSch.Co2M.RR CertificateChecks.KernelSporSch.Co2M.rRecs 22
#kmisc_packarrs CertificateChecks.KernelSporSch.Co2M.RC CertificateChecks.KernelSporSch.Co2M.rcRows 22
#kmisc_packarrs CertificateChecks.KernelSporSch.Co2M.RPI CertificateChecks.KernelSporSch.Co2M.rPis 12

namespace CertificateChecks.KernelSporSch.Co2M

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Co2M CFSG.KS.Co2LE CFSG.Sporadic.Co2Schreier

theorem rg_ok : allN 10 (fun j => Nat.beq (RG j) (rT.getD j (0, 0)).1) = true := by
  decide +kernel

theorem rhead_ok : bAnd(Nat.beq (eM RR 0) I22, Nat.beq (mR RR 10 0) 1) = true := by quickRfl

theorem rrecs_ok : allN 2048 (fun k => recK RR RG (PV 0) 10 2048 k) = true := by quickRfl

theorem rpi_ok : allN 2 (fun i => bindListK 2048 12 (RPI i)
    (localRec.chains.rAction.generators.getD i [])) = true := by
  decide +kernel

theorem rc_ok : allN 2 (fun i => bAnd(Nat.beq (RC i) (dT.getD i (0, 0)).1,
    Nat.beq (RC (Nat.add 2 i)) (dT.getD i (0, 0)).2)) = true := by
  decide +kernel

theorem rconj_ok : allN 2 (fun i => allN 2048 (fun k =>
    conjK RR (RC i) (RC (Nat.add 2 i)) (RPI i) 12 2048 k)) = true := by
  quickRfl

theorem rcent_ok : ((List.range 2048).filter (centK RR RG 10) == centerIdxR) = true := by
  quickRfl

theorem rzt_ok : bAnd(Nat.beq (eM RR 617) zP.1, Nat.beq (eM RR 434) tP.1) = true := by
  decide +kernel

open CFSG.KS.MatRep CFSG.Monster.B.Mathieu CFSG.Sporadic.Co2Cert CFSG.Monster.B.Co2.Native

theorem r_len : rT.length = 10 := by rw [rT, List.length_map, lens.2.2.2.1]

theorem d_len : dT.length = 2 := by rw [dT, List.length_map, lens.2.1]

theorem rgens : GensRep co2PackedVecs rArrs RG 10 := by
  refine ⟨by rw [rRep.1, r_len], fun j hj => ⟨(rT.getD j (0, 0)).2, ?_⟩⟩
  rw [Nat.eq_of_beq_eq_true (allN_spec rg_ok j hj)]
  exact repT_get rRep (by rw [r_len]; exact hj)

theorem rrecs : Recs RR RG (PV 0) 10 2048 := by
  obtain ⟨h1, h2⟩ := (bAnd_iff (Nat.beq (eM RR 0) I22) (Nat.beq (mR RR 10 0) 1)).1 rhead_ok
  exact ⟨allN_spec rrecs_ok, Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, by norm_num⟩

theorem rcrep : ∀ i < 2, Rep 22 co2PackedVecs dArrs[i]! (RC i) (RC (Nat.add 2 i)) := by
  intro i hi
  obtain ⟨h1, h2⟩ := (bAnd_iff (Nat.beq (RC i) (dT.getD i (0, 0)).1)
    (Nat.beq (RC (Nat.add 2 i)) (dT.getD i (0, 0)).2)).1 (allN_spec rc_ok i hi)
  rw [Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2]
  exact repT_get dRep (by rw [d_len]; exact hi)

theorem rgen_len : localRec.chains.rAction.generators.length = 2 := by decide +kernel

theorem enumR_elems : enumR.elems = LL co2PackedVecs RR 2048 :=
  (leftEnum_facts vok rrecs rgens (le_refl 2048)).1

theorem enumR_rep : ∀ k < 2048, ∃ M', Rep 22 co2PackedVecs enumR.elems[k]! (eM RR k) M' := by
  rw [enumR_elems]
  exact (leftEnum_facts vok rrecs rgens (le_refl 2048)).2.2

theorem coreR : coreOK rArrs dArrs localRec.chains.rAction.origArrs 2048 centerIdxR enumR = true ∧
    eqA 2300 enumR.elems[617]! zArr = true ∧ eqA 2300 enumR.elems[434]! tArr = true := by
  obtain ⟨hps, hpg⟩ := origArrs_get rgen_len rpi_ok
  obtain ⟨hz, ht⟩ := (bAnd_iff (Nat.beq (eM RR 617) zP.1) (Nat.beq (eM RR 434) tP.1)).1 rzt_ok
  refine ⟨coreOK_of vok rrecs rgens (le_refl 2048) (by rw [dRep.1, d_len]) rcrep hpg
    (fun i hi k hk => allN_spec (allN_spec rconj_ok i hi) k hk) rcent_ok, ?_, ?_⟩
  · rw [enumR_elems]
    exact eqA_entry (by norm_num) zRep (Nat.eq_of_beq_eq_true hz)
  · rw [enumR_elems]
    exact eqA_entry (by norm_num) tRep (Nat.eq_of_beq_eq_true ht)

end CertificateChecks.KernelSporSch.Co2M

end
