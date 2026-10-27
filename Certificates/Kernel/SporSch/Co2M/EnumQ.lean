
module

public import Certificates.Kernel.SporSch.Co2M.Span
public import Certificates.Kernel.SporSch.Co2M.Local
public import CFSG.Sporadic.Co2Schreier.CoreCheckInputs
public meta import Certificates.Kernel.SporSch.Co2M.EnumGen
public meta import CFSG.Sporadic.Co2Schreier.Arrays
public meta import CFSG.Sporadic.Co2Cert.Data
meta import Certificates.Kernel.Misc.Perm.HexCmd
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.SporSch.Co2M.EnumGen
import Certificates.Kernel.Misc.Perm.HexCmd

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.Co2M

open CFSG.Sporadic.Co2Schreier CFSG.Sporadic.Co2Cert

meta def vecsM : Array Nat := co2PackedVecs

meta def qgRows : Array (Array Nat) :=
  qArrs.map fun a => Gen.rowsOf (Gen.matOf vecsM (Gen.basisOf vecsM) a)

meta def qRecs : Array (Array Nat) :=
  Gen.enumRecs vecsM (qgRows.map fun r => (List.range 22).foldl (fun a i => a ||| (r[i]! <<< (22 * i))) 0) 512

meta def qcRows : Array (Array Nat) :=
  (cArrs ++ cArrs.map (CFSG.Monster.B.Co2.Native.invCand 2300)).map fun a =>
    Gen.rowsOf (Gen.matOf vecsM (Gen.basisOf vecsM) a)

meta def qPis : Array (Array Nat) := localRec.chains.qAction.origArrs

end CertificateChecks.KernelSporSch.Co2M

#kmisc_packarrs CertificateChecks.KernelSporSch.Co2M.QG CertificateChecks.KernelSporSch.Co2M.qgRows 22
#kmisc_packarrs CertificateChecks.KernelSporSch.Co2M.QR CertificateChecks.KernelSporSch.Co2M.qRecs 22
#kmisc_packarrs CertificateChecks.KernelSporSch.Co2M.QC CertificateChecks.KernelSporSch.Co2M.qcRows 22
#kmisc_packarrs CertificateChecks.KernelSporSch.Co2M.QPI CertificateChecks.KernelSporSch.Co2M.qPis 12

namespace CertificateChecks.KernelSporSch.Co2M

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Co2M CFSG.KS.Co2LE CFSG.Sporadic.Co2Schreier

theorem qg_ok : allN 8 (fun j => Nat.beq (QG j) (qT.getD j (0, 0)).1) = true := by
  decide +kernel

theorem qhead_ok : bAnd(Nat.beq (eM QR 0) I22, Nat.beq (mR QR 8 0) 1) = true := by quickRfl

theorem qrecs_ok : allN 512 (fun k => recK QR QG (PV 0) 8 512 k) = true := by quickRfl

theorem qpi_ok : allN 2 (fun i => bindListK 512 12 (QPI i)
    (localRec.chains.qAction.generators.getD i [])) = true := by
  decide +kernel

theorem qc_ok : allN 2 (fun i => bAnd(Nat.beq (QC i) (cT.getD i (0, 0)).1,
    Nat.beq (QC (Nat.add 2 i)) (cT.getD i (0, 0)).2)) = true := by
  decide +kernel

theorem qconj_ok : allN 2 (fun i => allN 512 (fun k =>
    conjK QR (QC i) (QC (Nat.add 2 i)) (QPI i) 12 512 k)) = true := by
  quickRfl

theorem qcent_ok : ((List.range 512).filter (centK QR QG 8) == [0, 23]) = true := by
  quickRfl

theorem qz_ok : Nat.beq (eM QR 23) zP.1 = true := by decide +kernel

open CFSG.KS.MatRep CFSG.Monster.B.Mathieu CFSG.Sporadic.Co2Cert CFSG.Monster.B.Co2.Native

theorem origArrs_get {c : ChainRecord} {n w nc : ℕ} {PI : ℕ → ℕ}
    (hl : c.generators.length = nc)
    (hb : allN nc (fun i => bindListK n w (PI i) (c.generators.getD i [])) = true) :
    c.origArrs.size = nc ∧ ∀ i < nc, ∀ k < n, (c.origArrs[i]!)[k]! = pg w (mask w) (PI i) k := by
  refine ⟨by rw [ChainRecord.origArrs_size, hl], fun i hi k hk => ?_⟩
  have e : c.origArrs[i]! = (c.generators.getD i []).toArray := by
    unfold ChainRecord.origArrs
    rw [getElem!_pos _ i (by simp [hl]; omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hl]; omega : i < _)]
  rw [e, toArray_eq_of_bindListK (allN_spec hb i hi), CFSG.KC.Misc.PairCount.unpack_get hk]

theorem q_len' : qT.length = 8 := by
  have h : localRec.qWords.length = 8 := by decide +kernel
  rw [qT, List.length_map, h]

theorem c_len'' : cT.length = 2 := by rw [cT, List.length_map, cInitT, List.length_map, lens.1]

theorem qgens : GensRep co2PackedVecs qArrs QG 8 := by
  refine ⟨by rw [qRep.1, q_len'], fun j hj => ⟨(qT.getD j (0, 0)).2, ?_⟩⟩
  rw [Nat.eq_of_beq_eq_true (allN_spec qg_ok j hj)]
  exact repT_get qRep (by rw [q_len']; exact hj)

theorem qrecs : Recs QR QG (PV 0) 8 512 := by
  obtain ⟨h1, h2⟩ := (bAnd_iff (Nat.beq (eM QR 0) I22) (Nat.beq (mR QR 8 0) 1)).1 qhead_ok
  exact ⟨allN_spec qrecs_ok, Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, by norm_num⟩

theorem qcrep : ∀ i < 2, Rep 22 co2PackedVecs cArrs[i]! (QC i) (QC (Nat.add 2 i)) := by
  intro i hi
  obtain ⟨h1, h2⟩ := (bAnd_iff (Nat.beq (QC i) (cT.getD i (0, 0)).1)
    (Nat.beq (QC (Nat.add 2 i)) (cT.getD i (0, 0)).2)).1 (allN_spec qc_ok i hi)
  rw [Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2]
  exact repT_get cRep (by rw [c_len'']; exact hi)

theorem qgen_len : localRec.chains.qAction.generators.length = 2 := by decide +kernel

theorem coreQ : coreOK qArrs cArrs localRec.chains.qAction.origArrs 512 [0, 23] enumQ = true ∧
    eqA 2300 enumQ.elems[23]! zArr = true := by
  obtain ⟨hps, hpg⟩ := origArrs_get qgen_len qpi_ok
  have hf := leftEnum_facts vok qrecs qgens (le_refl 512)
  refine ⟨coreOK_of vok qrecs qgens (le_refl 512) (by rw [cRep.1, c_len'']) qcrep hpg
    (fun i hi k hk => allN_spec (allN_spec qconj_ok i hi) k hk) qcent_ok, ?_⟩
  unfold enumQ
  rw [hf.1]
  exact eqA_entry (by norm_num) zRep (Nat.eq_of_beq_eq_true qz_ok)

end CertificateChecks.KernelSporSch.Co2M

end
