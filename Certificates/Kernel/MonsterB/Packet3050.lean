module

public import Certificates.Data.CFSGNative.MonsterB.PacketCheck
public import CFSG.Monster.B.Rep4371.GlueDefs
public import CFSG.Certificates.Kernel.MonsterB.Rep4371XNf
public import CFSG.Certificates.Kernel.MonsterB.Rep4371XPins
public import CFSG.Certificates.Kernel.KDense.Data.Fix
public import CFSG.Certificates.Kernel.BabyMonster.PktBind.Text
import CFSG.Certificates.Kernel.MonsterB.Rep4371XTauSound
import CFSG.Certificates.Kernel.MonsterB.Rep4371XLabSound
import CFSG.Certificates.Kernel.MonsterB.Rep4371XOctSound
import CFSG.Certificates.Kernel.MonsterB.Rep4371XC.Pauli
import CFSG.Certificates.Kernel.MonsterB.Rep4371XC.Perm0
import CFSG.Certificates.Kernel.MonsterB.Rep4371XC.Perm1
import CFSG.Certificates.Kernel.MonsterB.Rep4371XC.Sign
import CFSG.Certificates.Kernel.MonsterB.Rep4371XC.Xi0
import CFSG.Certificates.Kernel.MonsterB.Rep4371XC.Xi1
import CFSG.Certificates.Kernel.MonsterB.Rep4371XC.Misc
import CFSG.Certificates.Kernel.MonsterB.Rep4371XC.OctSign
import CFSG.Certificates.Kernel.KDense.Data.Checks
import Certificates.Kernel.BabyMonster.PktShape
import Certificates.Kernel.BabyMonster.ForallLt
public import Certificates.Data.Kernel.KDense.LetterOK
public import Certificates.Data.Kernel.KDense.Plan
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

public section

namespace CertificateChecks.KernelBM.Pkt3050

open CFSG.KC.Rep4371X CFSG.KC.BM.Pkt CFSG.Monster.B CFSG.Monster.B.Rep4371

theorem row_eq {i : Nat} (hi : i < 48) : (CFSG.Monster.B.Native.packetRows ())[i]! =
    lineRows (lineOf CFSG.KD.PktBind.CH CFSG.KD.PktBind.S i) := by
  rw [CertificateChecks.KernelBM.PktShape.packetRows_eq, getElem!_pos _ i (by simp [hi]),
    List.getElem_toArray, List.getElem_map, List.getElem_range]

theorem pauli_all : ∀ i < 23, pauliChk CFSG.KD.KDF.TH CFSG.KD.PktBind.CH CFSG.KD.PktBind.S i = true := by
  forall_lt_consts CFSG.KC.Rep4371X.C.pauli 23

theorem perm_all : ∀ r < 12, permChk CFSG.KD.KDF.TH CFSG.KD.PktBind.CH CFSG.KD.PktBind.S r = true := by
  forall_lt_consts CFSG.KC.Rep4371X.C.perm 12

theorem sign_all : ∀ r < 11, signChk CFSG.KD.KDF.TH CFSG.KD.PktBind.CH CFSG.KD.PktBind.S r = true := by
  forall_lt_consts CFSG.KC.Rep4371X.C.sign 11

theorem xi_all : ∀ c < 9, xiChk CFSG.KD.KDF.TH CFSG.KD.PktBind.CH CFSG.KD.PktBind.S c = true := by
  forall_lt_consts CFSG.KC.Rep4371X.C.xi 9

theorem genCheck_pauli {i : Nat} (hi : i < 23) : Native.genCheck i = true := by
  have hc := pauli_all i hi
  obtain ⟨hs, ha, hd⟩ := pauli_pins i hi
  unfold pauliChk at hc
  simp only [strictB_eq] at hc
  rw [hs, ha, hd] at hc
  unfold Native.genCheck Native.genAct
  rw [if_pos hi, native_genOK, native_keyActPauli, native_qPauli, row_eq (by omega)]
  exact genOK_of_lineChk CFSG.KD.KDF.th_ok (actPauli_eq (Model.qPauli i)) hc

theorem genCheck_perm {r : Nat} (hr : r < 12) : Native.genCheck (23 + r) = true := by
  have hc := perm_all r hr
  obtain ⟨hsz, hlt, hpe, hbt, hk⟩ := perm_pins r hr
  have hP := pe_all hpe hsz hlt
  have hK : (Model.kappaN Model.recPerms[r]! 63).toNat = pK r := by
    rw [← hk, ← hbt, CFSG.KC.Trace6091.kappaT_eq (fun i _ => hP i) 63]
  unfold permChk at hc
  simp only [strictB_eq] at hc
  unfold Native.genCheck Native.genAct
  rw [if_neg (by omega), if_pos (by omega), native_genOK, native_keyActPerm, native_recPerms,
    row_eq (by omega), show 23 + r - 23 = r by omega]
  exact genOK_of_lineChk CFSG.KD.KDF.th_ok (actPerm_eq CFSG.KD.KDF.th_ok hP hbt hK) hc

theorem genCheck_sign {r : Nat} (hr : r < 11) : Native.genCheck (35 + r) = true := by
  have hc := sign_all r hr
  obtain ⟨hA, hlt, hW, hT, hPA⟩ := sign_pins r hr
  unfold signChk at hc
  simp only [strictB_eq] at hc
  unfold Native.genCheck Native.genAct
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), native_genOK, native_keyActSign,
    row_eq (by omega), show 35 + r - 35 = r by omega, ← hA]
  exact genOK_of_lineChk CFSG.KD.KDF.th_ok (actSign_eq CFSG.KD.KDF.th_ok hlt hW hT hPA) hc

set_option maxRecDepth 200000 in
theorem genCheck_xi : Native.genCheck 46 = true := by
  unfold Native.genCheck Native.genAct
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), native_genOK, native_keyActXi,
    row_eq (by omega)]
  obtain ⟨hs0, hk0, hk9, hmono⟩ := xi_pins
  have hlen : (lineOf CFSG.KD.PktBind.CH CFSG.KD.PktBind.S 46).2 / 3 = f16 XS 9 :=
    Nat.eq_of_beq_eq_true CFSG.KC.Rep4371X.C.xiLen
  have hsc := chunks_scan (f := actXiT CFSG.KD.KDF.TH) (TH := CFSG.KD.KDF.TH)
    (N := (lineOf CFSG.KD.PktBind.CH CFSG.KD.PktBind.S 46).1) (S := f16 XS) (K := f16 XK) hs0 hk0 9
    hmono xi_all
  rw [hk9, ← hlen] at hsc
  exact genOK_of_scan CFSG.KD.KDF.th_ok (actXi_eq CFSG.KD.KDF.th_ok) hsc

theorem tauCheck_true : Native.tauCheck = true := by
  obtain ⟨-, hrows⟩ := tau_rows CFSG.KC.Rep4371X.C.tau
  unfold Native.tauCheck
  rw [List.all_eq_true]
  intro k hk
  have hk' := List.mem_range.1 hk
  rw [row_eq (by omega), native_tauRow, tauRow_eq hk', beq_iff_eq, ← hrows k hk', Array.toArray_toList]

theorem labels_ok : Native.labelsCheck = true ∧ Native.spinIndexCheck = true :=
  labels_true CFSG.KD.PktLab.eq (by decide +kernel) (by decide +kernel) CFSG.KD.KDF.th_ok
    CFSG.KC.Rep4371X.C.lab

theorem oct_ok : Native.octDataOK = true ∧ Native.octSignOK = true := by
  rw [native_octDataOK, native_octSignOK]
  exact ⟨octDataOK_of CFSG.KC.Rep4371X.C.oct, CFSG.KC.Rep4371X.C.octSign_ok⟩

end CertificateChecks.KernelBM.Pkt3050

end
