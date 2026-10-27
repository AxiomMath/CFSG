
module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4M2Gens
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Certificates.Kernel.J4Q.RepQT2B
public import CFSG.Certificates.Kernel.SporSch.J4SColsSound
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic
public import Certificates.Data.Kernel.J4FixCE
public import Certificates.Kernel.J4Count.FixCEData
public import Certificates.Kernel.J4Q.Mat

@[expose] public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Count.FixCE

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2A
open CFSG.Quasithin.J4M2 CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KC.J4FixCE CFSG.KD.J4FixCE
open CFSG.KS.SporSch.C11 MulAction CertificateChecks.KernelJ4Q
open CFSG.Sporadic.SmallF2 (toVecD toVecD_apply)
open CFSG.Sporadic.J4Schreier (app11)

@[expose] def PR (g : J) (m : ℕ) : Prop := ∃ X : Array V2, WfA X ∧ encR X = m ∧ Mx g = rowsMatrix X

theorem PR_of {g : J} {X : Array V2} {m : ℕ} (hX : WfA X ∧ encR X = m) (hg : Mx g = rowsMatrix X) :
    PR g m := ⟨X, hX.1, hX.2, hg⟩

theorem PR_one : PR 1 one := PR_of (id_enc hK) (by rw [map_one, rowsMatrix_idRows])

theorem PR_mul {g h : J} {a b : ℕ} (hg : PR g a) (hh : PR h b) : PR (g * h) (mulJ c rm a b) := by
  obtain ⟨X, hX, ha, hgX⟩ := hg
  obtain ⟨Y, hY, hb, hhY⟩ := hh
  exact PR_of (mul_enc hK ⟨hX, ha⟩ ⟨hY, hb⟩) (by rw [map_mul, hgX, hhY, rowsMatrix_mulRows])

theorem PR_pow {g : J} {a : ℕ} (hg : PR g a) (e : ℕ) : PR (g ^ e) (powJ c rm one a e) := by
  obtain ⟨X, hX, ha, hgX⟩ := hg
  exact PR_of (pow_enc hK ⟨hX, ha⟩ e) (by rw [map_pow, hgX, rowsMatrix_powRows])

theorem PR_eq {g h : J} {a : ℕ} (hg : PR g a) (hh : PR h a) : g = h := by
  obtain ⟨X, hX, ha, hgX⟩ := hg
  obtain ⟨Y, hY, hb, hhY⟩ := hh
  have e : eqRows X Y = true := by
    rw [eqRows_of ⟨hX, ha⟩ ⟨hY, hb⟩]
    exact Nat.beq_refl a
  apply Mx_injective
  rw [hgX, hhY, eqRows_iff.1 e]

theorem PR_eq_of_beq {g h : J} {a b : ℕ} (hg : PR g a) (hh : PR h b) (e : Nat.beq a b = true) :
    g = h := by
  rw [Nat.eq_of_beq_eq_true e] at hg
  exact PR_eq hg hh

theorem row_toVec (a : V2) : toRow a.toVec = toRow (toVecD 112 (v2N a)) := by
  funext j
  change a.toVec j = toVecD 112 (v2N a) j
  rw [V2.toVec_apply, toVecD_apply, testBit_v2N a (by omega)]

theorem inv_smul_PR {g : J} {m : ℕ} (hg : PR g m) {p : ℕ} (hp : p < 2 ^ 112) :
    g⁻¹ • toRow (toVecD 112 p) = toRow (toVecD 112 (vecJ rm p m)) := by
  obtain ⟨X, hX, hm, hgX⟩ := hg
  have hv := wf_ofN hp
  have e1 : toRow (toVecD 112 p) = toRow (ofN p).toVec := by rw [row_toVec, ofN_eq hp]
  have e2 : g⁻¹ • toRow (ofN p).toVec = toRow (frApply (frTable X) (ofN p)).toVec := by
    rw [← ofRow_inj, inv_smul_row, frApply_toVec_eq_vecMul, ← Mx_apply, hgX]
    rfl
  rw [e1, e2, row_toVec, v2N_frApply hK hX hv, ofN_eq hp, hm]

theorem fix_of_PR {g : J} {m : ℕ} (hg : PR g m) {p : ℕ} (hp : p < 2 ^ 112) (h : vecJ rm p m = p) :
    g • toRow (toVecD 112 p) = toRow (toVecD 112 p) := by
  have e := inv_smul_PR hg hp
  rw [h] at e
  calc g • toRow (toVecD 112 p) = g • (g⁻¹ • toRow (toVecD 112 p)) := by rw [e]
    _ = _ := smul_inv_smul _ _

@[expose] noncomputable def gw (w : List ℕ) : J := w.foldl (fun acc n => acc * gE n) 1

theorem inv_eq_sq {g : J} {m : ℕ} (hg : PR g m) (h3 : Nat.beq (powJ c rm one m 3) one = true) :
    g⁻¹ = g * g := by
  have e : g ^ 3 = 1 := PR_eq_of_beq (PR_pow hg 3) PR_one h3
  refine inv_eq_of_mul_eq_one_left ?_
  rw [← e, pow_succ, pow_two]

theorem rootBits_lt : CFSG.Sporadic.J4Schreier.rootBits < 2 ^ 112 := by
  unfold CFSG.Sporadic.J4Schreier.rootBits
  norm_num

section H

end H

section E

@[expose] noncomputable def CC : Array ℕ := unpack11 PC

theorem CC_get {j : ℕ} (hj : j < 11) : CC[j]! = colK PC j := unpackW_get hj

theorem eta_ofFn {G : Type*} [Group G] (u : ℕ → G) : ∀ (n a : ℕ),
    eta u n a = (List.ofFn fun j : Fin n => if a.testBit j then u j else 1).prod
  | 0, a => by simp [eta]
  | n + 1, a => by
    rw [eta_succ, eta_ofFn u n a, List.ofFn_succ', List.prod_concat]
    rfl

end E

section Final

end Final

end CertificateChecks.KernelJ4Count.FixCE

end
