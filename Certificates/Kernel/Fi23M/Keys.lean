
module

public import Certificates.Kernel.Fi23M.KeysBase
import all Certificates.Kernel.Fi23M.KeysBase

public import Certificates.Kernel.Fi23M.Psi
public import Certificates.Kernel.Fi23M.Matrix
public import Certificates.Kernel.Fi23K.OrbEq
public import CFSG.Perm.ChainSpec
import Certificates.Kernel.Fi23M.TreeK
import Certificates.Kernel.Fi23K.Misc
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import Mathlib

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi23M

open CFSG.F3.Native CFSG.Sporadic.Fi23 CFSG.Sporadic.Fi23.Native CFSG.KD.Fi23K CFSG.KC.Fi23K
  CFSG.KS.PC CFSG.KS.PCC CFSG.KS.PEnum CFSG.KC.Enum CFSG.Sporadic.Th.Native CFSG.KS.Raw.Orb

section

local notation "sg" => CFSG.KS.PC.sig 31671 (chainLetters orbLit)

theorem σ_wα_inv : ((σ wα)⁻¹).val = mA := inv_val_of σ_wα A_sq

theorem σ_wβ_inv : ((σ wβ)⁻¹).val = mB * mB := inv_val_of σ_wβ matrixFacts.B_inv

theorem conj_val (g : PG) : (σ (g * wD * g⁻¹)).val = (σ g).val * mW ^ 7 * ((σ g)⁻¹).val := by
  rw [map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul, σ_wD]

theorem conjA_val (g : PG) :
    mA * (σ (g * wD * g⁻¹)).val * mA = (σ ((wα * g) * wD * (wα * g)⁻¹)).val := by
  rw [conj_val, conj_val, map_mul, mul_inv_rev, Units.val_mul, Units.val_mul, σ_wα, σ_wα_inv]
  simp only [mul_assoc]

theorem conjB_val (g : PG) :
    mB * (σ (g * wD * g⁻¹)).val * (mB * mB) = (σ ((wβ * g) * wD * (wβ * g)⁻¹)).val := by
  rw [conj_val, conj_val, map_mul, mul_inv_rev, Units.val_mul, Units.val_mul, σ_wβ, σ_wβ_inv]
  simp only [mul_assoc]

theorem key_facts : ∀ f k, RowsWF (toVM (keyW f k)) ∧ canonM 253 (toVM (keyW f k)) = true ∧
    toMatW 253 (keyW f k) = (σ (gk f k * wD * (gk f k)⁻¹)).val
  | 0, k => by
    have e1 : keyW 0 k = matD := rfl
    have e2 : gk 0 k = 1 := rfl
    rw [e1, e2, one_mul, inv_one, mul_one, σ_wD]
    exact ⟨matD_facts.2.1, canonM_matD, matD_facts.2.2⟩
  | f + 1, k => by
    obtain ⟨ih1, -, ih2⟩ := key_facts f (tb G 91 k)
    have e1 : keyW (f + 1) k = if k = 0 then matD else if tb G 92 k = 1 then
        conjW 253 matA matA (keyW f (tb G 91 k)) else conjW 253 matB matBi (keyW f (tb G 91 k)) :=
      rfl
    have e2 : gk (f + 1) k = if k = 0 then 1 else if tb G 92 k = 1 then wα * gk f (tb G 91 k)
        else wβ * gk f (tb G 91 k) := rfl
    by_cases h0 : k = 0
    · rw [if_pos h0] at e1 e2
      rw [e1, e2, one_mul, inv_one, mul_one, σ_wD]
      exact ⟨matD_facts.2.1, canonM_matD, matD_facts.2.2⟩
    rw [if_neg h0] at e1 e2
    by_cases hl : tb G 92 k = 1
    · rw [if_pos hl] at e1 e2
      rw [e1, e2]
      refine ⟨RowsWF.conjW rowsWF_matA rowsWF_matA ih1,
        canonM_conjW matA_size rowsWF_matA ih1 canonM_matA, ?_⟩
      rw [toMatW_conjW matA_size rowsWF_matA rowsWF_matA ih1, toMatW_matA, ih2, conjA_val]
    · rw [if_neg hl] at e1 e2
      rw [e1, e2]
      refine ⟨RowsWF.conjW rowsWF_matB rowsWF_matBi ih1,
        canonM_conjW matB_size rowsWF_matB ih1 canonM_matBi, ?_⟩
      rw [toMatW_conjW matB_size rowsWF_matB rowsWF_matBi ih1, toMatW_matB, toMatW_matBi, ih2,
        conjB_val]

theorem key_mat {k : ℕ} (hk : k < 31671) :
    toMatW 253 orbLit.keys[k]! = (σ (tk k * wD * (tk k)⁻¹)).val := by
  rw [keys_get hk]
  exact (key_facts 200 k).2.2

theorem key_canon {k : ℕ} (hk : k < 31671) : canonM 253 (toVM orbLit.keys[k]!) = true := by
  rw [keys_get hk]
  exact (key_facts 200 k).2.1

theorem key_wf {k : ℕ} (hk : k < 31671) : RowsWF (toVM orbLit.keys[k]!) := by
  rw [keys_get hk]
  exact (key_facts 200 k).1

theorem hA' : ∀ k < 31671,
    conjW 253 matA matA orbLit.keys[k]! = orbLit.keys[ap orbLit.alpha k]! := by
  intro k hk
  have hk' : tb G 39 k < 31671 := rng 39 (by norm_num) k hk
  have ea : ap orbLit.alpha k = tb G 39 k := ap_tabOf 39 hk
  rw [ea]
  refine eq_of_mat (canonM_conjW matA_size rowsWF_matA (key_wf hk) canonM_matA) (key_canon hk') ?_
  rw [toMatW_conjW matA_size rowsWF_matA rowsWF_matA (key_wf hk), toMatW_matA, key_mat hk,
    key_mat hk', conjA_val, conj_eq]
  rw [map_mul, Equiv.Perm.mul_apply, tk_pt hk, tk_pt hk']
  exact Fin.ext (phiX_wα k hk)

theorem hB' : ∀ k < 31671,
    conjW 253 matB matBi orbLit.keys[k]! = orbLit.keys[ap orbLit.beta k]! := by
  intro k hk
  have hk' : tb G 40 k < 31671 := rng 40 (by norm_num) k hk
  have eb : ap orbLit.beta k = tb G 40 k := ap_tabOf 40 hk
  rw [eb]
  refine eq_of_mat (canonM_conjW matB_size rowsWF_matB (key_wf hk) canonM_matBi) (key_canon hk') ?_
  rw [toMatW_conjW matB_size rowsWF_matB rowsWF_matBi (key_wf hk), toMatW_matB, toMatW_matBi,
    key_mat hk, key_mat hk', conjB_val, conj_eq]
  rw [map_mul, Equiv.Perm.mul_apply, tk_pt hk, tk_pt hk']
  exact Fin.ext (phiX_wβ k hk)

end

section

theorem not_key_D {m : ℕ} (hm : m = 1 ∨ m = 2) {v : PG}
    (hv0 : (phiX v ⟨0, hn⟩).val = m) (hv : σ (v * wD * v⁻¹) = σ wD) : False := by
  have hmN : m < 31671 := by omega
  have e := conj_eq (v := v) (g := tk m) (by rw [tk_pt hmN]; exact Fin.ext hv0)
  have hK : toMatW 253 orbLit.keys[m]! = mW ^ 7 := by
    rw [key_mat hmN, ← e, hv, σ_wD]
  have hD := matrixFacts.D_sq
  obtain ⟨-, n1, -, n2⟩ := prodFacts
  rcases hm with rfl | rfl
  · rw [keys_get (by norm_num), toMatW_key1] at hK
    apply n1
    rw [mat_P1, hK, hD]
  · rw [keys_get (by norm_num), toMatW_key2] at hK
    apply n2
    rw [mat_P2, hK, hD]

theorem hinj' : ∀ i < 31671, ∀ j < 31671, orbLit.keys[i]! = orbLit.keys[j]! → i = j := by
  intro i hi j hj e
  have mu : σ (tk i * wD * (tk i)⁻¹) = σ (tk j * wD * (tk j)⁻¹) := by
    apply Units.ext
    rw [← key_mat hi, ← key_mat hj, e]
  have hv : σ (((tk j)⁻¹ * tk i) * wD * ((tk j)⁻¹ * tk i)⁻¹) = σ wD := by
    have e1 : ((tk j)⁻¹ * tk i) * wD * ((tk j)⁻¹ * tk i)⁻¹ =
        (tk j)⁻¹ * (tk i * wD * (tk i)⁻¹) * tk j := by group
    have e2 : wD = (tk j)⁻¹ * (tk j * wD * (tk j)⁻¹) * tk j := by group
    rw [e1, map_mul, map_mul, mu, ← map_mul, ← map_mul, ← e2]
  set v := (tk j)⁻¹ * tk i with hvdef
  have hpt : phiX v ⟨0, hn⟩ = (phiX (tk j))⁻¹ ⟨i, hi⟩ := by
    rw [hvdef, map_mul, map_inv, Equiv.Perm.mul_apply, tk_pt hi]
  by_cases h0 : (phiX v ⟨0, hn⟩).val = 0
  · have h0' : phiX v ⟨0, hn⟩ = ⟨0, hn⟩ := Fin.ext h0
    rw [hpt, Equiv.Perm.inv_eq_iff_eq, tk_pt hj] at h0'
    exact congrArg Fin.val h0'
  · exfalso
    obtain ⟨s, hs, hs12⟩ := move_root (phiX v ⟨0, hn⟩).isLt h0
    obtain ⟨hs0, hsX⟩ := H1_fix hs
    rw [← range_phiX] at hsX
    obtain ⟨w, rfl⟩ := hsX
    have hc := stab_comm hs0
    have hw : σ ((w * v) * wD * (w * v)⁻¹) = σ wD := by
      have e1 : (w * v) * wD * (w * v)⁻¹ = w * (v * wD * v⁻¹) * w⁻¹ := by group
      have e2 : wD = w * wD * w⁻¹ := by rw [hc, mul_inv_cancel_right]
      rw [e1, map_mul, map_mul, hv, ← map_mul, ← map_mul, ← e2]
    have hpt' : phiX (w * v) ⟨0, hn⟩ = phiX w ⟨(phiX v ⟨0, hn⟩).val, (phiX v ⟨0, hn⟩).isLt⟩ := by
      rw [map_mul, Equiv.Perm.mul_apply]
    rcases hs12 with h1 | h2
    · exact not_key_D (Or.inl rfl) (by rw [hpt', h1]) hw
    · exact not_key_D (Or.inr rfl) (by rw [hpt', h2]) hw

end

end CertificateChecks.KernelFi23M

namespace CFSG.KD.Fi23K

open CertificateChecks.KernelFi23M

theorem orbitData_eq' :
    CFSG.Sporadic.Fi23.Native.orbitData () = orbLit :=
  orbitData_eq hA' hB' hinj'

end CFSG.KD.Fi23K

end
