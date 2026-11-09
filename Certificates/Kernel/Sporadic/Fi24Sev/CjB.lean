module

public import Certificates.Kernel.Sporadic.Fi24Sev.DataB
public import CFSG.Certificates.Kernel.Spor.Fi24SevBSound
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallChunks

public section

namespace CFSG.KD.Fi24SevB

open CFSG.KC CFSG.KC.Loop CFSG.KC.LceS CFSG.KC.Fi24Net CFSG.KC.Fi24Kit CFSG.KC.Fi24ThreeO
  CFSG.KC.Fi24Sev CFSG.KC.Fi24SevB CFSG.KD.Fi24Net CFSG.KD.Fi24Kit

@[expose] noncomputable def cjPt (c : Nat × Nat × List Nat × List Nat) (b : Nat) : Bool :=
  andB (allL (fun l => hasU sl (Nat.shiftRight l (nat_lit 1))) c.2.2.1)
    (andB (Nat.beq (ptC NW NT (mW sl c.2.2.1) b) (ptC NW NT c.2.2.2 b))
      (Nat.beq (ptC NW NT (c.2.2.2 ++ cubeW sl c.1) b)
        (ptC NW NT (lIf (Nat.beq c.2.1 (nat_lit 0)) (findU sl (nat_lit 66)) (findU sl (nat_lit 67))
          ++ c.2.2.2) b)))

@[expose] noncomputable def cjPc (k : Nat) : Bool :=
  cjPt (cj.getD (Nat.div k (nat_lit 6)) (0, 0, [], [])) (cb.getD (Nat.mod k (nat_lit 6)) 0)

end CFSG.KD.Fi24SevB

#kc_each CFSG.KD.Fi24SevB.cjPc 0 54

#kc_forall_chunks CFSG.KD.Fi24SevB.cjPc_all (fun k => CFSG.KD.Fi24SevB.cjPc k = true) 54
  CFSG.KD.Fi24SevB.cjPc 1

namespace CFSG.KD.Fi24SevB

open CFSG.KC CFSG.KC.Loop CFSG.KC.LceS CFSG.KC.Fi24Net CFSG.KC.Fi24Kit CFSG.KC.Fi24ThreeO
  CFSG.KC.Fi24Sev CFSG.KC.Fi24SevB CFSG.KD.Fi24Net CFSG.KD.Fi24Kit CFSG.KS.Fi24SevB
  CFSG.KS.Fi24Sev

theorem cj_length : cj.length = 9 := by decide +kernel

theorem cb_length : cb.length = 6 := rfl

theorem cj_ok : ∀ c ∈ cj, cjOK NW NT sl c = true := by
  intro c hc
  obtain ⟨i, hi, hci⟩ := List.getElem_of_mem hc
  have hpt : ∀ b ∈ cb, cjPt c b = true := by
    intro b hb
    obtain ⟨j, hj, hbj⟩ := List.getElem_of_mem hb
    have hi9 : i < 9 := by
      rw [cj_length] at hi
      exact hi
    have hj6 : j < 6 := by
      rw [cb_length] at hj
      exact hj
    have hlt : 6 * i + j < 54 := by omega
    have hk := cjPc_all (6 * i + j) hlt
    have e1 : Nat.div (6 * i + j) 6 = i := by
      change (6 * i + j) / 6 = i
      omega
    have e2 : Nat.mod (6 * i + j) 6 = j := by
      change (6 * i + j) % 6 = j
      omega
    unfold cjPc at hk
    rw [e1, e2, List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj, hci, hbj] at hk
    exact hk
  obtain ⟨b0, hb0⟩ : ∃ b, b ∈ cb := ⟨0, List.mem_cons_self⟩
  have hA := (andB_true' (hpt b0 hb0)).1
  have h2 : agB NW NT (mW sl c.2.2.1) c.2.2.2 = true := by
    unfold agB
    exact allL_of fun b hb => (andB_true' (andB_true' (hpt b hb)).2).1
  have h3 : agB NW NT (c.2.2.2 ++ cubeW sl c.1)
      (lIf (Nat.beq c.2.1 (nat_lit 0)) (findU sl (nat_lit 66)) (findU sl (nat_lit 67)) ++
        c.2.2.2) = true := by
    unfold agB
    exact allL_of fun b hb => (andB_true' (andB_true' (hpt b hb)).2).2
  unfold cjOK
  rw [hA, h2, h3]
  rfl

end CFSG.KD.Fi24SevB

end
