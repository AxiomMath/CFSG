module

public import Certificates.Kernel.Sporadic.Fi24Sev.Data
public import Certificates.Kernel.Sporadic.Fi24Kit.Split

public section

namespace CFSG.KD.Fi24Sev.Ck

open CFSG.KC CFSG.KC.Loop CFSG.KC.LceS CFSG.KC.Fi24Net CFSG.KC.Fi24ThreeO CFSG.KD.Fi24Kit.Split

theorem letB_eq (v : Nat) (k : Nat → Bool) : letB v k = k v := by cases v <;> rfl

theorem covOK_of {NW : Nat → Nat → Nat} {NT : Nat → Nat} {ws : List (List Nat)}
    {d : Nat} {reps : List Nat} {d2 om c F T : Nat}
    (hF : itG (stepW NW NT ws) d2 (Nat.shiftLeft (nat_lit 1) om) = F)
    (hT : itG (stepW NW NT ws) d (plOf reps) = T)
    (h : andB (Nat.beq (Nat.land (Nat.lor T F) ptsM) ptsM)
      (Nat.beq (popcount F (nat_lit 524288)) c) = true) :
    CFSG.KC.Fi24Sev.covOK NW NT ws d reps d2 om c = true := by
  unfold CFSG.KC.Fi24Sev.covOK covW
  rw [iterW_itG, iterW_itG, hF, hT, letB_eq]
  exact h

end CFSG.KD.Fi24Sev.Ck

end
